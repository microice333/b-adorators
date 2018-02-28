#include "blimit.hpp"

#include <iostream>
#include <string>
#include <thread>
#include <fstream>
#include <regex>
#include <map>
#include <vector>
#include <set>
#include <list>
#include <atomic>
#include <algorithm>

using namespace std;

vector<int> vertices;

class Lock {
    atomic_flag flag = ATOMIC_FLAG_INIT;
public:
    void lock() {
        while (flag.test_and_set(memory_order_acquire)) { ; }
    }

    void unlock() {
        flag.clear(memory_order_release);
    }
}; 

struct comp {
    bool operator() (pair<int, int> i, pair<int, int> j) const {
        if (i.second == -1) {
            return false;
        } 

        if (j.second == -1) {
            return true;
        }

        return i.first > j.first || (i.first == j.first && vertices[i.second] > vertices[j.second]);
    }
};
 
list<int> Q; 
vector<vector<pair<int, int>>> edges; 
deque<atomic<int>> db;
vector<int> b;
vector<int> bv;
vector<set<pair<int, int>, comp>> S;
Lock Qlock;
vector<unique_ptr<Lock>> locks;
vector<unique_ptr<Lock>> db_locks;
thread_local list<int> R;

void read_graph(const string& filename) {
    ifstream file(filename);
    string line;
    static regex ex("(\\d*) (\\d*) (\\d*)");
    smatch m;
    set<int> input_vertices; 
    map<int, vector<pair<int, int>>> input_edges;

    if (file.is_open()) {
        while (getline(file, line)) {
            if (!line.empty() && line[0] != '#' && regex_match(line, m, ex)) {
                int u = stoi(m[1].str());
                int v = stoi(m[2].str());
                int weight = stoi(m[3].str());

                input_edges[u].push_back({weight, v});
                input_edges[v].push_back({weight, u});
                input_vertices.insert(u);
                input_vertices.insert(v);
            }
        }

        map<int, int> old_to_new_map;
        int i = 0;

        for (auto v: input_vertices) {
            vertices.push_back(v);
            old_to_new_map[v] = i;
            i++;
        }

        for (auto j = 0; j < vertices.size(); j++) {
            edges.push_back(vector<pair<int, int>>());

            for (auto l = 0; l < input_edges[vertices[j]].size(); ++l) {
                int w = input_edges[vertices[j]][l].first;
                int n = old_to_new_map[input_edges[vertices[j]][l].second];
                
                edges[j].push_back({w, n});
            }
        }
    } else {
        cerr << "Error: problem with file " << filename << '\n';
    }
}

pair<int, int> s_last(int v) {
    if (S[v].size() == bv[v] && bv[v] > 0) {
        return *(--S[v].end());
    } else {
        return {0, -1};
    }
}

bool is_eligible(int u, pair<int, int> p) {
    if (S[p.second].find({p.first, u}) != S[p.second].end())
        return false;

    if (S[p.second].size() < bv[p.second])
        return true;

    if (bv[p.second] > 0) {
        struct comp compare;
        pair<int, int> last = s_last(p.second);

        pair<int, int> candidate_adoratore;
        candidate_adoratore.first = p.first;
        candidate_adoratore.second = u;

        return compare(candidate_adoratore, last);;
    }

    return false;
}

pair<int, int> find_eligible(int u) {
    for (auto v = 0; v < edges[u].size(); ++v) {
        locks[edges[u][v].second].get()->lock();
        
        if (is_eligible(u, edges[u][v])) {
            return edges[u][v];
        }

        locks[edges[u][v].second].get()->unlock();
    }

    return {0, -1};
}

void find_adorators_on_vector(vector<int>& vect) {
    for (auto u : vect) {
        int i = 0;
        while(i < b[u]) {
            pair<int, int> p = find_eligible(u);
            
            if (p.second == -1) {
                break;
            } else {
                i++;
                pair<int, int> last = s_last(p.second);
                S[p.second].insert({p.first, u});

                if (last.second != -1) {
                    S[p.second].erase(--S[p.second].end());
                    
                    int prev = db[last.second].fetch_add(1);
                    if (prev == 0)
                        R.push_back(last.second);
                }    

                locks[p.second].get()->unlock();
            }
        }
    }

    Qlock.lock();
    Q.insert(Q.begin(), R.begin(), R.end());
    Qlock.unlock();
}

int bsuitor_parallel(int thread_count) {
    for (auto v = 0; v < vertices.size(); ++v) {
        Q.push_back(v);
    }

    Q.unique();

    thread threads[thread_count];

    while (!Q.empty()) {
        int i = 0;
        vector<int> thread_vertices[thread_count];

        for (auto u : Q) {
            thread_vertices[i % thread_count].push_back(u);
            i++;
        }

        Q.clear();

        for (int j = 0; j < thread_count; j++) {
            threads[j] = thread(find_adorators_on_vector, ref(thread_vertices[j]));
        }

        for (int j = 0; j < thread_count; j++) {
            threads[j].join();
        }

        for (auto v = 0; v < vertices.size(); ++v) {
            b[v] = db[v];
            db[v] = 0;
        }
    }

    int sum = 0;

    for (auto v = 0; v < vertices.size(); ++v) {
        for (auto it = S[v].begin(); it != S[v].end(); ++it) {
            sum += it->first;
        }

        S[v].clear();
    }

    return sum / 2;
}

void reset_bvalues(int b_method) {
    for (auto v = 0; v < vertices.size(); ++v) {
        db[v] = 0;
        b[v] = bvalue(b_method, vertices[v]);
        bv[v] = bvalue(b_method, vertices[v]);
    }
}

int main(int argc, char* argv[]) {
    if (argc != 4) {
        cerr << "usage: "<<argv[0]<<" thread-count inputfile b-limit"<< endl;
        return 1;
    }

    int thread_count = stoi(argv[1]);
    int b_limit = stoi(argv[3]);
    string input_filename{argv[2]};
    
    read_graph(input_filename);
    
    for (auto v = 0; v < vertices.size(); ++v) {
        sort(edges[v].begin(), edges[v].end(), comp());
        locks[vertices[v]];
        S.push_back(set<pair<int, int>, comp>());
        db.emplace_back(0);
        b.push_back(0);
        bv.push_back(0);
        locks.push_back(make_unique<Lock>());
        db_locks.push_back(make_unique<Lock>());
    }

    for (int i = 0; i <= b_limit; i++) {
        reset_bvalues(i);
        cout << bsuitor_parallel(thread_count) << endl;
    }

    return 0;
}
