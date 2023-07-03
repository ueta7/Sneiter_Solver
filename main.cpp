// Copyright © 2023-2023 ueta All Rights Reserved.

/*
   This code is based on wata-orz'codes(https://github.com/wata-orz/steiner_tree).
   Copyright (c) 2018 Yoichi Iwata

   Original codes are written in RUST, so I rewrote in C++.
*/

#include <bits/stdc++.h>
#include <cstdint>
#define rep(i,n) for(int i=0;i<n;i++)

using namespace std;

struct edge{
	int u,v,c;
	edge(int u,int v,int c):u(u),v(v),c(c){}
	friend ostream& operator<<(ostream &o,const edge& e){
		return o<<"edge(" << e.u << "," << e.v << ", c = " << e.c << ")";
	}
};

namespace Sneiter_Solver
{
    using G=vector<vector<pair<int,int>>>;
    using G2=vector<map<int,int>>;
    using V=vector<int>;
    using P=pair<int,int>;
    constexpr int INF = INT_MAX;
    constexpr long long INFLL = LONG_LONG_MAX;
    constexpr long long INFLL_m = LONG_LONG_MIN;
    template<typename T>void chmin(T& a, T b) {a = min(a, b);}
    template<typename T>void chmax(T& a, T b) {a = max(a, b);}
    template<typename T>bool setmin(T& a, T b) {if(a>b){a = b; return true;}return false;}
    template<typename T>bool setmax(T& a, T b) {if(a<b){a = b; return true;}return false;}
    class UnionFind {
    private:
        vector<int> ps;
        vector<bool> is_root;
    public:
        UnionFind(int n) : ps(n, 1), is_root(n, true) {}
        int find(int x) {
            if (is_root[x]) {
                return x;
            } else {
                int p = find(ps[x]);
                ps[x] = p;
                return p;
            }
        }
        void unite(int x, int y) {
            int root_x = find(x), root_y = find(y);
            if (root_x == root_y) {
                return;
            }
            if (ps[root_x] < ps[root_y]) {
                swap(root_x, root_y);
            }
            ps[root_x] += ps[root_y];
            ps[root_y] = root_x;
            is_root[root_y] = false;
        }
        bool same(int x, int y) {
            return find(x) == find(y);
        }
        int size(int x) {
            return ps[find(x)];
        }
    };
    template <typename T>
    struct InitVec {
        int n,version;
        T ini;
        vector<pair<T, int>> data;
        InitVec(int n,const T& ini) : n(n), version(0), ini(ini), data(n, make_pair(ini, 0)) {}
        void init() {
            if (version ==INF) {
                for (auto& entry : data) {
                    entry.second = 0;
                }
                version = 1;
            } else {
                version++;
            }
        }
        int size() const {return data.size();}
        const T& operator[](int i) const {
            if (data[i].second == version) {
                return data[i].first;
            } else {
                return ini;
            }
        }
        T& operator[](int i) {
            if (data[i].second != version) {
                data[i]= make_pair(ini,version);
            }
            return data[i].first;
        }
    };
    enum class ModifyType {
        Contract // (u, v, w): v with N(v)={u,w} is contracted to u.
        ,Include // (u, v, Nv): uv is included and v is contracted to u. Nv is the set of neighbors w of v such that c(vw)<c(uw).
    };
    struct Modify {
        int u,v,w;
        V Nv;
        ModifyType type;
        Modify(int u, int v, int w, V Nv, ModifyType modify): u(u),v(v),w(w),Nv(Nv),type(modify){}
    };
    struct Reduction_RESULT{
        int orig_n, t0, w0, gsize;
        G g;
        V ts, ids;
        vector<Modify> modify;

        Reduction_RESULT(int orig_n,int t0,int w0,G g, V ts,V ids,vector<Modify> modify)
        : orig_n(orig_n),t0(t0),w0(w0),g(g),ts(ts),ids(ids),modify(modify) {
            gsize = 0;
            rep(i,g.size()){
                if(g[i].size()!=0)gsize++;
            }
        }
    };
    struct Data {
        int v;
        long long cost;
        P prev;
        Data(int v,long long cost,P prev): v(v),cost(cost),prev(prev) {}
    };
    vector<pair<size_t, size_t>> intersect(const vector<Data>& d1, const vector<Data>& d2) {
        vector<pair<size_t, size_t>> result;
        size_t p = 0;
        size_t q = 0;
        while (p < d1.size() && q < d2.size()) {
            if (d1[p].v == d2[q].v) {
                result.emplace_back(p, q);
                p++;
                q++;
            } else if (d1[p].v < d2[q].v) {
                p++;
            } else {
                q++;
            }
        }
        return result;
    }
    class my_bitset {
    private:
        vector<u_int64_t> data;
    public:
        my_bitset(size_t n) :data((n + 63) / 64,0) {}
        my_bitset(const my_bitset &bit) :data(bit.data){}
        void set(size_t i, bool b) {
            assert(i/64<data.size());
            if (b) {data[i / 64] |= 1ULL << (i & 63);}
            else {data[i / 64] &= ~(1ULL << (i & 63));}
        }
        bool intersect(const my_bitset& other) const {
            for (size_t i = 0; i < data.size(); i++) {
                if ((data[i] & other.data[i]) != 0) {return true;}
            }
            return false;
        }
        size_t count() const {
            size_t c = 0;
            for (const auto& a : data) {c += __builtin_popcountll(a);}return c;
        }
        size_t size() const {return data.size();}
        bool operator[](size_t i) const {return ((data[i / 64] >> (i & 63)) & 1) == 1;}
        my_bitset operator&(const my_bitset& other) const {
            my_bitset result(min(size(),other.size())*64);
            for (size_t i = 0; i < min(size(),other.size()); i++) {result.data[i] = data[i] & other.data[i];}
            return result;
        }
        my_bitset operator|(const my_bitset& other) const {
            my_bitset result(min(size(),other.size())*64);
            for (size_t i = 0; i < min(size(),other.size()); i++) {result.data[i] = data[i] | other.data[i];}
            return result;
        }
        my_bitset operator^(const my_bitset& other) const {
            my_bitset result(min(size(),other.size())*64);
            for (size_t i = 0; i < min(size(),other.size()); i++) {result.data[i] = data[i] ^ other.data[i];}
            return result;
        }
        my_bitset operator&=(const my_bitset& other){return *this&other;}
        my_bitset operator|=(const my_bitset& other){return *this|other;}
        my_bitset operator^=(const my_bitset& other){return *this^other;}
        bool operator==(const my_bitset& other)const{return (data==other.data)?true : false;}
        bool operator<(const my_bitset& other)const{return data<other.data;}
        bool operator>(const my_bitset& other)const{return data>other.data;}
    };
    struct SubTree {
        my_bitset i_and, v_or;
        int p,i_pos;
        array<int, 2> cs;
        SubTree(my_bitset i_and, my_bitset v_or,int p,int i_pos,array<int, 2> cs): i_and(i_and),v_or(v_or),p(p),i_pos(i_pos),cs(cs){}
    };
    struct BitTree {
        vector<SubTree> ts;
        int root;
        BitTree() : ts({}), root(-1) {}
        void insert(const my_bitset i, const my_bitset& v, int p) {
            if (root == -1) {
                _new_leaf(i, v, p);
                root = 0;
            } else {
                int current_root = root;
                root = _insert(i, v, p, current_root, 0);
            }
        }
        V find(const my_bitset i, const my_bitset& v) const {
            if (root ==-1) {return {};}
            V ps;
            _find(i, v, root,ps);
            return ps;
        }
    private:
        int _new_leaf(const my_bitset& i, const my_bitset& v, int p) {
            int i_pos = i.size() * 64;
            SubTree tmp(i, v, p, i_pos, array<int, 2>{-1, -1});
            ts.push_back(tmp);
            return ts.size() - 1;
        }
        int _insert(const my_bitset i, const my_bitset v, int p, int x, int i_pos) {
            if (ts[x].i_pos == i_pos) {
                int j = i[i_pos] ? 1 : 0;
                int c = ts[x].cs[j];
                ts[x].i_and = ts[x].i_and & i;
                ts[x].v_or = ts[x].v_or| v;
                ts[x].cs[j] = _insert(i, v, p, c, i_pos + 1);
                return x;
            } else if (ts[x].i_and[i_pos] != i[i_pos]) {
                int leaf = _new_leaf(i, v, p);
                int c1 = i[i_pos] ? x : leaf;
                int c2 = i[i_pos] ? leaf : x;
                my_bitset iand = i & ts[x].i_and;
                my_bitset vor = v | ts[x].v_or;
                SubTree tmp(iand, vor, -1, i_pos, array<int, 2>{c1,c2});
                ts.push_back(tmp);
                return ts.size() - 1;
            } else {
                return _insert(i, v, p, x, i_pos + 1);
            }
        }
        void _find(const my_bitset& i, const my_bitset& v, int x,V &ps) const {
            if (ts[x].i_and.intersect(i) || !ts[x].v_or.intersect(v)) {
                ;
            } else if (ts[x].i_pos == i.size()*64) {
                ps.emplace_back(ts[x].p);
            } else {
                _find(i, v, ts[x].cs[0],ps);
                if (!i[ts[x].i_pos]) {
                    _find(i, v, ts[x].cs[1],ps);
                }
            }
            return;
        }
    };

    tuple<int, int, int> size(const G2& g2, const vector<bool>& is_t) {
        int n = 0,m = 0,t = 0;
        for (int i = 0; i < (int)g2.size(); i++) {
            if (!g2[i].empty()) {
                n++;
                m += g2[i].size();
                if (is_t[i]) {
                    t++;
                }
            }
        }
        return make_tuple(n, m / 2, t);
    }

    pair<V, V> get_ts(const G2 &g2, const vector<bool> &is_t) {
        int n = g2.size();
        V ts{}, id(n,-1);
        for (int u = 0; u < n; ++u) {
            if (is_t[u] && !g2[u].empty()) {
                id[u] = ts.size();
                ts.push_back(u);
            }
        }
        return make_pair(ts, id);
    }
// Include all the edges of weight zero.
// weight0のものがあればそこを他のもので繋ぎなおす
    bool weight0(G2& g2, vector<bool>& is_t, vector<Modify>& modify) {
        const int n = g2.size();
        bool modified = false;
        for (int u = 0; u < n; u++) {
            auto  it = find_if(g2[u].begin(), g2[u].end(), [](const auto& entry) {return entry.second == 0;});
            if (it != g2[u].end()) {
                int v = it->first;
                is_t[v] = is_t[v] || is_t[u];
                is_t[u] = false;
                V xs;
                map<int,int> fs = g2[u];
                for (auto[x,w] : fs) {
                    g2[x].erase(u);
                    if(x != v){
                        if (g2[v].find(x)==g2[v].end()) {
                            g2[v][x] = w;
                            xs.push_back(x);
                        }else if(setmin(g2[v][x],w)){
                            xs.push_back(x);
                        }
                    }
                }
                modify.push_back(Modify(v, u, -1, xs, ModifyType::Include));
                modified = true;
            }
        }
        return modified;
    }
// Lightweight reduction which runs in linear time.
    bool light(G2& g2, vector<bool>& is_t, vector<Modify>& modify, int& w0) {
        int n = g2.size();
        bool modified = false;
        int t_count = count(is_t.begin(), is_t.end(), true);
        for (int u = 0; u < n; u++) {
            if (t_count <= 1) {
                break;
            }
            if (g2[u].empty()) {
                ;
            } else if (g2[u].size() == 1) {
                // terminalは確定・non-terminalなら消す
                map<int,int> fs = g2[u];
                for (const auto& [v, w] : fs) {
                    if (is_t[u]) {
                        if (is_t[v]) {
                            t_count--;
                        }
                        is_t[u] = false;
                        is_t[v] = true;
                        modify.push_back(Modify(v, u, -1, {}, ModifyType::Include));
                        w0 += w;
                    }
                    g2[v].erase(u);
                    g2[u].erase(v);
                    modified = true;
                }
            } else if (g2[u].size() == 2 && !is_t[u]) {
                // non-terminal u が次数 2 のとき、繋ぎ直しできる
                auto it = g2[u].begin();
                auto [v1, w1] = *it;it++;
                auto [v2, w2] = *it;
                g2[v1].erase(u);
                g2[v2].erase(u);
                g2[u].clear();
                modified = true;
                if (g2[v1].find(v2)==g2[v1].end()) {
                    g2[v1][v2] = w1 + w2;
                    g2[v2][v1] = w1 + w2;
                    modify.push_back(Modify(v1, u, v2, {}, ModifyType::Contract)); 
                }else if (setmin(g2[v1][v2],w1 + w2)) {
                    g2[v2][v1] = w1 + w2;
                    modify.push_back(Modify(v1, u, v2, {}, ModifyType::Contract)); 
                }
               
                // assert(0);
            } else if (is_t[u]) {
                // 2つのターミナルuとvを結ぶ辺が、uに入射するすべての辺の中で最も小さい重みを持つとき、それを含める
                int min_w = min_element(g2[u].begin(), g2[u].end(), [](const auto &x, const auto &y) {return x.second < y.second;})->second;
                int v = -1;
                for (const auto& p : g2[u]) {
                    int a = p.first;
                    int w = p.second;
                    if (w == min_w && is_t[a]) {
                        v = a;
                        break;
                    }
                }

                if (v != -1) {
                    t_count--;
                    is_t[u] = false;
                    w0 += min_w;
                    V xs;
                    map<int,int> fs=g2[u];
                    for (const auto [x, w] : fs) {
                        g2[x].erase(u);
                        g2[u].erase(x);
                        if (x != v){
                            if(g2[v].find(x)==g2[v].end()) {
                                g2[v][x] = w;
                                g2[x][v] = w;
                                xs.push_back(x);
                            }else if(setmin(g2[v][x],w)){
                                g2[x][v] = w;
                                xs.push_back(x);
                            }
                        }
                    }
                    modify.push_back(Modify(v, u, -1, xs, ModifyType::Include));
                    modified = true;
                }
            }
        }
        return modified;
    }
	// s(u,v) := bottleneck distance from u to v in the distance graph on A+u+v.
	// When s(u,v)<c(uv), we can delete uv.
    bool sd(G2 &g2, const vector<bool> &is_t) {
        vector<pair<int, int>> del;
        int n = g2.size();
        {
            auto [ts, _] = get_ts(g2, is_t);
            V tid(n,-1);
            for (int t = 0; t < (int)ts.size(); ++t) {
                tid[ts[t]] = t;
            }
            // Perturbation for tie-breaking.
            vector<vector<pair<int, long long>>> g_perturbed(n);
            long long max_w = 0;
            for (int u = 0; u < n; ++u) {
                for (const auto &[v, w] : g2[u]) {
                    long long weight = ((long long)w << 32) - (is_t[u] ? 2LL : 1LL) - (is_t[v] ? 2LL : 1LL);
                    g_perturbed[u].emplace_back(v, weight);
                    chmax(max_w, weight);
                }
            }
            vector<vector<long long>> dist_t(ts.size(), vector<long long>(n, INFLL));
            vector<vector<pair<long long, int>>> gt(ts.size());
            priority_queue<pair<long long, int>> que;
            V debugger{};
            {
                for (int i = 0; i < (int)ts.size(); ++i) {
                    dist_t[i][ts[i]] = 0;
                    que.emplace(0LL, ts[i]);
                    while (!que.empty()) {
                        auto [d, u] = que.top();
                        que.pop();

                        debugger.push_back(que.size());
                        d *= -1;
                        if (dist_t[i][u] != d) {
                            continue;
                        }
                        for (const auto &[v, w] : g_perturbed[u]) {
                            long long d2 = d + w;
                            if (d2 < max_w && setmin(dist_t[i][v],d2)) {
                                que.emplace(-d2, v);
                            }
                        }
                    }
                    for (int &t: ts) {
                        if (t == ts[i]) {
                            continue;
                        }
                        if (dist_t[i][t] < max_w) {
                            gt[i].emplace_back(dist_t[i][t], t);
                        }
                        sort(gt[i].begin(), gt[i].end());
                    }
                }
            }
            InitVec<long long> dist(n, INFLL);
            for (int s = 0; s < n; ++s) {
                if (g_perturbed[s].empty()) {
                    continue;
                }
                long long d_max = INFLL_m;
                V adj;
                for (const auto &[v, w] : g_perturbed[s]) {
                    if (s < v) {
                        chmax(d_max, w);
                        adj.push_back(v);
                    }
                }
                if (adj.empty()) {
                    continue;
                }
                dist.init();
                dist[s] = 0LL;
                que.emplace(0LL, s);
                while (!que.empty()) {
                    auto [d, u] = que.top();
                    que.pop();
                    d *= -1;
                    if (d != dist[u]) {
                        continue;
                    }
                    if (tid[u] != -1) {
                        for (const int &v : adj) {
                            chmin(dist[v],max(d,dist_t[tid[u]][v]));
                        }
                        for (const auto &[w, t] : gt[tid[u]]) {
                            if (w >= d_max) {
                                break;
                            }
                            long long d2 = max(d,w);
                            if (setmin(dist[t],d2)) {
                                que.emplace(-d2, t);
                            }
                        }
                    } else {
                        for (const auto &[v, w] : g_perturbed[u]) {
                            long long d2 = d + w;
                            if (d2 < d_max && setmin(dist[v],d2)) {
                                que.emplace(-d2, v);
                            }
                        }
                    }
                }

                for (const auto &[v, w] : g_perturbed[s]) {
                    if (s < v && w > dist[v]) {
                        del.emplace_back(s, v);
                    }
                }
            }
        }
        for (const auto &[u, v] : del) {
            g2[u].erase(v);
            g2[v].erase(u);
        }

        return !del.empty();
    }

    bool nsc(G2& g2, vector<bool>& is_t, vector<Modify>& modify, int& w0) {
        int n = g2.size();
        vector<tuple<int, int, int, int>> fs;
        for (int u = 0; u < n; ++u) {
            for (const auto& [v, w] : g2[u]) {
                if (u < v) {
                    fs.emplace_back(w, (is_t[u] ? 0 : 1) + (is_t[v] ? 0 : 1), u, v);
                }
            }
        }
        sort(fs.begin(), fs.end());
        UnionFind uf(n);
        vector<vector<pair<int, int>>> mst(n);
        for (const auto& [w, _, u, v] : fs) {
            if (!uf.same(u, v)) {
                uf.unite(u, v);
                mst[u].emplace_back(v, w);
                mst[v].emplace_back(u, w);
            }
        }
        V parent(n, -1);
        V depth(n, -1);
        int r = -1;
        for (int u = 0; u < n; ++u) {
            if (!mst[u].empty()) {
                r = u;
                break;
            }
        }
        if (r == -1) {return false;}
        V root_to_leaf;
        root_to_leaf.push_back(r);
        depth[r] = 0;
        for (int p = 0; p < (int)root_to_leaf.size(); ++p) {
            int u = root_to_leaf[p];
            for (const auto& [v, w] : mst[u]) {
                if (depth[v] == -1) {
                    depth[v] = depth[u] + w;
                    parent[v] = u;
                    root_to_leaf.push_back(v);
                }
            }
        }
        auto [ts, id] = get_ts(g2, is_t);
        vector<V> dist_t(ts.size(), V(n, INF));
        for (int i = 0; i < (int)ts.size(); ++i) {
            priority_queue<pair<int, int>> que;
            dist_t[i][ts[i]] = 0;
            que.push(make_pair(0, ts[i]));

            while (!que.empty()) {
                auto [d, u] = que.top();
                que.pop();
                d *= -1;
                if (dist_t[i][u] != d) {
                    continue;
                }
                for (const auto& [v, w] : g2[u]) {
                    int d2 = d + w;
                    if (setmin(dist_t[i][v],d2)) {
                        que.push(make_pair(-d2, v));
                    }
                }
            }
        }
        vector<V> ts_below(n);
        for (auto it = root_to_leaf.rbegin(); it != root_to_leaf.rend(); ++it) {
            int u = *it;
            if (is_t[u]) {
                ts_below[u].push_back(id[u]);
            }
            int v = parent[u];
            if (v != -1) {
                ts_below[v].insert(ts_below[v].end(), ts_below[u].begin(), ts_below[u].end());
            }
        }
        V min_below(n, INF);
        V min_above(n, INF);
        InitVec<bool> is_below(ts.size(), false);
        for (int &u : root_to_leaf) {
            is_below.init();
            for (int &b : ts_below[u]) {
                is_below[b] = true;
            }
            for (int i = 0; i < (int)ts.size(); ++i) {
                if (is_below[i]) {
                    chmin(min_below[u], dist_t[i][u]);
                } else {
                    chmin(min_above[u], dist_t[i][parent[u]]);
                }
            }
        }
        vector<bool> ok(n);
        for (int u = 0; u < n; ++u) {
            ok[u] = (parent[u] != -1 && min_below[u] < INF && min_above[u] < INF);
        }        
        for (int u = 0; u < n; ++u) {
            for (const auto& [v, w] : g2[u]) {
                if (v == parent[u] || u == parent[v] || u < v) {
                    continue;
                }
                int x = u, y = v;
				while(x != y) {
					if (depth[x] < depth[y]) {
						y = parent[y];
					} else {
						x = parent[x];
					}
				}
                int lca = x;
                x = u,y = v;
                while (x != y) {
                    if (depth[x] < depth[y]) {
                        if (ok[y]) {
                            int c = depth[y] - depth[parent[y]];
                            int d_above = depth[u] - depth[lca] + depth[parent[y]] - depth[lca];
                            int d_below = depth[v] - depth[y];

                            if (min(d_above, min_above[y]) + min(d_below, min_below[y]) + c > w) {
                                ok[y] = false;
                            }
                        }
                        y = parent[y];
                    } else {
                        if (ok[x]) {
                            int c = depth[x] - depth[parent[x]];
                            int d_above = depth[v] - depth[lca] + depth[parent[x]] - depth[lca];
                            int d_below = depth[u] - depth[x];
                            if (min(d_above,min_above[x]) + min(d_below, min_below[x]) + c > w) {
                                ok[x] = false;
                            }
                        }
                        x = parent[x];
                    }
                }
            }
        }
        bool modified = false;
        for (auto it = root_to_leaf.rbegin(); it != root_to_leaf.rend(); ++it) {
            int u = *it;
            if (ok[u]) {
                modified = true;
                int v = parent[u];
                int w = depth[u] - depth[v];
                is_t[v] = is_t[v] || is_t[u];
                is_t[u] = false;
                V xs;
                map<int,int> fs = g2[u];
                for (auto [x, w] : fs) {
                    g2[x].erase(u);
                    g2[u].erase(x);
                    if (x != v){
                        if(g2[v].find(x)==g2[v].end()){
                            g2[v][x] = w;
                            g2[x][v] = w;
                            xs.push_back(x);
                        } else if (setmin(g2[v][x],w)) {
                            g2[x][v] = w;
                            xs.push_back(x);
                        }
                    }
                }
                modify.push_back(Modify(v, u, -1, xs, ModifyType::Include));
                w0 += w;
            }
        }
        return modified;
    }

    bool deg3(G2& g2, const vector<bool>& is_t) {
        int n = g2.size();
        bool modified = false;
        InitVec<int> dist(n,INF);
        // Compute d(s,t) on G-deleted, or return ub if the distance is at least ub.
        function<int(const G2&, const InitVec<bool>&, const V&, int, int)> 
        calc_dist = [&](const G2& g2, const InitVec<bool>& deleted, const V& s, int t, int ub) {
            dist.init();
            priority_queue<P> que;
            for (int u : s) {
                dist[u] = 0;
                que.push(make_pair(0, u));
            }
            while (!que.empty()) {
                auto [d, u] = que.top();
                que.pop();
                d *= -1;
                if (u == t) {
                    return d;
                }
                if (dist[u] != d) {
                    continue;
                }
                for (const auto& [v, w] : g2[u]) {
                    int d2 = d + w;
                    if (d2 < ub && !deleted[v] && setmin(dist[v],d2)) {
                        que.push(make_pair(-d2, v));
                    }
                }
            }
            return ub;
        };

        InitVec<bool> deleted(n, false);
        for (int u = 0; u < n; ++u) {
            if (g2[u].size() == 3 && !is_t[u]) {
                vector<pair<int, int>> gu(g2[u].begin(), g2[u].end());
                for (int i = 0; i < 3; ++i) {
                    int p, up, x, ux, y, uy;
                    tie(p, up) = gu[i];
                    tie(x,ux) = gu[(i + 1) % 3];
                    tie(y,uy) = gu[(i + 2) % 3];
                    deleted.init();
                    deleted[u] = true;
                    int xp = calc_dist(g2, deleted, {x}, p, ux + up + 1);
                    if (xp > ux + up) {
                        continue;
                    }
                    int yp = calc_dist(g2, deleted, {y}, p, uy + up + 1);
                    if (yp > uy + up) {
                        continue;
                    }
					// u has three neighbors {p, x, y} and there are shortest paths from p to x and p to y both avoiding u.
					// Let OPT be the set of edges contained in every optimal solution.
					// Suppose that up is in OPT. Then ux and uy are also in OPT.
                    int xy = calc_dist(g2, deleted, {x}, y, ux + uy);
                    if (xp + yp + xy - max({xp, yp, xy}) <= ux + uy + up) {
                        // Instead of using {up, ux, uy}, we can use MST of {p, x, y}.
                        modified = true;
                        g2[u].erase(p);
                        g2[p].erase(u);
                        break;
                    } else {
                        bool del = false;
                        while (true) {
                            if (calc_dist(g2, deleted, {x, y}, p, up + 1) <= up) {
                                // If there exists a path from {x,y} to p of length at most up, we can replace up by the path.
                                del = true;
                                break;
                            }
                            if (is_t[p]) {
                                break;
                            }
							// If p is not a terminal, p must have degree at least two in OPT.
                            deleted[p] = true;
                            vector<pair<int, int>> ps;
                            for (const auto& [q, pq] : g2[p]) {
                                if (ps.size() < 2 && !deleted[q] && calc_dist(g2, deleted, {x, y}, q, max(up, pq) + 1) > max(up, pq)) {
                                    ps.emplace_back(q, pq);
                                }
                            }
                            if (ps.size() > 1) {
                                break;
                            } else if (ps.size() == 1) {
								// If there is only one candidate q, p has degree two in OPT.
								// We repeat the process by setting p<-q.
                                p = ps[0].first;
                                up += ps[0].second;
                            } else {
                                del = true;
                                break;
                            }
                        }
                        if (del) {
                            modified = true;
                            int np = gu[i].first;
                            g2[u].erase(np);
                            g2[np].erase(u);
                            break;
                        }
                    }
                }
            }
        }
        return modified;
    }
    Reduction_RESULT reduce(vector<vector<P>>& g,V &ts){
        int n = g.size();
        int t0 = ts[0];
        G2 g2(n);
        vector<bool> is_t(n,false);
        for(int &i: ts){
            is_t[i] = true;
        }
        rep(u,n){
            for(P j: g[u]){
                if(g2[u].find(j.first)==g2[u].end()){
                    g2[u][j.first] = j.second;
                }else{
                    chmin(g2[u][j.first],j.second);
                }
            }
        }
        vector<Modify> modify{};
        int w0 = 0;
        {
            auto[n,m,t] = Sneiter_Solver::size(g2, is_t);
			if(Sneiter_Solver::weight0(g2,is_t,modify)){
				auto [n2, m2, t2] = size(g2, is_t);
            }
        }
        while (1) {
            auto [n, m, t] = Sneiter_Solver::size(g2, is_t);
            if (t <= 1) {
                break;
            }
            if (Sneiter_Solver::light(g2, is_t, modify, w0)) {
                auto [n2, m2, t2] = Sneiter_Solver::size(g2, is_t);
                continue;
            }
            if (Sneiter_Solver::sd(g2, is_t)) {
                auto [n2, m2, t2] = Sneiter_Solver::size(g2, is_t);
                continue;
            }
            if (Sneiter_Solver::nsc(g2, is_t, modify, w0)) {
                auto [n2, m2, t2] = Sneiter_Solver::size(g2, is_t);
                continue;
            }
            if (Sneiter_Solver::deg3(g2, is_t)) {
                auto [n2, m2, t2] = Sneiter_Solver::size(g2, is_t);
                continue;
            }
            break;
        }
        V ids;
        V name(n, -1);
        for (int u = 0; u < n; ++u) {
            if (g2[u].size() > 0) {
                name[u] = ids.size();
                ids.push_back(u);
            }
        }
        V ts_return;
        for (int t = 0; t < n; ++t) {
            if (is_t[t] && name[t] != -1) {
                ts_return.push_back(name[t]);
            }
        }
        G g_return(ids.size());
        for (int u = 0; u < ids.size(); ++u) {
            for (const auto& [v, w] : g2[ids[u]]) {
                g_return[u].emplace_back(name[v], w);
            }
        }
        for (int u = 0; u < n; ++u) {
            for (const auto& [v, w] : g2[u]) {
                assert(g2[v].at(u) == w);
            }
        }
        Reduction_RESULT ret(n, t0, w0, g_return, ts_return, ids, modify);
        return ret;
    }
    pair<int,vector<P>> restore(Reduction_RESULT&reduced,pair<int,vector<P>>&result) {
        int orig_n = reduced.orig_n;
        vector<Modify> modify = reduced.modify;
        vector<P> es = result.second;
        vector<set<int>> g(orig_n);
        for (const auto& edge : es) {
            int u = reduced.ids[edge.first];
            int v = reduced.ids[edge.second];
            g[u].insert(v);
            g[v].insert(u);
        }
        for (auto modit = modify.rbegin(); modit != modify.rend(); ++modit) {
            const auto& modop = *modit;
            int u = modop.u,v = modop.v, w = modop.w;
            switch (modop.type)
            {
            case ModifyType::Contract:
                if (g[u].count(w)) {
                    g[u].erase(w);
                    g[w].erase(u);
                    g[u].insert(v);
                    g[v].insert(u);
                    g[v].insert(w);
                    g[w].insert(v);
                }
                break;
            case ModifyType::Include:
                for(int w: modop.Nv) {
                    if (g[u].count(w)) {
                        g[u].erase(w);
                        g[w].erase(u);
                        g[v].insert(w);
                        g[w].insert(v);
					}
                }
                g[u].insert(v);
                g[v].insert(u);
                break;
            }
        }
        vector<bool> visited(orig_n, false);
        V stack;
        visited[reduced.t0] = true;
        stack.push_back(reduced.t0);
        while (!stack.empty()) {
            int u = stack.back();
            stack.pop_back();
            for (int v : g[u]) {
                if (!visited[v]) {
                    visited[v] = true;
                    stack.push_back(v);
                }
            }
        }
        vector<pair<int, int>> restored_es;
        for (int u = 0; u < orig_n; ++u) {
            for (int v : g[u]) {
                if (visited[u] && visited[v] && u < v) {
                    restored_es.emplace_back(u, v);
                }
            }
        }
        return {result.first + reduced.w0, restored_es};
    };
    bool validate(const G& g, const V& ts, int w, const vector<P>& es) {
        size_t n = g.size();
        long long w2 = 0;
        vector<unordered_map<int, int>> g2(n);
        for (int u = 0; u < n; ++u) {
            for (const auto& [v, w] : g[u]) {
                if(g2[u].find(v)==g2[u].end()){
                    g2[u][v] = w;
                }else{
                   chmin(g2[u][v], w); 
                }
            }
        }
        vector<V> st(n);
        for (const auto& [u, v] : es) {
            st[u].push_back(v);
            st[v].push_back(u);
            auto it = g2[u].find(v);
            if (it != g2[u].end()) {
                w2 += it->second;
            } else {
                cerr << "illegal edge" << endl;
                return false;
            }
        }
        if (w2 != static_cast<int64_t>(w)) {
            cerr << "wrong value: " << w << " vs " << w2 << endl;
            return false;
        }
        vector<bool> visited(n, false);
        stack<int> stack;
        visited[ts[0]] = true;
        stack.push(ts[0]);
        while (!stack.empty()) {
            int u = stack.top();
            stack.pop();
            for (int v : st[u]) {
                if (!visited[v]) {
                    visited[v] = true;
                    stack.push(v);
                }
            }
        }
        for (int t : ts) {
            if (!visited[t]) {
                cerr << "not connected" << endl;
                return false;
            }
        }
        return true;
    }
    pair<int,vector<P>> solver(const G& g, const V& ts) {
        if (ts.size() <= 1) {return {0,{}};}
        int n = g.size();
        long long div = (1LL << 32) / n;
        vector<vector<pair<int,long long>>> perturbed_g(n);
        for (int u = 0; u < n; u++) {
            for (const auto& [v,w] : g[u]) {
                long long perturbed_weight = ((long long)w << 32) | ((u + v) % div);
                perturbed_g[u].push_back(make_pair(v, perturbed_weight));
            }
        }
        unsigned int T = ts.size();
        V tid(n, -1);
        for (int t = 0; t < T; t++) {
            tid[ts[t]] = t;
        }
        my_bitset all(T);
        for (int i = 0; i < T; i++) {
            all.set(i, true);
        }
        set<pair<int, my_bitset>> i_set;
        map<my_bitset, vector<Data>> ongoing;
        for (long long i = 0; i < T; i++) {
            my_bitset bit(T);
            bit.set(i, 1);
            i_set.insert({1,bit});
            ongoing[bit] = {Data(ts[i], 0, { -1, -1 })};
        }

        long long min_ret = INFLL;
        long long min_x = -1;
        P min_prev = { -1, -1 };

        BitTree bit_tree;
        vector<my_bitset> bits;
        V bit_counts;
        vector<long long> offsets = { 0 };
        vector<Data> data;
        // data.reserve(1000000);
        int total_size = 0;
        int process = 0;
        while (!i_set.empty()) {
            auto [i_count, i_bit] = *i_set.begin();
            i_set.erase(i_set.begin());
            vector<Data> crt = ongoing[i_bit];
            ongoing.erase(i_bit);
            i_count = i_bit.count();
            if (process<i_count) {
                process = i_count;
            }

            vector<long long> dist(n, INFLL);
            vector<long long> ub(n, INFLL);
            vector<pair<int, int>> prev(n, P(-1, -1));
            vector<bool> valid(n, false);
            {
                vector<pair<long long, int>> cs(crt.size());
                for (int i = 0; i < (int)crt.size(); ++i) {
                    cs[i] = make_pair(crt[i].cost, i);
                }
                sort(cs.begin(), cs.end());
                V count(n, 0);
                vector<tuple<int,long long,long long>> stack;
                int valid_count = 0;
                
                for (auto& [_,i] : cs) {
                    Data& c = crt[i];
                    long long d = c.cost;
                    if (dist[c.v] < d) {
                        continue;
                    }
                    dist[c.v] = d;
                    valid[c.v] = true;
                    prev[c.v] = c.prev;
                    valid_count++;
                    count[c.v]++;
                    ub[c.v] = 0LL;
                    if (c.prev.first != -1) {
                        int x,y;tie(x,y) = c.prev;
                        stack.push_back(make_tuple(x, 0, 0));
                        stack.push_back(make_tuple(y, 0, 0));
                        while (!stack.empty()) {
                            int x; long long c,w;
                            tie(x, c, w) = stack.back();
                            stack.pop_back();
                            long long cost = data[x].cost;
                            tie(x,y) = data[x].prev;
                            if (x != -1) {
                                if (y != -1) {
                                    stack.push_back(make_tuple(x, 0, w));
                                    stack.push_back(make_tuple(y, 0, w));
                                } else {
                                    int v2 = data[x].v;
                                    long long c2 = c + cost - data[x].cost;
                                    long long w2 = max(w, c2);
                                    chmin(dist[v2], d);
                                    count[v2]++;
                                    chmin(ub[v2], w2);
                                    stack.push_back(make_tuple(x, c2, w2));
                                }
                            }
                        }
                    }
                }
                for (int u = 0; u < n; ++u) {
                    if (count[u] < valid_count) {
                        ub[u] = 0;
                    }
                }
            }
            int s = -1;
            {
                V adj_count(T, 0);
                priority_queue<pair<long long, int>> que;
                for (int u = 0; u < n; ++u) {
                    if (dist[u] < INFLL) {
                        que.push(make_pair(-dist[u], u));
                    }
                }
                while (!que.empty()) {
                    auto [d,u] = que.top();
                    que.pop();
                    d *= -1;
                    if (d != dist[u]) {
                        continue;
                    }
                    if (tid[u] != -1 && !i_bit[tid[u]]) {
                        s = u;
                        break;
                    }
                    bool ok = valid[u];
                    for (auto& [v,w] : perturbed_g[u]) {
                        long long d2 = d + w;
                        if (setmin(dist[v],d2)) {
                            que.push(make_pair(-d2, v));
                            valid[v] = ok;
                            prev[v] = make_pair(u, -1);
                        } else if (dist[v] == d2 && !ok) {
                            valid[v] = false;
                        }
                        if (tid[v] != -1 && !i_bit[tid[v]] && T - i_count > 1) {
                            adj_count[tid[v]]++;
                            if (adj_count[tid[v]] == perturbed_g[v].size()) {
                                s = v;
                                goto dij;
                            }
                        }
                    }
                }
                dij:;
            }
            if (T - i_count > 1) {
                priority_queue<pair<long long, int>> que;
                for (int u = 0; u < n; ++u) {
                    if (ub[u] > 0) {
                        que.push(make_pair(ub[u], u));
                    }
                }
                while (!que.empty()) {
                    auto [d,u] = que.top();
                    que.pop();
                    if (d != ub[u]) {
                        continue;
                    }
                    for (const auto& [v,w] : perturbed_g[u]) {
                        long long d2 = d - w;
                        if (ub[v] < d2) {
                            ub[v] = d2;
                            que.push(make_pair(d2, v));
                        }
                    }
                }
                long long atmost = -1;
                bool flag = 1;
                for(int t=0;t<T;t++){if(!i_bit[t] && ub[ts[t]]>0){flag = 0;break;}}
                if (flag) {
                    int count_t = 0;
                    vector<long long> min_d(n, -1);
                    min_d[s] = dist[s];
                    que.push(make_pair(dist[s], s));
                    V stack;
                    while (!que.empty()) {
                        auto [d,u] = que.top();
                        que.pop();
                        if (d != min_d[u]) {
                            continue;
                        }
                        stack.push_back(u);
                        while (!stack.empty()) {
                            int u = stack.back();
                            stack.pop_back();
                            if (tid[u] != -1){
                                if(!i_bit[tid[u]]) {
                                    ++count_t;
                                    if (count_t == T - i_count) {
                                        atmost = d;
                                        goto cut;
                                    }
                                }
                            }
                            for (const auto& [v,_] : perturbed_g[u]) {
                                    // cout << v << endl;
                                if (ub[v] > 0) {
                                    continue;
                                }
                                long long d2 = min(d, dist[v]);
                                if (min_d[v] < d2) {
                                    min_d[v] = d2;
                                    if (d == d2) {
                                        stack.push_back(v);
                                    } else {
                                        que.push(make_pair(d2, v));
                                    }
                                }
                            }
                        }
                    }
                    cut:;

                }
                for (int u = 0; u < n; ++u) {
                    if (dist[u] > atmost) {
                        valid[u] = false;
                    }
                }
            }
            if (find(valid.begin(), valid.end(), true) == valid.end()) {
                continue;
            }
            vector<Data> di;
            for (int v = 0; v < n; ++v) {
                if (valid[v]) {
                    di.push_back(Data(v, dist[v], prev[v]));
                }
            }
            V id(n, -1);
            for (int x = 0; x < di.size(); ++x) {
                id[di[x].v] = total_size + x;
            }
            for (auto& a : di) {
                if (a.prev.first != -1 && a.prev.second == -1) {
                    a.prev.first = id[a.prev.first];
                }
            }
            my_bitset valid_bit(n);
            for (int u = 0; u < n; ++u) {
                if (valid[u]) {
                    valid_bit.set(u, true);
                }
            }
            for (const auto& q : bit_tree.find(i_bit, valid_bit)) {
                if (i_count * 2 + bit_counts[q] > T) {
                    continue;
                }
                const auto& j = bits[q];
                const vector<Data> dj(data.begin() + offsets[q], data.begin() + offsets[q + 1]);
                vector<Data> tmp;
                for (const auto& [x, y] : intersect(di, dj)) {
                    tmp.emplace_back(Data(di[x].v, di[x].cost + dj[y].cost, {total_size + x, offsets[q] + y}));
                }
                const my_bitset k = i_bit | j;
                bool merged = false;
                if (ongoing.count(k)) {
                    vector<Data> dk2;
                    size_t x = 0;
                    size_t y = 0;
                    while (x < ongoing[k].size() || y < tmp.size()) {
                        const int v1 = (x < ongoing[k].size()) ? ongoing[k][x].v : n, v2 = (y < tmp.size()) ? tmp[y].v : n;
                        if (v1 == v2) {
                            if (ongoing[k][x].cost <= tmp[y].cost) {
                                dk2.push_back(ongoing[k][x]);
                            } else {
                                dk2.push_back(tmp[y]);
                            }
                            x++,y++;
                        } else if (v1 < v2) {
                            dk2.push_back(ongoing[k][x]);
                            x++;
                        } else {
                            dk2.push_back(tmp[y]);
                            y++;
                        }
                    }
                    ongoing[k] = dk2;
                    merged = true;
                }
                if (!merged) {
                    if (k.count() * 2 <= T) {
                        i_set.insert({k.count(), k});
                    }
                    ongoing[k] = tmp;
                }
            }
            my_bitset j = all ^ i_bit;
            if (ongoing.count(j)) {
                const auto& dj = ongoing[j];
                for (const auto& [x, y] : intersect(di, dj)) {
                    if (setmin(min_ret, di[x].cost + dj[y].cost)) {
                        min_x = total_size + x;
                        min_prev = dj[y].prev;
                    }
                }
            }
            auto size = di.size();
            if (i_count * 3 <= T) {
                bit_tree.insert(i_bit, valid_bit, bits.size());
            }
            bits.push_back(i_bit);
            bit_counts.push_back(i_count);
            data.insert(data.end(), di.begin(), di.end());
            total_size += size;
            offsets.push_back(total_size);
        }
        if (min_ret == INFLL) {return {0,{}};}
        vector<P> es;
        vector<long long> stack = {min_x};
        if (min_prev.first != -1) {
            stack.push_back(min_prev.first);
        }
        if (min_prev.second != -1) {
            stack.push_back(min_prev.second);
        }
        while (!stack.empty()) {
            auto x = stack.back();
            stack.pop_back();
            if (data[x].prev.first != -1) {
                stack.push_back(data[x].prev.first);
                if (data[x].prev.second != -1) {
                    stack.push_back(data[x].prev.second);
                } else {
                    es.push_back({data[x].v, data[data[x].prev.first].v});
                }
            }
        }
        return make_pair((min_ret >> 32),es);
    };
    vector<P> solve(vector<vector<P>>& g,V& ts,bool valid=false){
        auto stime =chrono::system_clock::now();
        Sneiter_Solver::Reduction_RESULT reduced = Sneiter_Solver::reduce(g, ts);
        int total_edges = 0;for (const auto& a : reduced.g) {total_edges += a.size();}
        pair<int,vector<P>> result = Sneiter_Solver::solver(reduced.g, reduced.ts);
        pair<int,vector<P>> ans = Sneiter_Solver::restore(reduced,result);
        if(valid){
            if (!validate(g, ts, ans.first, ans.second)){
                cerr << "value = WA" << endl;
                cerr << "time = WA" << endl;
                throw runtime_error("orz");
            }else{
                cerr << "clear" << endl;
            }
        }
        auto time =chrono::system_clock::now() - stime;
        double etime =chrono::duration<double>(time).count();
        if(valid){
            cerr << "time = " << etime << std::endl;
            cerr << "value = " << ans.first << std::endl;
        }
        return ans.second;
    };
};

pair<vector<vector<pair<int,int>>>,vector<int>> read_input(){
    int N,M,T;
    vector<edge> es;	//edges
    vector<int> ts;		//terminals
    vector<bool> isTerminal;
    vector<vector<pair<int,int>>> g;
    string s,t;
    cin >> s >> t;
    assert(s=="SECTION" && t=="Graph");
    cin >> s >> N ;//Nodes
    assert(s=="Nodes");
    cin >> s >> M ;//Edges
    assert(s=="Edges");
    rep(i,M){
        cin >> s;
        assert(s=="E");
        int u1,v1,w1;
        cin >> u1 >> v1 >> w1;
        es.push_back({u1,v1,w1});
    }
    cin >> s;
    assert(s=="END");

    cin >> s >> t;
    assert(s=="SECTION" && t=="Terminals");
    cin >> s;
    assert(s=="Terminals");
    cin >> T;
    rep(i,T){
        cin>>s;
        assert(s=="T");
        int u1;
        cin >> u1;
        ts.push_back(u1-1);
    }
    
    cin >> s;
    assert(s=="END");
    cin >> t;
    assert(t=="EOF");
    g.resize(N,vector<pair<int,int>>{});
    rep(i,M){
        g[es[i].u-1].push_back({es[i].v-1,es[i].c});
        g[es[i].v-1].push_back({es[i].u-1,es[i].c});
    }
    return make_pair(g,ts);
}
/*
vector<vector<pair<int,int>>> g
g[u]={{v0,w0},{v1,w1},...}
road from u to vi, which weight is wi.

vector<int> ts
terminals(Point are needed to select.)

vector<pair<int,int>> ans
point point a to point b
*/

int main()
{
    auto input = read_input();
    auto g = input.first;
    auto ts = input.second;
    vector<pair<int,int>> ans = Sneiter_Solver::solve(g, ts,1);
    for (const auto& edge : ans) {
        std::cout << edge.first + 1 << " " << edge.second + 1 << std::endl;
    }
    return 0;
}
