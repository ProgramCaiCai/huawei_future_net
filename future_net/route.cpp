
#include "route.h"
#include "lib_record.h"
#include <stdio.h>
#include <bits/stdc++.h>
#include "lp_lib.h"
#include <sys/time.h>

using namespace std;

struct Edge{
    int idx,id,from,to,length;
    Edge(){}
    Edge(int idx,int id,int from,int to,int length):idx(idx),id(id),from(from),to(to),length(length){}
};
namespace Utils{
    template <class T>
    bool in_set(const set<T> &s,const T &elem){
        return s.find(elem) != s.end();
    }

    template <class T>
    set<T> vector_to_set(const vector<T> &vec){
        set<T> ret;
        for(auto e:vec) ret.insert(e);
        return ret;
    }

    vector<string> &split(const string &s, char delim, vector<std::string> &elems) {
        stringstream ss(s);
        string item;
        while (getline(ss, item, delim)) {
            elems.push_back(item);
        }
        return elems;
    }

    vector<std::string> split(const string &s, char delim) {
        vector<string> elems;
        split(s, delim, elems);
        return elems;
    }

    template<class T>
    void print_vector(vector<T> &vec){
        for(auto elem:vec) cout<<elem<<" ";
        cout<<endl;
    }

    int str2int(const string &s){
        return atoi(s.c_str());
    }

    vector<int> strVec2int(const vector<string> &s){
        vector<int> ret;
        for(auto e:s) ret.push_back(stoi(e));
        return ret;
    }

    double now() {
        struct timeval tp;
        gettimeofday(&tp, NULL);
        long int ms = tp.tv_sec * 1000 + tp.tv_usec / 1000;
        return ms / 1000.0;
    }
    template<class T>
    void uniquefy(vector<T> &v){
        sort(v.begin(),v.end());
        auto end = unique(v.begin(),v.end());
        while(v.end()!=end) v.pop_back();
    }

};
using namespace Utils;

struct Graph{
    static const int N = 1010;
    vector<Edge> edges;
    vector<Edge> ve[N],vr[N];
    int noNodes=0;
    int noEdges=0;

    int startNode,endNode;
    vector<int> must;

    Graph(){edges.push_back(Edge());}
    void add_edge(int id,int u,int v,int len){
        Edge e = Edge(++noEdges,id,u,v,len);
        noNodes = max(noNodes,max(u,v)+1);
        edges.push_back(e);
        ve[e.from].push_back(e);
        vr[e.to].push_back(e);
    }

    int idx_edge(int x) const {return x;}
    int idx_in(int x) const {return noEdges + x + 1;}
    int idx_out(int x) const {return noEdges + noNodes +x +1;}

    vector<int> idx_edge_in_nodeset(vector<int> nodeset) const {
        set<int> s = vector_to_set(nodeset);
        vector<int> ret;

        for(auto elem: s) {
            for(auto edge: ve[elem]) {
                if(in_set(s,edge.to)) ret.push_back(edge.idx);
            }
        }

        return ret;
    }
    vector<int> idx_incoming_edge(int orig) const {
        vector<int> ret;
        for(auto e:vr[orig]) ret.push_back(e.idx);
        return ret;
    }
    vector<int> idx_outgoing_edge(int orig) const {
        vector<int> ret;
        for(auto e:ve[orig]) ret.push_back(e.idx);
        return ret;
    }


   void readTopo(char *topo[5000], int edge_num){
        for(int i=0;i<edge_num;i++){
            auto v = Utils::split(topo[i],',');
            vector<int> xs = Utils::strVec2int(v);
            add_edge(xs[0],xs[1],xs[2],xs[3]);
        }
    }

    void readDemand(char *demandStr){
        int start,end;
        auto v = split(demandStr,',');
        startNode = stoi(v[0]);
        endNode = stoi(v[1]);
        auto v2 = split(v[2],'|');
        must=strVec2int(v2);
    };


};
struct SparseVector{
    vector<double> values;
    vector<int> idxs;
    SparseVector(){};
    SparseVector(vector<int> _idxs,vector<double> _values): idxs(_idxs),values(_values){}

    void add_col(int idx,double value){
        idxs.push_back(idx);
        values.push_back(value);
    }

    SparseVector * add_to_lp(lprec *lp,int constr_type, double rhs){
        add_constraintex(lp,values.size(),&values[0],&idxs[0],constr_type,rhs);
        return this;
    }

    static SparseVector* sumExp(vector<int> _idxs){
        vector<double> _values;
        for(auto x: _idxs) _values.push_back(1);
        return new SparseVector(_idxs,_values);
    }

    static SparseVector* sumExpMinus(vector<int> _idxs,int minusidx){
        vector<double> _values;
        for(auto x: _idxs) _values.push_back(1);
        _idxs.push_back(minusidx);
        _values.push_back(-1);
        return new SparseVector(_idxs,_values);
    }

    static SparseVector* sumExpMinus(vector<int> _idxs,vector<int> _idxs2){
        vector<double> _values;
        for(auto x: _idxs) _values.push_back(1);
        for(auto x: _idxs2) _values.push_back(-1);
        for(auto x: _idxs2) _idxs.push_back(x);
        return new SparseVector(_idxs,_values);
    }

    static SparseVector* unary_one(int idx){
        vector<int> _idxs;
        vector<double> _values;
        _idxs.push_back(idx);
        _values.push_back(1);
        return new SparseVector(_idxs,_values);
    }

    static SparseVector* minus(int idx1,int idx2){
        vector<int> _idxs;
        vector<double> _values;
        _idxs.push_back(idx1);
        _idxs.push_back(idx2);
        _values.push_back(1);
        _values.push_back(-1);
        return new SparseVector(_idxs,_values);
    }

};

Graph *g = new Graph();

lprec * build_problem(const Graph *g) {
    lprec *lp = make_lp(0,g->noEdges + g->noNodes *2);
    set_add_rowmode(lp,TRUE);



    for(int i=1;i<=g->noEdges + g->noNodes *2;i++) set_binary(lp,i,TRUE);
    for(int i=1;i<=g->noEdges;i++) set_obj(lp,i,g->edges[i].length);

    for(int i=0;i<g->noNodes;i++) {
        SparseVector::sumExpMinus(g->idx_incoming_edge(i),g->idx_in(i))->add_to_lp(lp,EQ,0);
        SparseVector::sumExpMinus(g->idx_outgoing_edge(i),g->idx_out(i))->add_to_lp(lp,EQ,0);

        if(i!= g->startNode && i!= g->endNode){
            SparseVector::minus(g->idx_in(i),g->idx_out(i))->add_to_lp(lp,EQ,0);
        }
    }


    for(auto elem: g->must) {
        if(elem!= g->startNode && elem!= g->endNode) {
            SparseVector::unary_one(g->idx_in(elem))->add_to_lp(lp,EQ,1);
            SparseVector::unary_one(g->idx_out(elem))->add_to_lp(lp,EQ,1);
        }
    }


    SparseVector::unary_one(g->idx_in(g->startNode))->add_to_lp(lp,EQ,0);
    SparseVector::unary_one(g->idx_out(g->startNode))->add_to_lp(lp,EQ,1);

    SparseVector::unary_one(g->idx_in(g->endNode))->add_to_lp(lp,EQ,1);
    SparseVector::unary_one(g->idx_out(g->endNode))->add_to_lp(lp,EQ,0);


    set_add_rowmode(lp,FALSE);


    return lp;
}

vector<int> get_solution(lprec *lp){
    vector<int> v;
    v.push_back(0);
    for(int i=1;i<=g->noEdges;i++) {
        v.push_back(get_var_primalresult(lp,get_Norig_rows(lp)+i)+1e-8);
    }
    return v;
}

vector<int> get_pvec(Graph *g,const vector<int> &solution){
    vector<int> p(g->noNodes,-1);
    for(int i=1;i<=g->noEdges;i++) if(solution[i]) p[g->edges[i].from] = g->edges[i].to;
    return p;
}

vector<vector<int>> checkCycle(const vector<int> &x){
    int groups = 0;
    vector<bool> vis(x.size(),0);

    vector<vector<int>> ret;
    vector<int> tmp;
    for(int i=0;i<x.size();i++){
        tmp.clear();
        int t = i;
        if(vis[t]==0) {
            tmp.push_back(t);

            while(x[t]!=-1 ) {
                t = x[t];
                vis[t] = 1;
                if(t==i) break;
                tmp.push_back(t);

            }
            if(t==i && tmp.size()>1) ret.push_back(tmp);
        }
    }
    return ret;
}

vector<vector<int>> all_loops(Graph *g,const vector<int> &solution){
    vector<vector<int>> ret;
    auto p = get_pvec(g,solution);

    return checkCycle(p);
}

vector<int> get_path(Graph *g,const vector<int> &solution){
    if(solution.empty()) return vector<int>();
    vector<bool> vis(1000,0);

    vector<int> path;
    int now = g->startNode;
    vis[now]=1;

    int len = 0;

    double valid = true;
    while(now!=g->endNode){
        int moved = 0;
        for(Edge e: g->ve[now]) if(solution[e.idx]) {
                moved +=1;
                if(!vis[e.to]){
                    now = e.to;
                    vis[e.to]=1;
                    len += e.length;
                    path.push_back(e.id);
                }else{
                    valid = false;
                    break;
                }
            }
        if(moved!=1){
            valid = false;
            break;
        }
    }

    if (now != g->endNode) valid = false;
    for (auto x: g->must) if (vis[x] != 1) valid = false;

    if (valid) {

        cout<<"Valid Path Len="<<len<<endl;
        return path;
    } else {

        return vector<int>();
    }
}

bool add_subtour_constraint(Graph *g,lprec *lp,const vector<int> &solution){
    auto loops = all_loops(g,solution);
    if(loops.empty()) return false;


    for(auto loop:loops){

        auto edgeidxs = g->idx_edge_in_nodeset(loop);
        print_vector(loop);
        print_vector(edgeidxs);
        SparseVector::sumExp(g->idx_edge_in_nodeset(loop))->add_to_lp(lp,LE,loop.size()-1);
    }

    cout<<"Constraint Added"<<endl;
    return true;
}


struct TimedSearch {
    double limit;
    double t_start;

    Graph *g;
    lprec *lp;
    vector<int> solution;


    TimedSearch(Graph *g,lprec *lp) {
        this->g = g;
        this->lp = lp;
    }

    double timeSinceStart() {
        return now() - t_start;
    }

    void mainLoop() {
        vector<int> solution;
        double value=1e10;
        double flag = true;

        int iters =0;
        do {
            if (timeSinceStart() > limit &&flag) {
                lp = build_problem(g);
                set_verbose(lp,0);
                set_timeout(lp,0);
                flag= false;
                set_break_at_first(lp,1);
            }
            solve(lp);
            value= min(value,get_objective(lp));
            solution = get_solution(lp);
        } while (add_subtour_constraint(g,lp,solution));
        this->solution = solution;
    }

    vector<int> run(double limit) {
        t_start = now();
        this->limit = limit;
        mainLoop();
        return solution;
    }
};

void search_route(char *topo[5000], int edge_num, char *demand) {

    g->readTopo(topo,edge_num);
    g->readDemand(demand);

    lprec *lp = build_problem(g);
    set_timeout(lp,2);
    set_verbose(lp,0);
    //set_break_at_first(lp, 1);
    TimedSearch search(g,lp);

    auto result = search.run(5.5);
    auto path = get_path(g,result);

    for (auto elem:path)
        record_result(elem);
}
