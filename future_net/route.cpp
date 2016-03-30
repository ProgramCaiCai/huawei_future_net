
#include "route.h"
#include "lib_record.h"
#include <stdio.h>
#include <string>
#include <sstream>
#include <vector>
#include <cstdlib>
#include <cstring>
#include <algorithm> 
#include <sys/time.h>




#include <cassert>
#include <iomanip>
#include <array>

#include "CoinPragma.hpp"
// For Branch and bound
#include "OsiSolverInterface.hpp"
#include "CbcModel.hpp"
#include "CoinModel.hpp"
// For all different
#include "CbcBranchCut.hpp"
#include "CbcBranchActual.hpp"
#include "CbcBranchAllDifferent.hpp"
#include "CglCutGenerator.hpp"
#include "CglZeroHalf.hpp"
#include "CglFlowCover.hpp"
#include "CglProbing.hpp"

#include "CbcCutGenerator.hpp"
#include "CglAllDifferent.hpp"
#include "OsiClpSolverInterface.hpp"
#include "CglStored.hpp"
#include "CoinTime.hpp"

#include "CglRedSplit.hpp"
#include <algorithm>
#include <queue>
#include <vector>
#include <tuple>
#include <unordered_map>
#include <OsiClpSolverInterface.hpp>
#include <CbcSolver.hpp>


using namespace std;
typedef unsigned int uint;






#define N 1010
#define M 1010*8*4
#define inf 1000000000
#define inf 1000000000

struct Dinic {
    int s, t, n, pre[N], cur[N], h[N], level[N], sign, q[N];
    int  to[M], ne[M], e;


    bool vis[N];

    double cap[M],flow;
    void liu(int u, int v, double w) {
        to[e] = v, ne[e] = h[u], cap[e] = w;
        h[u] = e++;
    }
    void link(int u, int v, double w) {
        liu(u, v, w);
        liu(v, u, 0);
    }
    void init(int n) {
        for (int i = 0; i <= n; ++i)
            h[i] = -1;
        e = 0;
        this->n =n;
    }
    bool bfs() {
        int L = 0, R = 0;
        fill(level, level + n, -1);
        sign = q[R++] = t;
        level[t] = 0;
        while (L < R && level[s] == -1) {
            int c = q[L++];
            for (int k = h[c]; ~k; k = ne[k]) {
                if (cap[k ^ 1] > 0 && level[to[k]] == -1)
                    level[to[k]] = level[c] + 1, q[R++] = to[k];
            }
        }
        return ~level[s];
    }

    void push() {
        double pl = inf;
        int p, k;
        for (p = t; p != s; p = to[k ^ 1]) {
            k = pre[p];
            pl = min(pl, cap[k]);
        }
        for (p = t; p != s; p = to[k ^ 1]) {
            k = pre[p];
            cap[k] -= pl;
            cap[k ^ 1] += pl;
            if (cap[k] == 0)
                sign = to[k ^ 1];
        }
        flow += pl;
    }
    void dfs(int c) {
        if (c == t)
            push();
        else {
            for (int &k = cur[c]; ~k; k = ne[k])
                if (cap[k] > 0 && level[to[k]] + 1 == level[c]) {
                    pre[to[k]] = k;
                    dfs(to[k]);
                    if (level[sign] > level[c])
                        return;
                    sign = t;
                }
            level[c] = -1;
        }
    }

    void dfs2(int x){
        vis[x]=1;
        for (int &k = h[x]; ~k; k = ne[k])
            if(cap[k]>0 && !vis[to[k]]) {
                dfs2(to[k]);
            }
    }


    const bool * mincut(){
        for(int i=0;i<=n;i++) vis[i] = 0;
        dfs2(s);
        return vis;
    }


    double run(int _s, int _t) {
        s = _s, t = _t;
        flow = 0;
        while (bfs()) {
            for (int i = 0; i < n; ++i)
                cur[i] = h[i];
            dfs(s);
        }
        return flow;
    }
} maxflow;


struct Kosaraju{
    int n,h1[N],ne1[M],to1[M],e1,h2[N],ne2[M],to2[M],e2;
    int sta[N], top, mark[N], color;
    bool vis[N];
    void edge1(int u, int v) {
        to1[e1] = v, ne1[e1] = h1[u];
        h1[u] = e1++;
    }
    void edge2(int u, int v) {
        to2[e2] = v, ne2[e2] = h2[u];
        h2[u] = e2++;
    }
    void link(int u, int v) {
        edge1(u, v);
        edge2(v, u);
    }
    void dfs(int idx) {
        vis[idx] = true;
        for (int i = h1[idx]; ~i ; i=ne1[i])
            if (!vis[to1[i]])
                dfs(to1[i]);
        sta[top++] = idx;
    }
    void rdfs(int idx) {
        vis[idx] = true;
        mark[idx] = color;
        for (int i = h2[i]; ~i; i=ne2[i])
            if (!vis[to2[i]])
                rdfs(to2[i]);
    }
    void solve() {
        int i;
        memset(vis, 0, sizeof(vis));
        for (i = top = 0; i < n; ++i)
            if (!vis[i])
                dfs(i);
        memset(vis, 0, sizeof(vis));
        for (i = top - 1, color = 0; i >= 0; --i)
            if (!vis[sta[i]]) rdfs(sta[i]), ++color;
    }
    void init(int n) {
        for (int i = 0; i <= n; ++i)
            h2[i] = h1[i] = -1;
        e1 = e2 = 0;
    }
}sp;

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


int str2int(const string &s){
	return atoi(s.c_str());
}


vector<int> strVec2int(const vector<string> &s){
    vector<int> ret;
    for(auto e:s) ret.push_back(stoi(e));
    return ret;
}



struct Edge{
    int id,from,to,length;
    Edge(){}
    Edge(int id,int from,int to,int length):id(id),from(from),to(to),length(length){}
};
vector<Edge> topo;
tuple<int,int,vector<int>> demand ;
int startNode = get<0>(demand);
int endNode = get<1>(demand);
vector<int> must = get<2>(demand);
vector<Edge> ve[1010];
vector<Edge> vr[1010];
int noNodes;



CoinPackedVector UnaryVector(int ind,double x){
    int inds[1];
    double val[1];
    inds[0]=ind;
    val[0]=x;
    return CoinPackedVector(1,inds,val);
}


CoinPackedVector BiVector(int ind1,int ind2,double x1,double x2){
    int inds[2];
    double val[2];
    inds[0] = ind1;
    inds[1] = ind2;
    val[0]=x1;
    val[1]=x2;
    return CoinPackedVector(2,inds,val);
}

CoinPackedVector sumExpEq(vector<int> inds,int equalIdx){
    vector<double> vals;
    for(int i=0;i<inds.size();i++) vals.push_back(1);
    inds.push_back(equalIdx);
    vals.push_back(-1);
    return CoinPackedVector((int)inds.size(),&inds[0],&vals[0]);
}

CoinPackedVector sumExp(vector<int> inds){
    vector<double> vals;
    for(int i=0;i<inds.size();i++) vals.push_back(1);
    return CoinPackedVector((int)inds.size(),&inds[0],&vals[0]);
}


CoinPackedVector sumMinus(vector<int> inds,vector<int> inds2){
    vector<double> vals;
    for(auto x:inds) vals.push_back(1);
    for(auto x:inds2) vals.push_back(-1);
    return CoinPackedVector((int)inds.size(),&inds[0],&vals[0]);
}


vector<vector<int>> ins,outs;


OsiClpSolverInterface load_problem(vector<Edge> graph,vector<int> must,int start,int end){

    int noNodes = 0;
    for(auto e: graph) noNodes = max(noNodes,max(e.from,e.to)+1);

    auto in_id = [&](int x){return x+graph.size();};
    auto out_id = [&](int x){return x+noNodes + graph.size();};

    OsiClpSolverInterface solver;

    for(auto e:graph){
        solver.addCol(0,NULL,NULL,0,1,e.length);
    }
    for(int i=0;i<2*noNodes;i++) solver.addCol(0,NULL,NULL,0,1,0);



    ins.resize(noNodes);
    outs.resize(noNodes);



    for(uint i=0;i<graph.size();i++) {
        ins[graph[i].to].push_back(i);
        outs[graph[i].from].push_back(i);
    }

    for(uint i=0;i<noNodes;i++)
        if(!ins[i].empty()){
            solver.addRow(sumExpEq(ins[i],in_id(i)),0,0);
        } else{
            solver.addRow(UnaryVector(in_id(i),1),0,0);
        }

    for(uint i=0;i<noNodes;i++)
        if(!outs[i].empty()){
            solver.addRow(sumExpEq(outs[i],out_id(i)),0,0);
        } else{
            solver.addRow(UnaryVector(out_id(i),1),0,0);
        }

    //balanced coodition
    for(int i=0;i<noNodes;i++)
        if(i!=start&& i!=end){
            solver.addRow(BiVector(in_id(i),out_id(i),1,-1),0,0);
        }

    for(int x:must) {
            solver.addRow(UnaryVector(in_id(x),1),1,1);
            solver.addRow(UnaryVector(out_id(x),1),1,1);
    }

    solver.addRow(UnaryVector(in_id(start),1),0,0);
    solver.addRow(UnaryVector(out_id(start),1),1,1);

    solver.addRow(UnaryVector(in_id(end),1),1,1);
    solver.addRow(UnaryVector(out_id(end),1),0,0);

    for(int i=0;i<graph.size();i++) solver.setInteger(i);



    return solver;

}




vector<set<int>> checkCycle(const vector<int> &x){

    int groups = 0;
    vector<bool> vis(x.size(),0);

    vector<set<int>> ret;
    set<int> tmp;
    for(int i=0;i<x.size();i++){
        tmp.clear();
        int t = i;
        if(vis[t]==0) {
            tmp.insert(t);

            while(x[t]!=-1 ) {
                t = x[t];
                vis[t] = 1;
                if(t==i) break;
                tmp.insert(t);

            }
            if(t==i && tmp.size()>1) ret.push_back(tmp);
        }
    }
    return ret;
}


template<class T>
void uniquefy(vector<T> &v){
    sort(v.begin(),v.end());
    auto end = unique(v.begin(),v.end());
    while(v.end()!=end) v.pop_back();
}

map<set<int>,int>  allTSPCuts;
vector<set<int>> nowCuts;



CoinPackedVector getCycleVars(const set<int> &cycle){
    vector<int> vars3;

    for(auto elem:cycle){
        for(auto e:ins[elem]) if(cycle.find(topo[e].from)!=cycle.end()) vars3.push_back(e);
        for(auto e:outs[elem]) if(cycle.find(topo[e].to)!=cycle.end()) vars3.push_back(e);
    }
    uniquefy(vars3);

    return sumExp(vars3);
}



void AddCycleConstraint(OsiClpSolverInterface &problem,const set<int> &cycle){
    problem.addRow(getCycleVars(cycle),0,cycle.size()-1);
}


bool addConstraints(OsiClpSolverInterface &problem,vector<double> solution){
    int n= (problem.getNumCols()- topo.size())/2;
    vector<int> p(n,-1);
    for(uint i=0;i<solution.size();i++) if(solution[i]) p[topo[i].from] = topo[i].to;

    auto cycles = checkCycle(p);

    if(cycles.empty()) {
        for(auto e: must) if(p[e]==-1) {
                cout<<"Node "<<e<<"Unreached";
                assert(false);
            }
        cout<<"No Cycles!"<<endl;
        return false;
    }

    for(auto cycle:cycles){
        allTSPCuts[cycle]=-1;
        AddCycleConstraint(problem,cycle);
    }

    for(auto cycle : nowCuts) if(allTSPCuts[cycle]==1){
            allTSPCuts[cycle]=-1;
            AddCycleConstraint(problem,cycle);
        }
    nowCuts.clear();

    return true;
}



class TSPCut:public CglCutGenerator{
public:

    /**@name Generate Cuts */
    //@{
    /** Generate cuts for the model data contained in si.
    The generated cuts are inserted into and returned in the
    collection of cuts cs.
    */


    bool canReach[N];


    void dfs(int x,const double *solution){
        canReach[x] = 1;
        for(auto e: vr[x]) if(fabs(solution[e.id])>1e-6  && !canReach[e.from]){
                dfs(e.from,solution);
            }
    }


    void generateCuts( const OsiSolverInterface & si, OsiCuts & cs,
                       const CglTreeInfo info = CglTreeInfo()){

        int n = noNodes ;


        memset(canReach,0,sizeof(canReach));


        const double *tmpSolution = si.getColSolution();
        dfs(endNode,tmpSolution);


        maxflow.init(n);
        for(int i=0;i<topo.size();i++)
            if(fabs(tmpSolution[i])>1e-6) {
                maxflow.link(topo[i].from,topo[i].to,tmpSolution[i]);
            }


        bool bmust[N];
        for(auto e:must) bmust[e]=1;
        bmust[endNode]=1;


        for(int i=0;i<noNodes;i++) if(canReach[i] && i!=endNode){

                Dinic maxflowcopy = maxflow;
                double flow = maxflowcopy.run(i,endNode);


                if(flow!=1){
                    const bool *cut = maxflowcopy.mincut();

                    set<int> one,other;
                    for(int i=0;i<noNodes;i++) if(canReach[i] && cut[i]) one.insert(i);

                    for(int i=0;i<noNodes;i++) if(canReach[i] && !cut[i]) other.insert(i);




                    vector<int> atob,btoa;
                    for(int i=0;i<topo.size();i++){
                            if(cut[topo[i].from]  && !cut[topo[i].to]) atob.push_back(i);
                        }
                    cout<<"Across:"<<atob.size()<<endl;



                    if(atob.size()>0){
                        OsiRowCut atobcut,btoacut;
                        atobcut.setRow(sumExp(atob));
                        atobcut.setLb(1);
                        atobcut.setUb(10000);



                        cs.insert(atobcut);
                    }

                    //cs.insert(btoacut);
                }


            }


    }

    TSPCut () {}
    CglCutGenerator * clone() const {

        return new TSPCut();
    }
    inline int getAggressiveness() const
    { return 100;}

    /**
       Set Aggressiveness - 0 = neutral, 100 is normal root node.
       Really just a hint to cut generator
    */
    inline void setAggressiveness(int value)
    { aggressive_=value;}
    /// Set whether can do global cuts


    inline bool canDoGlobalCuts() const
    {return true;}
    /**
       Returns true if may generate Row cuts in tree (rather than root node).
       Used so know if matrix will change in tree.  Really
       meant so column cut generators can still be active
       without worrying code.
       Default is true
    */
    bool mayGenerateRowCutsInTree() const{
        return true;
    }
    /// Return true if needs optimal basis to do cuts
    bool needsOptimalBasis() const {
        return false;
    };

    int maximumLengthOfCutInTree() const
    { return COIN_INT_MAX;}

private:

    int aggressive_;
};





void addFakeCost(OsiClpSolverInterface &problem,int amount){

    const double *coefs = problem.getObjCoefficients();
    for(int i=0;i<topo.size();i++) problem.setObjCoeff(i,coefs[i]+amount);
}

void totalFake(OsiClpSolverInterface &problem){
    for(int i=0;i<topo.size();i++) problem.setObjCoeff(i,0);
}

vector<double> getSolution(OsiClpSolverInterface &problem){


    CbcModel model(problem);
 //   model.addCutGenerator(new TSPCut(),-1);
    model.setLogLevel(0);
    model.setMaximumSeconds(1);
    model.initialSolve();
    model.branchAndBound();

    if(model.isProvenInfeasible()) return vector<double>();

    const double *solution = model.getColSolution();
    vector<double> ret;
    for(int i=0;i<topo.size();i++) ret.push_back(solution[i]);
    return ret;
}






vector<int> get_path(vector<double> solution){

    cout<<"Getting Path!"<<endl;

    vector<bool> vis(1000,0);

    vector<int> path;
    int now = startNode;
    vis[now]=1;

    int len = 0;
    while(now!=endNode){
        int moved = 0;
        for(Edge e: ve[now]) if(solution[e.id]) {
                moved +=1;
                if(!vis[e.to]){


                    if(e.to==241){
                        cout<<e.id<<" "<<e.from<<endl;
                    }


                    now = e.to;
                    vis[e.to]=1;
                    len += e.length;
                    path.push_back(e.id);
                }else{
                    assert(false);
                }
            }
        if(moved!=1){
            cout<<"Stuck! moved="<<moved<<endl;
            break;
        }
    }

    assert(now==endNode);
    for(auto x: must) assert(vis[x]==1);
    cout<<"Length:"<<len<<" Valid Path"<<endl;


    cout<<"Cycle Constraints:"<<allTSPCuts.size()<<endl;
    return path;
}


vector<Edge> readTopo(char *topo[5000], int edge_num){
    vector<Edge> ret;
    for(int i=0;i<edge_num;i++){
        auto v = split(topo[i],',');
        vector<int> xs = strVec2int(v);
        ret.push_back(Edge(xs[0],xs[1],xs[2],xs[3]));
    }
    return ret;
}

tuple<int,int,vector<int>> readDemand(char *demandStr){
    int start,end;
    vector<int> must;


    auto v = split(demandStr,',');
    start = stoi(v[0]);
    end = stoi(v[1]);
    auto v2 = split(v[2],'|');
    must=strVec2int(v2);


    vector<int> ret;
    for(auto x:must) if(x!=start&&x!=end) ret.push_back(x);

    return make_tuple(start,end,ret);
};






void init(char *topoStrs[5000], int edge_num, char *demandStr){
    topo = readTopo(topoStrs,edge_num);
    demand = readDemand(demandStr);
    startNode = get<0>(demand);
    endNode = get<1>(demand);
    must = get<2>(demand);
}




set<set<int>> all_triangles(){

    map<pair<int,int>,int>  mp;
    set<set<int>> ret;

    for(auto e:topo) mp[make_pair(e.from,e.to)] =1;

    for(int a=0;a<noNodes;a++){
        for(auto e: ve[a]) {
            int b = e.to;
            for(auto e: vr[a]){
                int c = e.from;

                if(mp[make_pair(b,c)]){


                    set<int> s;
                    s.insert(a);
                    s.insert(b);
                    s.insert(c);
                    ret.insert(s);
                }
            }
        }
    }
    return ret;
}





void search_route(char *topoStrs[5000], int edge_num, char *demandStr){
	srand(time(0));

	init(topoStrs,edge_num,demandStr);

    for(auto e:topo) ve[e.from].push_back(e);
    for(auto e:topo) vr[e.to].push_back(e);
    for(auto e:topo) noNodes = max(noNodes,max(e.from,e.to)+1);


    //for(auto triangle:all_triangles())  nowCuts.push_back(triangle);

    OsiClpSolverInterface problem = load_problem(topo,must,startNode,endNode);

    bool hasSolution = true;

    double esplasedTime = 0.0;
    double onetime = 2.0;
    const double totaltime = 9.5;


    int solvedTime = 0;


    //totalFake(problem);


    vector<double> solution;










    do {
        solvedTime++;
        solution = getSolution(problem);

        if(solvedTime>=10 && solvedTime%2==0) addFakeCost(problem,1);
        if(solution.empty()) {

            hasSolution = false;
            break;
        }
        esplasedTime += onetime;
    }while(addConstraints(problem,solution));


    cout<<"Resolved:"<<solvedTime<<"times"<<endl;

    if(hasSolution){
        auto path = get_path(solution);
        for(int x:path) record_result(x);
    }

}

