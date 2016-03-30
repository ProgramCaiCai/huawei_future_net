#include "route.h"
#include "lib_record.h"
#include <bits/stdc++.h>

#include "OsiSolverInterface.hpp"
#include "CbcModel.hpp"
#include "CglFlowCover.hpp"
#include "CbcCutGenerator.hpp"
#include "OsiClpSolverInterface.hpp"
#include "CoinTime.hpp"
using namespace std;
typedef unsigned int uint;

#define N 1010
#define M 1010*8*4
#define inf 1000000000

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

    CoinPackedVector cv = getCycleVars(cycle);

//    for(int i=0;i<cv.getNumElements();i++) {
//
//        int idx= cv.getIndices()[i];
//        problem.setObjCoeff(idx,problem.getObjCoefficients()[idx]+1);
//    }

//    for(auto e: topo) if(cycle.find(e.from)!=cycle.end()  && cycle.find(e.to)!=cycle.end()){
//            problem.setObjCoeff(e.id,problem.getObjCoefficients()[e.id]+1);
//        }

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
        cout << "Cycles:";
        for (auto e:cycle) cout << e << " ";
        cout << endl;
    }

    for(auto cycle : nowCuts) if(allTSPCuts[cycle]==1){
            allTSPCuts[cycle]=-1;
            AddCycleConstraint(problem,cycle);
        }
    nowCuts.clear();

    return true;
}


void setFakeCost(OsiClpSolverInterface &problem, int amount) {

    const double *coefs = problem.getObjCoefficients();
    for (int i = 0; i < topo.size(); i++) problem.setObjCoeff(i, topo[i].length + amount);
}

void constantWeight(OsiClpSolverInterface &problem, int c) {
    for (int i = 0; i < topo.size(); i++) problem.setObjCoeff(i, c);
}

void randObjective(OsiClpSolverInterface &problem) {
    for (int i = 0; i < topo.size(); i++) problem.setObjCoeff(i, rand() % 20 + 1);
}



vector<double> getSolution(OsiClpSolverInterface &problem){


    CbcModel model(problem);
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

    double valid = true;

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
                    valid = false;
                    break;
                }
            }
        if(moved!=1){
            valid = false;
            break;
        }
    }


    if (now != endNode) valid = false;
    for (auto x: must) if (vis[x] != 1) valid = false;

    if (valid) {
        return path;
    } else {

        return vector<int>();
    }
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


double now() {
    struct timeval tp;
    gettimeofday(&tp, NULL);
    long int ms = tp.tv_sec * 1000 + tp.tv_usec / 1000;
    return ms / 1000.0;
}


struct TimedSearch {
    double limit;
    OsiClpSolverInterface *problem;
    double t_start;
    vector<double> solution;


    TimedSearch(OsiClpSolverInterface *problem) {
        this->problem = problem;
    }


    double timeSinceStart() {
        return now() - t_start;
    }


    void mainLoop() {
        vector<double> solution;
        do {

            if (timeSinceStart() > limit) break;
            solution = getSolution(*problem);
        } while (addConstraints(*problem, solution));
        this->solution = solution;
    }

    vector<double> run(double limit) {
        t_start = now();
        this->limit = limit;
        mainLoop();
        return solution;
    }

};









void search_route(char *topoStrs[5000], int edge_num, char *demandStr){
	srand(time(0));

	init(topoStrs,edge_num,demandStr);

    for(auto e:topo) ve[e.from].push_back(e);
    for(auto e:topo) vr[e.to].push_back(e);
    for(auto e:topo) noNodes = max(noNodes,max(e.from,e.to)+1);


    OsiClpSolverInterface problem = load_problem(topo,must,startNode,endNode);

    bool hasSolution = true;



    int solvedTime = 0;

    vector<double> solution;


    TimedSearch search(&problem);

    solution = search.run(3.0);


    if (get_path(solution).empty()) {

        for (int i = 1; i <= 3; i++) {
            setFakeCost(problem, i * 5);
            solution = search.run(1.0);
            if (!get_path(solution).empty()) break;
        }
    }

    if (get_path(solution).empty()) {
        constantWeight(problem, 0);
        solution = search.run(3.0);
    }

    cout<<"Resolved:"<<solvedTime<<"times"<<endl;

    if(hasSolution){
        auto path = get_path(solution);
        for(int x:path) record_result(x);
    }

}

