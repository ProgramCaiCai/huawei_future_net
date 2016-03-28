
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
#include "CbcCutGenerator.hpp"
#include "CglAllDifferent.hpp"
#include "OsiClpSolverInterface.hpp"
#include "CglStored.hpp"
#include "CoinTime.hpp"


#include <algorithm>
#include <queue>
#include <vector>
#include <tuple>
using namespace std;
typedef unsigned int uint;

using namespace std;




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

vector<vector<int>> ins,outs;


OsiClpSolverInterface load_problem(vector<Edge> graph,vector<int> must,int start,int end){
    OsiClpSolverInterface ret;

    int noNodes = 0;
    for(auto e: graph) noNodes = max(noNodes,max(e.from,e.to)+1);

    auto in_id = [=](int x){return x+graph.size();};
    auto out_id = [=](int x){return x+noNodes + graph.size();};

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
        }

    for(uint i=0;i<noNodes;i++)
        if(!outs[i].empty()){
            solver.addRow(sumExpEq(outs[i],out_id(i)),0,0);
        }

    //balanced coodition
    for(int i=0;i<noNodes;i++)
        if(i!=start&& i!=end){
            solver.addRow(BiVector(in_id(i),out_id(i),1,-1),0,0);
        }

    for(int x:must)
        if(x!=start && x!=end){
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


vector<double> getSolution(const OsiClpSolverInterface &problem){
    CbcModel model(problem);
    model.setMaximumSeconds(2.0);
    model.branchAndBound();

    const double *solution = model.solver()->getColSolution();
    vector<double> ret;
    for(int i=0;i<topo.size();i++) ret.push_back(solution[i]);
    return ret;
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






bool addConstraints(OsiClpSolverInterface &problem,vector<double> solution){
    int n= (problem.getNumCols()- topo.size())/2;
    vector<int> p(n,-1);
    for(uint i=0;i<solution.size();i++) if(solution[i]) p[topo[i].from] = topo[i].to;


    for(int i=0;i<n;i++) cout<<" "<<p[i];
    cout<<endl;




    auto cycles = checkCycle(p);

    if(cycles.empty()) {


        for(auto e: must) if(p[e]==-1) assert(false);
        cout<<"No Cycles!"<<endl;
        return false;
    }

    for(auto cycle:cycles){
        vector<int> vars;


        cout<<"--"<<endl;
        for(auto elem:cycle){
            cout<<elem<<endl;
            for(auto e:ins[elem]) if(cycle.find(topo[e].from)!=cycle.end()) vars.push_back(e);
            for(auto e:outs[elem]) if(cycle.find(topo[e].to)!=cycle.end()) vars.push_back(e);
        }

        for(auto v:vars) cout<<v<<endl;
        sort(vars.begin(),vars.end());
        int p = unique(vars.begin(),vars.end()) - vars.begin();
        while(vars.size()>p) vars.pop_back();
        problem.addRow(sumExp(vars),0,cycle.size()-1);
    }


    return true;
}




vector<int> get_path(vector<double> solution){
    vector<bool> vis(1000,0);

    vector<int> path;
    int now = startNode;
    vis[now]=1;

    int len = 0;
    while(now!=endNode){
        for(Edge e: ve[now]) if(solution[e.id]) {
                if(!vis[e.to]){
                    now = e.to;
                    vis[e.to]=1;
                    len += e.length;
                    path.push_back(e.id);
                }else{
                    assert(false);
                }
            }
    }

    assert(now==endNode);
    for(auto x: must) assert(vis[x]==1);
    cout<<"Length:"<<len<<" Valid Path"<<endl;
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
    return make_tuple(start,end,must);
};






void init(char *topoStrs[5000], int edge_num, char *demandStr){
    topo = readTopo(topoStrs,edge_num);
    demand = readDemand(demandStr);
    startNode = get<0>(demand);
    endNode = get<1>(demand);
    must = get<2>(demand);
}


void search_route(char *topoStrs[5000], int edge_num, char *demandStr){
	srand(time(0));

	init(topoStrs,edge_num,demandStr);

    for(auto e:topo) ve[e.from].push_back(e);

    OsiClpSolverInterface problem = load_problem(topo,must,startNode,endNode);


    vector<double> solution;
    do {
        solution = getSolution(problem);
    }while(addConstraints(problem,solution));

    auto path = get_path(solution);

    for(int x:path) record_result(x);

}

