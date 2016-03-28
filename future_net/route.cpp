
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
vector<Edge> vr[1010];
int noNodes;

class TSPEvent:public CbcEventHandler{
    virtual CbcEventHandler* clone() {
        return new TSPEvent();
    }
    virtual CbcAction event(CbcEventHandler::CbcEvent e) {

        cout<<e<<endl;
        if (e == CbcEventHandler::solution) {
            cout<<"meow!!"<<endl;
            return CbcEventHandler::addCuts;
        }
    }
};






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




void AddCycleConstraint(OsiClpSolverInterface &problem,const set<int> &cycle){


    vector<int> vars1,vars2,vars3;
    for(auto elem:cycle){
        for(auto e:ins[elem]) if(cycle.find(topo[e].from)==cycle.end()) vars1.push_back(e);
        for(auto e:outs[elem]) if(cycle.find(topo[e].to)==cycle.end()) vars2.push_back(e);
    }


    for(auto elem:cycle){
        for(auto e:ins[elem]) if(cycle.find(topo[e].from)!=cycle.end()) vars3.push_back(e);
        for(auto e:outs[elem]) if(cycle.find(topo[e].to)!=cycle.end()) vars3.push_back(e);
    }


    uniquefy(vars1);
    uniquefy(vars2);
    uniquefy(vars3);
    problem.addRow(sumExp(vars3),0,cycle.size()-1);
//    problem.addRow(sumExp(vars1),1,10000);
//    problem.addRow(sumExp(vars2),1,10000);

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
    void generateCuts( const OsiSolverInterface & si, OsiCuts & cs,
                       const CglTreeInfo info = CglTreeInfo()){

        int n = (si.getNumCols() - topo.size())/2 ;


        vector<int> p(n,-1);


        const double *colSolution = si.getColSolution();


        for(int i=0;i< topo.size() ;i++) if(fabs(colSolution[i]-1)<1e-8) p[topo[i].from] = topo[i].to;



//        for(int i=0;i< topo.size() ;i++) cout<<colSolution[i]<<" ";
//        cout<<endl;



        auto cycles = checkCycle(p);


        if(!cycles.empty()){
            for(auto cycle:cycles){

                vector<int> vars3;
                for(auto elem:cycle){
                    for(auto e:ins[elem]) if(cycle.find(topo[e].from)!=cycle.end()) vars3.push_back(e);
                    for(auto e:outs[elem]) if(cycle.find(topo[e].to)!=cycle.end()) vars3.push_back(e);
                }

                uniquefy(vars3);

                if(!allTSPCuts[cycle]){
                    allTSPCuts[cycle] = 1;
                    nowCuts.push_back(cycle);
                }
//                OsiRowCut rc;
//
//
//                rc.setRow(sumExp(vars3));
//                rc.setLb(0);
//                rc.setUb(cycle.size()-1);
//                cs.insert(rc);

            }
        }


    }

    TSPCut () {}
    CglCutGenerator * clone() const {

        return new TSPCut();
    }
    inline int getAggressiveness() const
    { return aggressive_;}

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
        return true;
    };

    int maximumLengthOfCutInTree() const
    { return COIN_INT_MAX;}

private:

    int aggressive_;
};





vector<double> getSolution(OsiClpSolverInterface &problem,double limit=0.1){

    cout<<"Solving with Limit:"<<limit<<endl;


    CbcModel model(problem);

    model.setMaximumSeconds(limit);
    model.setMaximumSavedSolutions(10);
    model.addCutGenerator(new TSPCut(),1,NULL,true,true);




    cout<<"Saved:"<<model.numberSavedSolutions()<<endl;

//    model.addCutGenerator(&zeroHalf,-1);
    model.initialSolve();
    model.setPrintFrequency(1);
    model.branchAndBound();




    if(model.isProvenInfeasible() ) return vector<double>();


    const double *solution = model.solver()->getColSolution();
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
    vector<double> solution;
    do {
        solvedTime++;
        solution = getSolution(problem,onetime);
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

