//
// Created by meow on 16-3-28.
//

#ifndef FUTURE_NET_TSPCUT_HPP
#define FUTURE_NET_TSPCUT_HPP

#endif //FUTURE_NET_TSPCUT_HPP

#include "CglCutGenerator.hpp"


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



    }

    TSPCut ();

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

    virtual int maximumLengthOfCutInTree() const
    { return COIN_INT_MAX;}

 private:

    int aggressive_;
};