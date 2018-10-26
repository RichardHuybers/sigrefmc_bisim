#include <unistd.h>
#include <sys/time.h>

#include <sylvan.h>
#include <sylvan_int.h>
#include <sylvan_obj.hpp>

#include <bisimulation.hpp>
#include <sigref.h>
#include <sigref_util.hpp>

#include <fstream>

namespace sigref {

using namespace sylvan;
using namespace std;


/**
 * Generates a cube for *bit_string* defined over *vars* 
 */
BDD generate_cube(BDD vars, uint64_t bit_string) {
    if (vars == sylvan_true)
        return sylvan_true;
    if (sylvan_set_count(vars) > 64) {
        printf("\n\nERROR (generate_cube): cannot generate cube with more than 64 variables.\n\n");
        return sylvan_false;
    }

    BDD child = generate_cube(mtbdd_gethigh(vars), bit_string >> 1);

    if (bit_string & 1)
        return mtbdd_makenode(mtbdd_getvar(vars), sylvan_false, child);
    else
        return mtbdd_makenode(mtbdd_getvar(vars), child, sylvan_false);
}


/**
 * Compute the converse relation of T
 */
#define converse(T) CALL(converse, T)
TASK_1(BDD, converse, BDD, T) 
{
    if (sylvan_isconst(T)) return T;

    BDD result;

    if (cache_get3(CACHE_CONVERSE, T, 0, 0, &result)) return result;

    BDD T0 = sylvan_low(T);
    BDD T1 = sylvan_high(T);
    BDD low, aLow, bLow, high, aHigh, bHigh;
    BDDVAR xi = sylvan_var(T);

    sylvan_gc_test();

    if (xi%2 == 1) { // top variable of T is primed
        bdd_refs_spawn(SPAWN(converse, T1));
        low = bdd_refs_push(CALL(converse, T0));
        high = bdd_refs_push(bdd_refs_sync(SYNC(converse)));                                      
        result = sylvan_makenode(xi-1, low, high);
        bdd_refs_pop(2);

    } else if (xi%2 != 0) {
        printf("ERROR (converse): topvar(= %i) is not in x.\n", xi);
    } else if (sylvan_var(T0) != xi+1  && sylvan_var(T1) != xi+1) { // top variables of T0 and T1 are not xi'
        bdd_refs_spawn(SPAWN(converse, T1));
        low = bdd_refs_push(CALL(converse, T0));
        high = bdd_refs_push(bdd_refs_sync(SYNC(converse)));                                      
        result = sylvan_makenode(xi+1, low, high);
        bdd_refs_pop(2);
    } else if (sylvan_var(T0) != xi+1) { // top variable of T0 is not xi'
        bdd_refs_spawn(SPAWN(converse, sylvan_low(T1)));
        aLow = bLow = bdd_refs_push(CALL(converse, T0));
        aHigh = bdd_refs_push(bdd_refs_sync(SYNC(converse))); 
        bHigh = bdd_refs_push(CALL(converse, sylvan_high(T1)));
        low = bdd_refs_push(sylvan_makenode(xi+1, aLow, aHigh));
        high = bdd_refs_push(sylvan_makenode(xi+1, bLow, bHigh));
        result = sylvan_makenode(xi, low, high);
        bdd_refs_pop(5);
    } else if (sylvan_var(T1) != xi+1) { // top variable of T1 is not xi'
        bdd_refs_spawn(SPAWN(converse, sylvan_low(T0)));
        aHigh = bHigh = bdd_refs_push(CALL(converse, T1));
        aLow = bdd_refs_push(bdd_refs_sync(SYNC(converse))); 
        bLow = bdd_refs_push(CALL(converse, sylvan_high(T0)));
        low = bdd_refs_push(sylvan_makenode(xi+1, aLow, aHigh));
        high = bdd_refs_push(sylvan_makenode(xi+1, bLow, bHigh));
        result = sylvan_makenode(xi, low, high);
        bdd_refs_pop(5);
    } else { // top variables of T0 and T1 are xi'
        bdd_refs_spawn(SPAWN(converse, sylvan_low(T1)));
        aLow = bdd_refs_push(CALL(converse, sylvan_low(T0)));
        aHigh = bdd_refs_push(bdd_refs_sync(SYNC(converse)));
        bdd_refs_spawn(SPAWN(converse, sylvan_high(T1)));
        bLow = bdd_refs_push(CALL(converse, sylvan_high(T0)));
        bHigh = bdd_refs_push(bdd_refs_sync(SYNC(converse)));
        low = bdd_refs_push(sylvan_makenode(xi+1, aLow, aHigh));
        high = bdd_refs_push(sylvan_makenode(xi+1, bLow, bHigh));
        result = sylvan_makenode(xi, low, high);
        bdd_refs_pop(6);
    }

    cache_put3(CACHE_CONVERSE, T, 0, 0, result);

    return result;
}


/**
 * Parallel BFS extension
 */
#define parLoop(R, relations, n_relations) CALL(parLoop, R, relations, n_relations)
TASK_3(BDD, parLoop, BDD, R, BDD*, relations, int, n_relations)
{
    if (n_relations == 1) {
        BDD result = bdd_refs_push(sylvan_forall_preimage(R, *relations));
        result = sylvan_relcomp(*relations, result);
        bdd_refs_pop(1); bdd_refs_push(result);
        BDD converse_result = bdd_refs_push(converse(result));
        result = sylvan_or(result, converse_result);
        bdd_refs_pop(2);
        return result;
    } else {
        bdd_refs_spawn(SPAWN(parLoop, R, relations, n_relations/2));
        BDD right = bdd_refs_push(CALL(parLoop, R, relations+(n_relations/2), n_relations-n_relations/2));
        BDD left = bdd_refs_push(bdd_refs_sync(SYNC(parLoop)));
        BDD result = sylvan_or(left, right);
        bdd_refs_pop(2);
        return result;       
    }
}

/*
 * bisim2: Computes the maximal bisimulation of "lts" as a relation using parallel BFS expansion.
 */
TASK_IMPL_1(BDD, min_lts_strong2, LTS&, lts)
{
    // Gather states and actions
    BDD S = lts.getVarS().GetBDD();
    BDD T = lts.getVarT().GetBDD();
    BDD ST = sylvan_and(S,T);  
    BDD A = lts.getVarA().GetBDD();
    BDD states = lts.getStates().GetBDD();
    BDD states_cp = sylvan_and(states, swap_prime(states)); // crossproduct of reachable states
    sylvan_protect(&ST);
    sylvan_protect(&states_cp);

    int state_length = sylvan_set_count(S);
    int action_length = sylvan_set_count(A);

    // Create a cube for every action
    int n_actions = 1 << action_length;
    BDD actions[n_actions];
    for (int i=0; i<n_actions; i++) {
        actions[i] = generate_cube(A, i);
        sylvan_protect(actions+i);
    }

    // Gather and rewrite transition relations
    int n_relations = lts.getTransitions().size();                   
    BDD transition_relations[n_relations];
    BDD transition_variables[n_relations];
    BDD new_transition_relations[n_actions];

    for (int i=0; i<n_actions; i++)
        new_transition_relations[i] = sylvan_false;

    for (int i=0; i<n_relations; i++) {
        transition_relations[i] = lts.getTransitions()[i].first.GetBDD();
        sylvan_protect(transition_relations+i);
        transition_variables[i] = lts.getTransitions()[i].second.GetBDD();
        transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
        for (int j=0; j<n_actions; j++) {
            BDD temp = sylvan_and_exists(transition_relations[i], actions[j], A);  
            new_transition_relations[j] = sylvan_or(new_transition_relations[j], temp);
            sylvan_protect(new_transition_relations+j);
        }        
        sylvan_unprotect(transition_relations+i);
    }
    
    for (int i=0; i<n_actions; i++) 
        sylvan_unprotect(actions+i);

    // Statistics
    long double n_new_transitions = big_satcount(new_transition_relations, n_actions, 2*state_length, mtbdd_true);
    INFO("");
    INFO("Number of states: %'zu.", (size_t)sylvan_satcount(states, S));
    INFO("Number of possible pairs of states: %'zu.", (size_t)sylvan_satcount(states_cp, ST));
    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("Number of transitions: %'0.0Lf.", n_new_transitions);
    if (verbosity >= 2)
        INFO("");
    
    // Compute least fixed point R
    double i1 = wctime();

    BDD R = sylvan_not(states_cp);
    BDD old_R;
    sylvan_protect(&R);
    sylvan_protect(&old_R);
     
    size_t iteration = 1;
    do {
    	old_R = R;

        BDD temp = bdd_refs_push(parLoop(R, new_transition_relations, n_actions));
        R = sylvan_or(R, temp);
        bdd_refs_pop(1);

        INFO("Finished iteration %zu.", iteration++);
        if (verbosity >= 2) {
            INFO("After iteration %zu:\t%'zu inequivalent state pairs found.", iteration++, (size_t)sylvan_satcount(sylvan_and(R, states_cp), ST)); 
            INFO("\t\t\t%'zu nodes in R.",  mtbdd_nodecount(sylvan_not(R)));
        }
    } while (R != old_R); 

    double i2 = wctime();

    INFO("");
    INFO("Number of equivalent state pairs: %'zu", (size_t)sylvan_satcount(sylvan_not(R), ST));

    INFO("");
    INFO("Time for computing the bisimulation relation: %.2f sec.", i2-i1);

    // Unprotect BDDs
	for (int i=0; i<n_actions; i++)
        sylvan_unprotect(new_transition_relations+i);
    sylvan_unprotect(&ST);
    sylvan_unprotect(&states_cp);
    sylvan_unprotect(&R);
	sylvan_unprotect(&old_R);

	return sylvan_not(R);
} 


/*
 * bisim: Computes the maximal bisimulation of "lts" as a relation using sequential chaining expansion.
 */
TASK_IMPL_1(BDD, min_lts_strong3, LTS&, lts)
{
    // Gather states and actions
    BDD S = lts.getVarS().GetBDD();
    BDD T = lts.getVarT().GetBDD();
    BDD ST = sylvan_and(S,T);  
    BDD A = lts.getVarA().GetBDD();
    BDD states = lts.getStates().GetBDD();
    BDD states_cp = sylvan_and(states, swap_prime(states)); // crossproduct of reachable states
    sylvan_protect(&ST);
    sylvan_protect(&states_cp);

    int state_length = sylvan_set_count(S);
    int action_length = sylvan_set_count(A);

    // Create a cube for every action
    int n_actions = 1 << action_length;
    BDD actions[n_actions];
    for (int i=0; i<n_actions; i++) {
        actions[i] = generate_cube(A, i);
        sylvan_protect(actions+i);
    }

    // Gather and rewrite transition relations
    int n_relations = lts.getTransitions().size();                   
    BDD transition_relations[n_relations];
    BDD transition_variables[n_relations];
    BDD new_transition_relations[n_actions];

    for (int i=0; i<n_actions; i++)
        new_transition_relations[i] = sylvan_false;

    for (int i=0; i<n_relations; i++) {
        transition_relations[i] = lts.getTransitions()[i].first.GetBDD();        
        sylvan_protect(transition_relations+i);
        transition_variables[i] = lts.getTransitions()[i].second.GetBDD();
        transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
        for (int j=0; j<n_actions; j++) {
            BDD temp = sylvan_and_exists(transition_relations[i], actions[j], A);  
            new_transition_relations[j] = sylvan_or(new_transition_relations[j], temp);
            sylvan_protect(new_transition_relations+j);
        }        
        sylvan_unprotect(transition_relations+i);
    }
    
    for (int i=0; i<n_actions; i++)
        sylvan_unprotect(actions+i);


    // Statistics
    long double n_new_transitions = big_satcount(new_transition_relations, n_actions, 2*state_length, mtbdd_true);
    INFO("");
    INFO("Number of states: %'zu.", (size_t)sylvan_satcount(states, S));
    INFO("Number of possible pairs of states: %'zu.", (size_t)sylvan_satcount(states_cp, ST));
    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("Number of transitions: %'0.0Lf.", n_new_transitions);
    if (verbosity >= 2)
        INFO("");
    

    // Compute least fixed point R
    double i1 = wctime();

    BDD R = sylvan_not(states_cp);
    BDD old_R;
    sylvan_protect(&R);
    sylvan_protect(&old_R);
     
    size_t iteration = 1;
    do {
        old_R = R;

        for (int i=0; i<n_actions; i++) { // hyperPre(R, Ta) := relcomp(Ta, forallrelprev(R,Ta))
            BDD temp = bdd_refs_push(sylvan_forall_preimage(R, new_transition_relations[i]));    

            temp = sylvan_relcomp(new_transition_relations[i], temp);

            bdd_refs_pop(1); bdd_refs_push(temp);
            BDD conv_temp = bdd_refs_push(converse(temp));
            temp = bdd_refs_push(sylvan_or(temp, conv_temp));

            R = sylvan_or(R, temp);
            
            bdd_refs_pop(3);
        } 

        INFO("Finished iteration %zu.", iteration++);
        if (verbosity >= 2) {
            INFO("After iteration %zu:\t%'zu inequivalent state pairs found.", iteration++, (size_t)sylvan_satcount(sylvan_and(R, states_cp), ST)); 
            INFO("\t\t\t%'zu nodes in R.",  mtbdd_nodecount(sylvan_not(R)));
        }
    } while (R != old_R); 

    double i2 = wctime();

    INFO("");
    INFO("Number of equivalent state pairs: %'zu", (size_t)sylvan_satcount(sylvan_not(R), ST));

    INFO("");
    INFO("Time for computing the bisimulation relation: %.2f sec.", i2-i1);

    // Unprotect BDDs
    for (int i=0; i<n_actions; i++)
        sylvan_unprotect(new_transition_relations+i);
    sylvan_unprotect(&ST);
    sylvan_unprotect(&states_cp);
    sylvan_unprotect(&R);
    sylvan_unprotect(&old_R);
    
    return sylvan_not(R);
}

} // namespace sigref