#include <unistd.h>
#include <sys/time.h>

#include <sylvan.h>
#include <sylvan_int.h>
#include <sylvan_obj.hpp>

#include <bisimulation.hpp>
#include <sigref.h>
#include <sigref_util.hpp>

namespace sigref {

using namespace sylvan;


/**
 * Print F
 * TODO: Remove when finished
 */
#define print_BDD(F, spaces, spaces_limit) CALL(print_BDD, F, spaces, spaces_limit)
VOID_TASK_3(print_BDD, BDD, F, int, spaces, int, spaces_limit)
{
    if (spaces > spaces_limit)
        return;
    for (int i = 0; i < spaces; i++)
        printf(" ");
    if (F == sylvan_true) {
        printf("T\n");
        return;
    }
    if (F == sylvan_false) {
        printf("F\n");
        return;
    }

    printf("%i(%lu) ", mtbdd_getvar(F), F&0x000000ffffffffff);

    BDD low = mtbdd_getlow(F);
    if (low == sylvan_true)
        printf("L: T ");
    else if (low == sylvan_false)
        printf("L: F ");
    else
        printf("L: %i(%lu) ", mtbdd_getvar(low), low&0x000000ffffffffff);

    BDD high = mtbdd_gethigh(F);
    if (high == sylvan_true)
        printf("H: T\n");
    else if (high == sylvan_false)
        printf("H: F\n");
    else
        printf("H: %i(%lu)\n", mtbdd_getvar(high), high&0x000000ffffffffff);

    spaces++;
    if (low != sylvan_true && low != sylvan_false)
        CALL(print_BDD, low, spaces, spaces_limit);
    if (high != sylvan_true && high != sylvan_false)
        CALL(print_BDD, high, spaces, spaces_limit);
    return;
}


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


void swap(BDD bdd_array[], int i, int j) {
    BDD temp = bdd_array[i];
    bdd_array[i] = bdd_array[j];
    bdd_array[j] = temp;
}


int partition(BDD transitions[], int low, int high) {
    int i, j;
    BDDVAR pivot;

    pivot = sylvan_var(transitions[high]);
    i = low-1;
    for (j = low; j < high; j++) {
        if (sylvan_var(transitions[j]) < pivot) {
            i++;
            swap(transitions, i, j);
        }
    }
    swap(transitions, i+1, high);

    return i+1;
}


/**
 * Sort transition relations by top variable in descending order
 */
void sort_transitions(BDD transitions[], int low, int high) {
    int p;

    if (low < high) {
        p = partition(transitions, low, high);
        sort_transitions(transitions, low, p-1);
        sort_transitions(transitions, p+1, high);
    }

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
        low = sylvan_makenode(xi+1, aLow, aHigh);
        high = sylvan_makenode(xi+1, bLow, bHigh);
        result = sylvan_makenode(xi, low, high);
        bdd_refs_pop(3);
    } else if (sylvan_var(T1) != xi+1) { // top variable of T1 is not xi'
        bdd_refs_spawn(SPAWN(converse, sylvan_low(T0)));
        aHigh = bHigh = bdd_refs_push(CALL(converse, T1));
        aLow = bdd_refs_push(bdd_refs_sync(SYNC(converse))); 
        bLow = bdd_refs_push(CALL(converse, sylvan_high(T0)));
        low = sylvan_makenode(xi+1, aLow, aHigh);
        high = sylvan_makenode(xi+1, bLow, bHigh);
        result = sylvan_makenode(xi, low, high);
        bdd_refs_pop(3);
    } else { // top variables of T0 and T1 are xi'
        bdd_refs_spawn(SPAWN(converse, sylvan_low(T1)));
        aLow = bdd_refs_push(CALL(converse, sylvan_low(T0)));
        aHigh = bdd_refs_push(bdd_refs_sync(SYNC(converse)));
        bdd_refs_spawn(SPAWN(converse, sylvan_high(T1)));
        bLow = bdd_refs_push(CALL(converse, sylvan_high(T0)));
        bHigh = bdd_refs_push(bdd_refs_sync(SYNC(converse)));
        low = sylvan_makenode(xi+1, aLow, aHigh);
        high = sylvan_makenode(xi+1, bLow, bHigh);
        result = sylvan_makenode(xi, low, high);
        bdd_refs_pop(4);
    }

    cache_put3(CACHE_CONVERSE, T, 0, 0, result);

    return result;
}


/**
 * Computes the hyper preimage of R
 */
#define hyper_preimage(R, relations, n_relations) CALL(hyper_preimage, R, relations, n_relations)
TASK_3(BDD, hyper_preimage, BDD, R, BDD*, relations, int, n_relations)
{
    if (n_relations == 1) {
        BDD result = bdd_refs_push(sylvan_forall_preimage(R, *relations));
        result = sylvan_relcomp(*relations, result);
        bdd_refs_pop(1);
        return result;
    } else {
        bdd_refs_spawn(SPAWN(hyper_preimage, R, relations, n_relations/2));
        BDD right = bdd_refs_push(CALL(hyper_preimage, R, relations+(n_relations/2), n_relations-n_relations/2));
        BDD left = bdd_refs_push(bdd_refs_sync(SYNC(hyper_preimage)));
        BDD result = sylvan_or(left, right);
        bdd_refs_pop(2);
        return result;       
    }
}


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
    int n_actions = 1 << action_length; // WARNING: wrong if A skips levels
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
        transition_relations[i] = sylvan_and(transition_relations[i], states_cp);
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

    //BDD R = sylvan_false;
    BDD R = sylvan_not(states_cp);
    BDD old_R;
    sylvan_protect(&R);
    sylvan_protect(&old_R);
    
    
    size_t iteration = 1;
    do {
    	old_R = R;
        
        for (int i=0; i<n_actions; i++) { // hyperPre(R, Ta) := relcomp(Ta, forallrelprev(R,Ta))
            BDD temp = bdd_refs_push(sylvan_forall_preimage(R, new_transition_relations[i]));
            temp = bdd_refs_push(sylvan_relcomp(new_transition_relations[i], temp));
            temp = bdd_refs_push(sylvan_or(temp, converse(temp)));
    		R = sylvan_or(R, temp);
    		bdd_refs_pop(3);
    	} 

        //R = hyper_preimage(R, new_transition_relations, n_actions);
        INFO("Finished iteration %zu.", iteration++);
        if (verbosity >= 2) {
            INFO("After iteration %zu:\t%'zu inequivalent state pairs found.", iteration++, (size_t)sylvan_satcount(sylvan_and(R, states_cp), ST)); 
            INFO("\t\t\t%'zu nodes in R.",  mtbdd_nodecount(sylvan_not(R)));
        }
    } while (R != old_R); 

    //BDD not_R = sylvan_and(sylvan_not(R), states_cp);

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


#define bisim(R, T, n_actions, level) CALL (bisim, R, T, n_actions, level)
TASK_4(BDD, bisim, BDD, R, BDD *, T, int, n_actions, BDDVAR, level) 
{
    BDD low, high, result, old_result;
 
    if (n_actions == 0 || R == sylvan_true) 
        return R;

    if (cache_get4(CACHE_BISIM, R, 0, 0, level, &result)) 
        return result;

    result = R;

    if (result != sylvan_false) {
        if (level == sylvan_var(result)) {
            low = bisim(sylvan_low(result), T, n_actions, level+1);
            high = bisim(sylvan_high(result), T, n_actions, level+1);
            result = mtbdd_makenode(level, low, high);
        }
        else
            result = bisim(result, T, n_actions, level+1);
    }

    do {
        old_result = result;

        int i = 0;
        while (i < n_actions && sylvan_var(T[i]) == level) { 
            BDD temp = sylvan_forall_preimage(result, T[i]);
            temp = sylvan_relcomp(T[i], temp);
            temp = sylvan_or(temp, converse(temp));
            result = sylvan_or(result, temp);

            temp = sylvan_false; // For gc
            i++;
        }


        if (result != old_result) { // Saturate deeper
            if (level == sylvan_var(result)) {
                low = bisim(sylvan_low(result), T+i, n_actions-i, level+1);
                high = bisim(sylvan_high(result), T+i, n_actions-i, level+1);
                result = mtbdd_makenode(level, low, high);
            }
            else
                result = bisim(result, T+i, n_actions-i, level+1);
        }
    } while (result != old_result);
    
    cache_put4(CACHE_BISIM, R, 0, 0, level, result);

    return result;
}


#define bisim2(R, T, idx, n_actions) CALL (bisim2, R, T, idx, n_actions)
TASK_4(BDD, bisim2, BDD, R, BDD *, T, int, idx, int, n_actions) 
{
    /* Terminal cases */
    if (R == sylvan_true) return sylvan_true;
    if (idx == n_actions) return R;

    /* Consult the cache */
    BDD result;
    const BDD _R = R;
    if (cache_get3(270LL<<42, _R, idx, 0, &result)) return result;
    mtbdd_refs_push(_R);

    /* Check if the relation should be applied */
    const uint32_t var = sylvan_var(T[idx]);
    if (R == sylvan_false || var <= sylvan_var(R)) {
        /* Count the number of relations starting here */
        int count = idx+1;
        while (count < n_actions && var == sylvan_var(T[count])) count++;
        /*
         * Compute until fixpoint:
         * - SAT deeper
         * - chain-apply all current level once
         */
        BDD prev = sylvan_false;
        BDD temp = sylvan_false;
        mtbdd_refs_push(R);
        mtbdd_refs_push(prev);
        mtbdd_refs_push(temp);
        do {
            prev = R;
            // SAT deeper
            R = CALL(bisim2, R, T, count, n_actions);
            // chain-apply all current level once
            for (int i=idx;i<count;i++) {
                temp = sylvan_forall_preimage(R, T[i]);
                temp = sylvan_relcomp(T[i], temp);
                temp = sylvan_or(temp, converse(temp));
                R = sylvan_or(R, temp);

                temp = sylvan_false; // unset, for gc
            }
        } while (prev != R);
        mtbdd_refs_pop(3);
        result = R;
    } else {
        /* Recursive computation */
        mtbdd_refs_spawn(SPAWN(bisim2, sylvan_low(R), T, idx, n_actions));
        BDD high = mtbdd_refs_push(CALL(bisim2, sylvan_high(R), T, idx, n_actions));
        BDD low = mtbdd_refs_sync(SYNC(bisim2));
        mtbdd_refs_pop(1);
        result = sylvan_makenode(sylvan_var(R), low, high);
    }

    /* Store in cache */
    cache_put3(270LL<<42, _R, idx, 0, result);
    mtbdd_refs_pop(1);
    return result;
}


// With saturation
TASK_IMPL_1(BDD, min_lts_strong3, LTS&, lts)
{
    /* Gather states and actions */
    BDD S = lts.getVarS().GetBDD();
    BDD T = lts.getVarT().GetBDD();
    BDD ST = sylvan_and(S,T);  
    BDD A = lts.getVarA().GetBDD();
    BDD states = lts.getStates().GetBDD();
    BDD states_cp = sylvan_and(states, swap_prime(states)); /* Crossproduct of reachable states */
    sylvan_protect(&ST);
    sylvan_protect(&states_cp);

    int state_length = sylvan_set_count(S);
    int action_length = sylvan_set_count(A);

    /* Create a BDD for every action */
    int n_actions = 1 << action_length;
    BDD actions[n_actions];
    for (int i=0; i<n_actions; i++) {
        actions[i] = generate_cube(A, i);
        sylvan_protect(actions+i);
    }

    /* Gather transition relations */
    int n_relations = lts.getTransitions().size();                   
    BDD transition_relations[n_relations];
    BDD transition_variables[n_relations];
    BDD new_transition_relations[n_actions];
    BDDVAR topvars[n_actions];

    for (int i=0; i<n_actions; i++) {
        new_transition_relations[i] = sylvan_false;
        sylvan_protect(new_transition_relations+i);
        topvars[i] = 1000000;
    }

    int k = 0;

    for (int i=0; i<n_relations; i++) {
        /* Get transition relation */
        transition_relations[i] = lts.getTransitions()[i].first.GetBDD();
        transition_variables[i] = lts.getTransitions()[i].second.GetBDD();
        sylvan_protect(transition_relations+i);
        sylvan_protect(transition_variables+i);
        /* Extend to full domain */
        transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
        /* Remove unreachable/impossible transitions */
        transition_relations[i] = sylvan_and(transition_relations[i], states_cp);
        /* Split transition relation on actions */
        for (int j=0; j<n_actions; j++) {
            BDD temp = sylvan_and_exists(transition_relations[i], actions[j], A);  
            if (temp != sylvan_false && sylvan_var(transition_variables[i]) < topvars[j])
                topvars[j] = sylvan_var(transition_variables[i]);
            new_transition_relations[j] = sylvan_or(new_transition_relations[j], temp);
        }        
        sylvan_unprotect(transition_relations+i);
        sylvan_unprotect(transition_variables+i);
    }

    for (int i=0; i<n_actions; i++) 
        sylvan_unprotect(actions+i);

    INFO("transition_relations[3] (topvar[3] = %u) before", topvars[3]);
    print_BDD(new_transition_relations[3], 0, 4);

    /* Remove "identity prefix" from transition relations */
    for (int i=0; i<n_actions; i++) {
        while (!sylvan_isconst(new_transition_relations[i]) && sylvan_var(new_transition_relations[i]) != topvars[i]) {
            if (!sylvan_isconst(sylvan_low(new_transition_relations[i])))
                new_transition_relations[i] = sylvan_low(new_transition_relations[i]);
            else
                new_transition_relations[i] = sylvan_high(new_transition_relations[i]);
        }
    } 

    INFO("transition_relations[3] (topvar[3] = %u) after", topvars[3]);
    print_BDD(new_transition_relations[3], 0, 4);
    
    /* Sort transition relations on top variable in ascending order (highest variables first) */
    sort_transitions(new_transition_relations, 0, n_actions-1); 

    /* Statistics */
    INFO("");
    INFO("Number of states: %'zu.", (size_t)sylvan_satcount(states, S));
    INFO("Number of possible pairs of states: %'zu.", (size_t)sylvan_satcount(states_cp, ST));
    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("");
        
    /* Compute all inequivalent pairs of states */
//    double i1 = wctime();

    BDD R1 = sylvan_not(states_cp);
    sylvan_protect(&R1);
    R1 = bisim(R1, new_transition_relations, n_actions, 0);
    INFO("Number of equivalent state pairs according to method 1: %'zu", (size_t)sylvan_satcount(sylvan_not(R1), ST));
    sylvan_unprotect(&R1);
    
    BDD R2 = sylvan_not(states_cp);
    sylvan_protect(&R2); 
    R2 = bisim2(R2, new_transition_relations, 0, n_actions);
    INFO("Number of equivalent state pairs according to method 2: %'zu", (size_t)sylvan_satcount(sylvan_not(R2), ST));

//   double i2 = wctime(); 

//    INFO("");
//    INFO("Time for computing the bisimulation relation: %.2f sec.", i2-i1);

    // Unprotect BDDs
    for (int i=0; i<n_actions; i++)
        sylvan_unprotect(new_transition_relations+i);
    sylvan_unprotect(&ST);
    sylvan_unprotect(&states_cp);

    sylvan_unprotect(&R2);

    return sylvan_not(R1);
} 

/*
// With saturation
TASK_IMPL_1(BDD, min_lts_strong3, LTS&, lts)
{
    LTS L = lts;
    

    // Gather states and actions
    BDD S, T;
    S = T = sylvan_true;
    for (int i = 2; i >= 0; i--) {
        S = sylvan_makenode(i*2, sylvan_false, S);
        T = sylvan_makenode(i*2+1, sylvan_false, T);   
    }
    BDD ST = sylvan_and(S,T); 
    BDD A = sylvan_makenode(1000001, sylvan_false, sylvan_true);
    A = sylvan_makenode(1000000, sylvan_false, A);

    BDD states = sylvan_false;
    BDD _t;
    // 000
    _t = sylvan_true;
    _t = sylvan_makenode(4, _t, sylvan_false);
    _t = sylvan_makenode(2, _t, sylvan_false);
    _t = sylvan_makenode(0, _t, sylvan_false);
    states = sylvan_or(states, _t);
    // 001
    _t = sylvan_true;
    _t = sylvan_makenode(4, sylvan_false, _t);
    _t = sylvan_makenode(2, _t, sylvan_false);
    _t = sylvan_makenode(0, _t, sylvan_false);
    states = sylvan_or(states, _t);
    // 010
    _t = sylvan_true;
    _t = sylvan_makenode(4, _t, sylvan_false);
    _t = sylvan_makenode(2, sylvan_false, _t);
    _t = sylvan_makenode(0, _t, sylvan_false);
    states = sylvan_or(states, _t);
    // 011
    _t = sylvan_true;
    _t = sylvan_makenode(4, sylvan_false, _t);
    _t = sylvan_makenode(2, sylvan_false, _t);
    _t = sylvan_makenode(0, _t, sylvan_false);
    states = sylvan_or(states, _t);
    // 111
    _t = sylvan_true;
    _t = sylvan_makenode(4, sylvan_false, _t);
    _t = sylvan_makenode(2, sylvan_false, _t);
    _t = sylvan_makenode(0, sylvan_false, _t);
    states = sylvan_or(states, _t);

    BDD states_cp = sylvan_and(states, swap_prime(states)); // crossproduct of reachable states
    sylvan_protect(&ST);
    sylvan_protect(&states_cp);

    int state_length = sylvan_set_count(S);
    int action_length = sylvan_set_count(A);

    // Create a cube for every action
    int n_actions = 1 << action_length;
    INFO("n_actions = %d", n_actions);
    BDD actions[n_actions];
    for (int i=0; i<n_actions; i++) {
        actions[i] = generate_cube(A, i);
        sylvan_protect(actions+i);
    }
    
    // Gather and rewrite transition relations
    int n_relations = 2;
    BDD transition_relations[n_relations];
    BDD transition_variables[n_relations];
    transition_relations[0] = sylvan_makenode(1000001, sylvan_true, sylvan_false);
    transition_relations[0] = sylvan_makenode(1000000, transition_relations[0], sylvan_false);
    transition_relations[0] = sylvan_makenode(3, sylvan_false, transition_relations[0]);
    transition_relations[0] = sylvan_makenode(2, transition_relations[0], sylvan_false);

    transition_variables[0] = sylvan_makenode(3, sylvan_false, sylvan_true);
    transition_variables[0] = sylvan_makenode(2, sylvan_false, transition_variables[0]);


    transition_relations[1] = sylvan_makenode(1000001, sylvan_false, sylvan_true);
    transition_relations[1] = sylvan_makenode(1000000, transition_relations[1], sylvan_false);
    transition_relations[1] = sylvan_makenode(5, sylvan_false, transition_relations[1]);
    transition_relations[1] = sylvan_makenode(3, sylvan_false, transition_relations[1]);
    transition_relations[1] = sylvan_makenode(2, sylvan_false, transition_relations[1]);
    transition_relations[1] = sylvan_makenode(1, sylvan_false, transition_relations[1]);
    transition_relations[1] = sylvan_makenode(0, transition_relations[1], sylvan_false);

    transition_variables[1] = sylvan_makenode(5, sylvan_false, sylvan_true);
    transition_variables[1] = sylvan_makenode(3, sylvan_false, transition_variables[1]);
    transition_variables[1] = sylvan_makenode(2, sylvan_false, transition_variables[1]);
    transition_variables[1] = sylvan_makenode(1, sylvan_false, transition_variables[1]);
    transition_variables[1] = sylvan_makenode(0, sylvan_false, transition_variables[1]);
    

    BDD new_transition_relations[n_actions];
    BDDVAR topvars[n_actions];

    for (int i=0; i<n_actions; i++) {
        new_transition_relations[i] = sylvan_false;
        topvars[i] = 1000000;
    }
    //TODO: Check for cases T = true
    for (int i=0; i<n_relations; i++) {
        sylvan_protect(transition_relations+i);
        sylvan_protect(transition_variables+i);
        transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
        transition_relations[i] = sylvan_and(transition_relations[i], states_cp);
        for (int j=0; j<n_actions; j++) {
            BDD temp = sylvan_and_exists(transition_relations[i], actions[j], A);
            if (!sylvan_isconst(temp) && sylvan_var(transition_variables[i]) < topvars[j])
                topvars[j] = sylvan_var(transition_variables[i]);
            new_transition_relations[j] = sylvan_or(new_transition_relations[j], temp);
            sylvan_protect(new_transition_relations+j);
        }        
        sylvan_unprotect(transition_relations+i);
        sylvan_unprotect(transition_variables+i);
    }
    for (int i=0; i<n_actions; i++) 
        sylvan_unprotect(actions+i); 

    for (int i=0; i<n_actions; i++) {
        while (!sylvan_isconst(new_transition_relations[i]) && sylvan_var(new_transition_relations[i]) != topvars[i]) {
            if (!sylvan_isconst(sylvan_low(new_transition_relations[i])))
                new_transition_relations[i] = sylvan_low(new_transition_relations[i]);
            else 
                new_transition_relations[i] = sylvan_high(new_transition_relations[i]);
        }
    } 

    sort_transitions(new_transition_relations, 0, n_actions-1); 

    INFO("Transitions after sorting");
    INFO("T0:");
    print_BDD(new_transition_relations[0],0,10);
    INFO("");
    INFO("T1:");
    print_BDD(new_transition_relations[1],0,10);
    INFO("T2:");
    print_BDD(new_transition_relations[2],0,10);
    INFO("");
    INFO("T3:");
    print_BDD(new_transition_relations[3],0,10);
    INFO(""); 

    
    
    // Statistics
    INFO("");
    INFO("Number of states: %'zu.", (size_t)sylvan_satcount(states, S));
    INFO("Number of possible pairs of states: %'zu.", (size_t)sylvan_satcount(states_cp, ST));
    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
        
    // Compute least fixed point R
    double i1 = wctime();

    BDD R = sylvan_not(states_cp);
    
    if (R != converse(R))
        INFO("WARNING: R != converse(R) at start of algorithm.");

    sylvan_protect(&R);
    R = bisim(R, new_transition_relations, n_actions, 0, 2*state_length-1);
    

    if (R != converse(R))
        INFO("WARNING: R != converse(R) at end of algorithm.");

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

    return sylvan_not(R);
} */

} // namespace sigref