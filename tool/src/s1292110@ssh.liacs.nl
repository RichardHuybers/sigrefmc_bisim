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

double MAX_SIZE = 0;


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


void swap(BDD a[], int i, int j) {
    BDD temp = a[i];
    a[i] = a[j];
    a[j] = temp;
}

void swap(BDDVAR a[], int i, int j) {
    BDD temp = a[i];
    a[i] = a[j];
    a[j] = temp;
}


int partition(BDD transitions[], BDDVAR top_variables[], int low, int high) {
    int i, j; 
    BDDVAR pivot;

    pivot = top_variables[high];
    i = low-1;
    for (j = low; j < high; j++) {
        if (top_variables[j] < pivot) {
            i++;
            swap(transitions, i, j);
            swap(top_variables, i, j);
        }
    }
    swap(transitions, i+1, high);
    swap(top_variables, i+1, high);

    return i+1;
}


/**
 * Sort transition relations by top variable in descending order
 */
void sort_transitions(BDD transitions[], BDDVAR top_variables[], int low, int high) {
    int p;

    if (low < high) {
        p = partition(transitions, top_variables, low, high);
        sort_transitions(transitions, top_variables, low, p-1);
        sort_transitions(transitions, top_variables, p+1, high);
    }

}


/**
 * Extend relation to domain vars2
 */
#define extend_relation2(relation, vars1, vars2, state_length) CALL(extend_relation2, relation, vars1, vars2, state_length)
TASK_4(BDD, extend_relation2, BDD, relation, BDD, vars1, BDD, vars2, int, state_length) {
    /* first determine which state BDD variables are in rel */
    int has[state_length];
    for (int i=0; i<state_length; i++) has[i] = 1;
    BDDSET s = vars2;
    while (s != sylvan_true) {
        BDDVAR v = sylvan_var(s);
        if (v/2 >= (unsigned)state_length) break; // action labels
        has[v/2] = 0;
        s = sylvan_high(s);
    }
    s = vars1;
    while (s != sylvan_true) {
        BDDVAR v = sylvan_var(s);
        if (v/2 >= (unsigned)state_length) break; // action labels
        has[v/2] = 1;
        s = sylvan_high(s);
    }


    /* create "s=s'" for all variables not in rel */
    BDD eq = sylvan_true;
    for (int i=state_length-1; i>=0; i--) {
        if (has[i]) continue;
        BDD low = sylvan_makenode(2*i+1, eq, sylvan_false);
        bdd_refs_push(low);
        BDD high = sylvan_makenode(2*i+1, sylvan_false, eq);
        bdd_refs_pop(1);
        eq = sylvan_makenode(2*i, low, high);
    }

    bdd_refs_push(eq);
    BDD result = sylvan_and(relation, eq);
    bdd_refs_pop(1);

    return result;
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
 * Computes the hyper preimage of R
 */
#define hyper_preimage(R, relations, n_relations) CALL(hyper_preimage, R, relations, n_relations)
TASK_3(BDD, hyper_preimage, BDD, R, BDD*, relations, int, n_relations)
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
        
        // for (int i=0; i<n_actions; i++) { // hyperPre(R, Ta) := relcomp(Ta, forallrelprev(R,Ta))
        //     BDD temp = bdd_refs_push(sylvan_forall_preimage(R, new_transition_relations[i]));
        //     temp = bdd_refs_push(sylvan_relcomp(new_transition_relations[i], temp));
        //     temp = bdd_refs_push(sylvan_or(temp, converse(temp)));
        //     R = sylvan_or(R, temp);
        //     bdd_refs_pop(3);
        // } 

        BDD temp = bdd_refs_push(hyper_preimage(R, new_transition_relations, n_actions));
        R = sylvan_or(R, temp);
        bdd_refs_pop(1);

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

        //BDD temp = bdd_refs_push(hyper_preimage(R, new_transition_relations, n_actions));
        //R = sylvan_or(R, temp);
        //bdd_refs_pop(1);

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


// #define bisim(R, T, n_actions, level, depth) CALL (bisim, R, T, n_actions, level, depth)
// TASK_5(BDD, bisim, BDD, R, BDD *, T, int, n_actions, BDDVAR, level, unsigned int, depth) 
// {
//     BDD low, high, result, old_result;
 
//     if (n_actions == 0 || R == sylvan_true || level == depth+1) 
//         return R;

//     if (cache_get4(CACHE_BISIM, R, 0, 0, level, &result)) 
//         return result;

//     result = R;

//     if (level == sylvan_var(result) && result != sylvan_false) {
//         low = bisim(sylvan_low(result), T, n_actions, level+1, depth);
//         high = bisim(sylvan_high(result), T, n_actions, level+1, depth);
//         result = mtbdd_makenode(level, low, high);
//     }
//     else
//         result = bisim(result, T, n_actions, level+1, depth);

//     do {
//         old_result = result;

//         for (int i = 0; i < n_actions && sylvan_var(T[i]) == level; i++) { 
//             BDD temp = sylvan_forall_preimage(result, T[i]);
//             temp = sylvan_relcomp(T[i], temp);
//             temp = sylvan_or(temp, converse(temp));
//             result = sylvan_or(result, temp);

//             if (result != old_result) { // Saturate deeper
//                 if (level == sylvan_var(result)) {
//                     low = bisim(sylvan_low(result), T+i, n_actions-i, level+1, depth);
//                     high = bisim(sylvan_high(result), T+i, n_actions-i, level+1, depth);
//                     result = mtbdd_makenode(level, low, high);
//                 }
//                 else
//                     result = bisim(result, T+i, n_actions-i, level+1, depth);
//             }
//         }
//     } while (result != old_result);
    
//     cache_put4(CACHE_BISIM, R, 0, 0, level, result);

//     return result;
// }



// #define bisim2(R, T, top_vars, idx, n_actions) CALL (bisim2, R, T, top_vars, idx, n_actions)
// TASK_5(BDD, bisim2, BDD, R, BDD *, T, BDDVAR *, top_vars, int, idx, int, n_actions) 
// {
//     /* Terminal cases */
//     if (R == sylvan_true) return sylvan_true;
//     if (idx == n_actions) return R;

//     /* Consult the cache */
//     BDD result;
//     const BDD _R = R;
//     if (cache_get3(270LL<<42, _R, idx, 0, &result)) return result;  
    
//     sylvan_gc_test();

//     mtbdd_refs_push(_R);

//     /* Check if the relation should be applied */
//     const uint32_t var = top_vars[idx];
//     if (R == sylvan_false || var <= sylvan_var(R)) {
//         /* Count the number of relations starting here */
//         int count = idx+1;
//         while (count < n_actions && var == top_vars[count]) count++;
//         /*
//          * Compute until fixpoint:
//          * - SAT deeper
//          * - chain-apply all current level once
//          */
//         BDD prev = sylvan_false;
//         BDD temp = sylvan_false;
//         mtbdd_refs_push(R);
//         mtbdd_refs_push(prev);
//         mtbdd_refs_push(temp);
//         do {
//             prev = R;
//             // SAT deeper
//             R = CALL(bisim2, R, T, top_vars, count, n_actions);

//             // chain-apply all current level once
//             for (int i=idx;i<count;i++) {
//                 temp = sylvan_forall_preimage(R, T[i]);
//                 temp = sylvan_relcomp(T[i], temp);
//                 temp = sylvan_or(temp, converse(temp));
//                 R = sylvan_or(R, temp);

//                 temp = sylvan_false; // unset, for gc
//             }
//         } while (prev != R);
//         mtbdd_refs_pop(3);
//         result = R;
//     } else {
//         /* Recursive computation */
//         mtbdd_refs_spawn(SPAWN(bisim2, sylvan_low(R), T, top_vars, idx, n_actions));
//         BDD high = mtbdd_refs_push(CALL(bisim2, sylvan_high(R), T, top_vars, idx, n_actions));
//         BDD low = mtbdd_refs_sync(SYNC(bisim2));
//         mtbdd_refs_pop(1);
//         result = sylvan_makenode(sylvan_var(R), low, high);
//     }

//     /* Store in cache */
//     cache_put3(270LL<<42, _R, idx, 0, result);
//     mtbdd_refs_pop(1);

//     int n_nodes = mtbdd_nodecount(R);
//     if (n_nodes > MAX_SIZE)
//         MAX_SIZE = n_nodes; 

//     return result;
// }


// // With saturation
// TASK_IMPL_1(BDD, min_lts_strong3, LTS&, lts)
// {
//     /* Gather states and actions */
//     BDD S = lts.getVarS().GetBDD();
//     BDD T = lts.getVarT().GetBDD();
//     BDD ST = sylvan_and(S,T);  
//     BDD A = lts.getVarA().GetBDD();
//     BDD states = lts.getStates().GetBDD();
//     BDD states_cp = sylvan_and(states, swap_prime(states)); /* Crossproduct of reachable states */
//     sylvan_protect(&ST);
//     sylvan_protect(&states_cp);

//     int state_length = sylvan_set_count(S);
//     int action_length = sylvan_set_count(A);

//     /* Create a BDD for every action */
//     int n_actions = 1 << action_length;
//     BDD actions[n_actions];
//     for (int i=0; i<n_actions; i++) {
//         actions[i] = generate_cube(A, i);
//         sylvan_protect(actions+i);
//     }

//     /* Gather transition relations */
//     int n_relations = lts.getTransitions().size();
//     BDD transition_relations[n_relations];
//     BDD transition_variables[n_relations];
    
//     BDD new_transition_relations[n_actions];
//     BDDVAR top_variables[n_actions];
//     for (int i = 0; i < n_actions; i++) {
//         new_transition_relations[i] = sylvan_false;
//         sylvan_protect(new_transition_relations+i);
//         top_variables[i] = 2*state_length;
//     }

//     for (int i = 0; i < n_relations; i++) {
//         transition_relations[i] = lts.getTransitions()[i].first.GetBDD();
//         transition_variables[i] = lts.getTransitions()[i].second.GetBDD();
//         transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
//         for (int j = 0; j < n_actions; j++) {
//             BDD split = sylvan_and_exists(transition_relations[i], actions[j], A); 
//             if (split != sylvan_false) {
//                 new_transition_relations[j] = sylvan_or(new_transition_relations[j], split);
//                 if (sylvan_var(transition_variables[i]) < top_variables[j])
//                     top_variables[j] = sylvan_var(transition_variables[i]);
//             }
//         } 
//     }

//     /* Remove identity prefix */
//     for (int i = 0; i < n_actions; i++) {
//         BDDSET V = sylvan_true;
//         for (int j = top_variables[i]-1; j >= 0; j--)
//             V = sylvan_makenode(j, sylvan_false, V);
//         new_transition_relations[i] = sylvan_exists(new_transition_relations[i], V);
//     }
  
//     /* Sort transition relations on top variable (highest variables first) */
//     sort_transitions(new_transition_relations, top_variables, 0, n_actions-1);   

//     /* Remove empty transition relations */
//     for (int i = n_actions-1; (signed)top_variables[i] == 2*state_length; i--) {
//         sylvan_unprotect(new_transition_relations+i);
//         n_actions--;
//     }

//     printf("top_variables: ");
//     for (int i = 0; i < n_actions; i++) 
//         printf("%u ", top_variables[i]);
//     printf("\n");

//     /* Count transitions */
//     long int n_transitions = 0;
//     for (int i = 0; i < n_actions; i++) {
//         BDD I = sylvan_true;
//         for (int j = top_variables[i]/2-1; j >= 0; j--) {
//             BDD low = sylvan_makenode(2*j+1, I, sylvan_false);
//             bdd_refs_push(low);
//             BDD high = sylvan_makenode(2*j+1, sylvan_false, I);
//             bdd_refs_pop(1);
//             I = sylvan_makenode(2*j, low, high);
//         }

//         BDD temp = sylvan_and(I, new_transition_relations[i]);
//         n_transitions += sylvan_satcount(temp, ST);
//     }

//     /* Statistics */
//     INFO("");
//     INFO("Number of states: %'zu.", (size_t)sylvan_satcount(states, S));
//     INFO("Number of possible pairs of states: %'zu.", (size_t)sylvan_satcount(states_cp, ST));
//     INFO("Number of state variables: %d.", state_length);
//     INFO("Number of action variables: %d.", action_length);
//     INFO("Number of transitions: %'ld.", n_transitions)
//     INFO("");
        
//     /* Compute all inequivalent pairs of states */
//     double i1 = wctime();
    
//     BDD R = sylvan_not(states_cp);
//     MAX_SIZE = mtbdd_nodecount(R);
//     INFO("Number of nodes in initial result BDD: %'f", MAX_SIZE);
//     sylvan_protect(&R); 
//     R = bisim2(R, new_transition_relations, top_variables, 0, n_actions);
    
//     if (R != converse(R)) {
//         R = sylvan_or(R, converse(R));
//         INFO("WARNING: R is not symmetrical!");
//     }
//     INFO("Maximum size of intermediate result BDD: %'f", MAX_SIZE);
//     INFO("Number of nodes in final result BDD: %'zu", mtbdd_nodecount(sylvan_not(R)));
//     INFO("Number of equivalent state pairs according to sylvan_not(R): %'zu", (size_t)sylvan_satcount(sylvan_not(R), ST));
//     sylvan_unprotect(&R);

//     double i2 = wctime();   

//     INFO("");
//     INFO("Time for computing the bisimulation relation: %.2f sec.", i2-i1);

//     // Unprotect BDDs
//     for (int i=0; i<n_actions; i++)
//         sylvan_unprotect(new_transition_relations+i);
//     sylvan_unprotect(&ST);
//     sylvan_unprotect(&states_cp);

//     return sylvan_not(R);
// } 

} // namespace sigref