/*
 * Copyright 2015 Formal Methods and Tools, University of Twente
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <assert.h>
#include <stdio.h>
#include <sys/mman.h> // for mmap, munmap, etc

#include <sylvan_int.h>

#include <sigref.h>
#include <blocks.h>
#include <refine.h>

/**
 * Signatures records the signature of each block.
 * The default and maximum size of this array is "signatures_size", 1LL<<25
 * In practice, we will run out of memory and time way before this.
 */

#define SL_DEPTH 5
typedef struct
{
    BDD sig;
    uint32_t prev;
    uint32_t next[SL_DEPTH];
} signature_elem;

static signature_elem *signatures = NULL;
static size_t signatures_size = 0;
static uint32_t next_block = 1;
static size_t refine_iteration = 0;

void
prepare_refine()
{
    if (signatures != NULL) {
        munmap(signatures, sizeof(signature_elem)*signatures_size);
    }
    signatures = (signature_elem*)mmap(0, sizeof(signature_elem)*signatures_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, 0, 0);
    if (signatures == (signature_elem*)-1) {
        fprintf(stderr, "sigref: Unable to allocate memory (%'zu bytes) for the signatures!\n", signatures_size*sizeof(signature_elem));
        exit(1);
    }
    refine_iteration++;
}

TASK_2(BDD, assign_block, BDD, sig, BDD, previous_block)
{
    assert(previous_block != mtbdd_false); // if so, incorrect call!

    // maybe do garbage collection
    sylvan_gc_test();

    if (sig == sylvan_false) {
        // slightly different handling because sylvan_false == 0
        sig = (uint64_t)-1;
    }

    // try to claim previous block number
    const uint64_t p_b = CALL(decode_block, previous_block);
    assert(p_b != 0);

    for (;;) {
        BDD cur = *(volatile BDD*)&signatures[p_b].sig;
        if (cur == sig) return previous_block;
        if (cur != 0) break;
        if (cas(&signatures[p_b].sig, 0, sig)) return previous_block;
    }

    /* claim unsuccesful, find newly added */
    uint32_t trace[SL_DEPTH];
    uint32_t loc = 0, loc_next = 0, k = SL_DEPTH-1;
    for (;;) {
        /* invariant: [loc].sig < sig */
        /* note: this is always true for loc==0 */
        signature_elem *e = &signatures[loc];
        loc_next = (*(volatile uint32_t*)&e->next[k]) & 0x7fffffff;
        if (loc_next != 0 && signatures[loc_next].sig == sig && signatures[loc_next].prev == p_b) {
            /* found */
            return CALL(encode_block, loc_next);
        } else if (loc_next != 0 && signatures[loc_next].sig == sig && signatures[loc_next].prev < p_b) {
            /* go right */
            loc = loc_next;
        } else if (loc_next != 0 && signatures[loc_next].sig < sig) {
            /* go right */
            loc = loc_next;
        } else if (k > 0) {
            /* go down */
            trace[k] = loc;
            k--;
        } else if (!(e->next[0] & 0x80000000) && cas(&e->next[0], loc_next, loc_next|0x80000000)) {
            /* locked */
            break;
        }
    }

    /* claim next item */
    const uint32_t b_nr = __sync_fetch_and_add(&next_block, 1);

    if (b_nr >= signatures_size) {
        fprintf(stderr, "Out of cheese exception, no more blocks available\n");
        exit(1);
    }

    /* fill next item */
    signature_elem *a = &signatures[b_nr];
    a->sig = sig;
    a->prev = p_b;
    a->next[0] = loc_next;
    compiler_barrier();
    signatures[loc].next[0] = b_nr;

    /* determine height */
    uint64_t h = 1 + __builtin_clz(LACE_TRNG) / 2;
    if (h > SL_DEPTH) h = SL_DEPTH;

    /* go up and create links */
    for (k=1;k<h;k++) {
        loc = trace[k];
        for (;;) {
            signature_elem *e = &signatures[loc];
            /* note, at k>0, no locks on edges */
            uint32_t loc_next = *(volatile uint32_t*)&e->next[k];
            if (loc_next != 0 && signatures[loc_next].sig == sig && signatures[loc_next].prev < p_b) {
                loc = loc_next;
            } else if (loc_next != 0 && signatures[loc_next].sig < sig) {
                loc = loc_next;
            } else {
                a->next[k] = loc_next;
                if (cas(&e->next[k], loc_next, b_nr)) break;
            }
        }
    }

    return CALL(encode_block, b_nr);
}

TASK_3(BDD, refine_partition, BDD, dd, BDD, vars, BDD, previous_partition)
{
    /* expecting dd as in s,a,B */
    /* expecting vars to be conjunction of variables in s */
    /* expecting previous_partition as in t,B */

    if (previous_partition == sylvan_false) {
        /* it had no block in the previous iteration, therefore also not now */
        return sylvan_false;
    }

    if (sylvan_set_isempty(vars)) {
        BDD result;
        if (cache_get3(CACHE_REFINE, dd, vars, previous_partition|(refine_iteration<<40), &result)) return result;
        result = CALL(assign_block, dd, previous_partition);
        cache_put3(CACHE_REFINE, dd, vars, previous_partition|(refine_iteration<<40), result);
        return result;
    }

    sylvan_gc_test();

    /* vars != sylvan_false */
    /* dd cannot be sylvan_true - if vars != sylvan_true, then dd is in a,B */

    BDDVAR dd_var = sylvan_isconst(dd) ? 0xffffffff : sylvan_var(dd);
    BDDVAR pp_var = sylvan_var(previous_partition);
    BDDVAR vars_var = sylvan_set_first(vars);

    while (vars_var < dd_var && vars_var+1 < pp_var) {
        vars = sylvan_set_next(vars);
        if (sylvan_set_isempty(vars)) return CALL(refine_partition, dd, vars, previous_partition);
        vars_var = sylvan_set_first(vars);
    }

    /* Consult cache */
    BDD result;
    if (cache_get3(CACHE_REFINE, dd, vars, previous_partition|(refine_iteration<<40), &result)) {
        return result;
    }

    /* Compute cofactors */
    BDD dd_low, dd_high;
    if (vars_var == dd_var) {
        dd_low = sylvan_low(dd);
        dd_high = sylvan_high(dd);
    } else {
        dd_low = dd_high = dd;
    }

    BDD pp_low, pp_high;
    if (vars_var+1 == pp_var) {
        pp_low = sylvan_low(previous_partition);
        pp_high = sylvan_high(previous_partition);
    } else {
        pp_low = pp_high = previous_partition;
    }

    /* Recursive steps */
    BDD next_vars = sylvan_set_next(vars);
    bdd_refs_spawn(SPAWN(refine_partition, dd_low, next_vars, pp_low));
    BDD high = bdd_refs_push(CALL(refine_partition, dd_high, next_vars, pp_high));
    BDD low = bdd_refs_sync(SYNC(refine_partition));
    bdd_refs_pop(1);

    /* rename from s to t */
    result = sylvan_makenode(vars_var+1, low, high);

    /* Write to cache */
    cache_put3(CACHE_REFINE, dd, vars, previous_partition|(refine_iteration<<40), result);
    return result;
}

TASK_IMPL_3(BDD, refine, MTBDD, signature, BDD, vars, BDD, previous_partition)
{
    prepare_refine();
    return CALL(refine_partition, signature, vars, previous_partition);
}

size_t
count_blocks()
{
    return next_block - 1;
}

void
set_signatures_size(size_t count)
{
    signatures_size = count;
}

size_t
get_next_block()
{
    return next_block++;
}

BDD
get_signature(size_t index)
{
    BDD result = signatures[index+1].sig;
    if (result == (uint64_t)-1) return sylvan_false;
    else return result;
}

void
free_refine_data()
{
    if (signatures != NULL) {
        munmap(signatures, sizeof(signature_elem)*signatures_size);
        signatures = NULL;
    }
}
