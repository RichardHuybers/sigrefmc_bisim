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

static BDD *signatures = NULL;
static size_t signatures_size = 0;
static uint32_t next_block = 1;
static size_t refine_iteration = 0;

static uint64_t *table = NULL;
static size_t table_size = 0;

static uint64_t *old_table = NULL;
static size_t old_table_size = 0;
static int go_resize = 0;

void
prepare_refine()
{
    if (signatures != NULL) {
        munmap(signatures, sizeof(BDD)*signatures_size);
    }
    signatures = (BDD*)mmap(0, sizeof(BDD)*signatures_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, 0, 0);
    if (signatures == (BDD*)-1) {
        fprintf(stderr, "sigref: Unable to allocate memory (%'zu bytes) for the signatures!\n", signatures_size*sizeof(BDD));
        exit(1);
    }
    refine_iteration++;

    if (table != NULL) munmap(table, 3*8*table_size);
    table_size = 1ULL<<14;
    table = (uint64_t*)mmap(0, 3*8*table_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, 0, 0);
    if (table == (uint64_t*)-1) {
        fprintf(stderr, "sigref: Unable to allocate memory (%'zu bytes) for the table!\n", 3*8*table_size);
        exit(1);
    }
}

/* Rotating 64-bit FNV-1a hash */
static uint64_t
_hash(uint64_t a, uint64_t b)
{
    const uint64_t prime = 1099511628211;
    uint64_t hash = 14695981039346656037LLU;
    hash = (hash ^ (a>>32));
    hash = (hash ^ a) * prime;
    hash = (hash ^ b) * prime;
    return hash ^ (hash>>32);
}

VOID_TASK_2(rehash, size_t, first, size_t, count)
{
    if (count > 128) {
        SPAWN(rehash, first, count/2);
        CALL(rehash, first+count/2, count-count/2);
        SYNC(rehash);
        return;
    }

    while (count--) {
        uint64_t *old_ptr = old_table + first*3;
        uint64_t a = old_ptr[0];
        uint64_t b = old_ptr[1];
        uint64_t c = old_ptr[2];

        uint64_t hash = _hash(a, b);
        uint64_t pos = hash % table_size;

        volatile uint64_t *ptr = 0;
        for (;;) {
            ptr = table + pos*3;
            if (*ptr == 0) {
                if (cas(ptr, 0, a)) {
                    ptr[1] = b;
                    ptr[2] = c;
                    break;
                }
            }
            pos++;
            if (pos >= table_size) pos = 0;
        }

        first++;
    }
}

VOID_TASK_0(grow_it)
{
    old_table = table;
    old_table_size = table_size;

    table_size = old_table_size*2;
    table = (uint64_t*)mmap(0, 3*8*table_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, 0, 0);
    if (table == (uint64_t*)-1) {
        fprintf(stderr, "sigref: Unable to allocate memory (%'zu bytes) for the table!\n", 3*8*table_size);
        exit(1);
    }

    CALL(rehash, 0, old_table_size);

    munmap(old_table, 3*8*old_table_size);
}

VOID_TASK_0(grow)
{
    if (cas(&go_resize, 0, 1)) {
        NEWFRAME(grow_it);
        go_resize = 0;
    } else {
        /* wait for new frame to appear */
        while (*(Task* volatile*)&(lace_newframe.t) == 0) {}
        lace_yield(__lace_worker, __lace_dq_head);
    }
}

static uint64_t
search_or_insert(uint64_t sig, uint64_t previous_block)
{
    uint64_t hash = _hash(sig, previous_block);
    uint64_t pos = hash % table_size;

    volatile uint64_t *ptr = 0;
    uint64_t a, b, c;
    int count = 0;
    for (;;) {
        ptr = table + pos*3;
        a = *ptr;
        if (a == sig) {
            while ((b=ptr[1]) == 0) continue;
            if (b == previous_block) {
                while ((c=ptr[2]) == 0) continue;
                return c;
            }
        } else if (a == 0) {
            if (cas(ptr, 0, sig)) {
                c = ptr[2] = __sync_fetch_and_add(&next_block, 1);
                ptr[1] = previous_block;
                return c;
            } else {
                continue;
            }
        }
        pos++;
        if (pos >= table_size) pos = 0;
        if (++count >= 128) return 0;
    }
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
        BDD cur = *(volatile BDD*)&signatures[p_b];
        if (cur == sig) return previous_block;
        if (cur != 0) break;
        if (cas(&signatures[p_b], 0, sig)) return previous_block;
    }

    // no previous block number, search or insert
    uint64_t c;
    while ((c = search_or_insert(sig, previous_block)) == 0) CALL(grow);

    if (c >= signatures_size) {
        fprintf(stderr, "Out of cheese exception, no more blocks available\n");
        exit(1);
    }

    return CALL(encode_block, c);
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
    BDD result = signatures[index+1];
    if (result == (uint64_t)-1) return sylvan_false;
    else return result;
}

void
free_refine_data()
{
    if (signatures != NULL) {
        munmap(signatures, sizeof(BDD)*signatures_size);
        signatures = NULL;
    }

    if (table != NULL) {
        munmap(table, 3*8*table_size);
        table = NULL;
    }
}
