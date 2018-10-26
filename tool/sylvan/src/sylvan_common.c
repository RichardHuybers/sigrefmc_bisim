/*
 * Copyright 2011-2016 Formal Methods and Tools, University of Twente
 * Copyright 2016 Tom van Dijk, Johannes Kepler University Linz
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

#include <sylvan_int.h>

#ifndef cas
#define cas(ptr, old, new) (__sync_bool_compare_and_swap((ptr),(old),(new)))
#endif

/**
 * Implementation of garbage collection
 */

/**
 * Whether garbage collection is enabled or not.
 */
static int gc_enabled = 1;

/**
 * Enable garbage collection (both automatic and manual).
 */
void
sylvan_gc_enable()
{
    gc_enabled = 1;
}

/**
 * Disable garbage collection (both automatic and manual).
 */
void
sylvan_gc_disable()
{
    gc_enabled = 0;
}

/**
 * This variable is used for a cas flag so only one gc runs at one time
 */
static volatile int gc;

/**
 * Structures for the marking mechanisms
 */
typedef struct gc_hook_entry
{
    struct gc_hook_entry *next;
    gc_hook_cb cb;
} * gc_hook_entry_t;

static gc_hook_entry_t mark_list;
static gc_hook_entry_t pregc_list;
static gc_hook_entry_t postgc_list;
static gc_hook_cb main_hook;

void
sylvan_gc_hook_pregc(gc_hook_cb callback)
{
    gc_hook_entry_t e = (gc_hook_entry_t)malloc(sizeof(struct gc_hook_entry));
    e->cb = callback;
    e->next = pregc_list;
    pregc_list = e;
}

void
sylvan_gc_hook_postgc(gc_hook_cb callback)
{
    gc_hook_entry_t e = (gc_hook_entry_t)malloc(sizeof(struct gc_hook_entry));
    e->cb = callback;
    e->next = postgc_list;
    postgc_list = e;
}

void
sylvan_gc_add_mark(gc_hook_cb callback)
{
    gc_hook_entry_t e = (gc_hook_entry_t)malloc(sizeof(struct gc_hook_entry));
    e->cb = callback;
    e->next = mark_list;
    mark_list = e;
}

void
sylvan_gc_hook_main(gc_hook_cb callback)
{
    main_hook = callback;
}

/**
 * Clear the operation cache.
 */
VOID_TASK_IMPL_0(sylvan_clear_cache)
{
   cache_clear();
}

/**
 * Clear the nodes table and mark all referenced nodes.
 *
 * This does not clear the hash data or rehash the nodes.
 * After marking, the "destroy" hooks are called for all unmarked nodes,
 * for example to free data of custom MTBDD leaves.
 */
VOID_TASK_IMPL_0(sylvan_clear_and_mark)
{
    llmsset_clear_data(nodes);

    for (gc_hook_entry_t e = mark_list; e != NULL; e = e->next) {
        WRAP(e->cb);
    }

    llmsset_destroy_unmarked(nodes);
}

/**
 * Clear the hash array of the nodes table and rehash all marked buckets.
 */
VOID_TASK_IMPL_0(sylvan_rehash_all)
{
    // clear hash array
    llmsset_clear_hashes(nodes);

    // rehash marked nodes
    if (llmsset_rehash(nodes) != 0) {
        fprintf(stderr, "sylvan_gc_rehash error: not all nodes could be rehashed!\n");
        exit(1);
    }
}

/**
 * Logic for resizing the nodes table and operation cache
 */

/**
 * Helper routine to compute the next size....
 */
size_t
next_size(size_t current_size)
{
#if SYLVAN_SIZE_FIBONACCI
    size_t f1=1, f2=1;
    for (;;) {
        f2 += f1;
        if (f2 > current_size) return f2;
        f1 += f2;
        if (f1 > current_size) return f1;
    }
#else
    return current_size*2;
#endif
}

/**
 * Resizing heuristic that always doubles the tables when running gc (until max).
 * The nodes table and operation cache are both resized until their maximum size.
 */
VOID_TASK_IMPL_0(sylvan_gc_aggressive_resize)
{
    size_t nodes_size = llmsset_get_size(nodes);
    size_t nodes_max = llmsset_get_max_size(nodes);
    if (nodes_size < nodes_max) {
        size_t new_size = next_size(nodes_size);
        if (new_size > nodes_max) new_size = nodes_max;
        llmsset_set_size(nodes, new_size);
    }
    size_t cache_size = cache_getsize();
    size_t cache_max = cache_getmaxsize();
    if (cache_size < cache_max) {
        size_t new_size = next_size(cache_size);
        if (new_size > cache_max) new_size = cache_max;
        cache_setsize(new_size);
    }
}

/**
 * Resizing heuristic that only resizes when more than 50% is marked.
 * The operation cache is only resized if the nodes table is resized.
 */
VOID_TASK_IMPL_0(sylvan_gc_normal_resize)
{
    size_t nodes_size = llmsset_get_size(nodes);
    size_t nodes_max = llmsset_get_max_size(nodes);
    if (nodes_size < nodes_max) {
        size_t marked = llmsset_count_marked(nodes);
        if (marked*2 > nodes_size) {
            size_t new_size = next_size(nodes_size);
            if (new_size > nodes_max) new_size = nodes_max;
            llmsset_set_size(nodes, new_size);

            // also increase the operation cache
            size_t cache_size = cache_getsize();
            size_t cache_max = cache_getmaxsize();
            if (cache_size < cache_max) {
                new_size = next_size(cache_size);
                if (new_size > cache_max) new_size = cache_max;
                cache_setsize(new_size);
            }
        }
    }
}

/**
 * Actual implementation of garbage collection
 */
VOID_TASK_0(sylvan_gc_go)
{
    sylvan_stats_count(SYLVAN_GC_COUNT);
    sylvan_timer_start(SYLVAN_GC);

    // call pre gc hooks
    for (gc_hook_entry_t e = pregc_list; e != NULL; e = e->next) {
        WRAP(e->cb);
    }

    /*
     * This simply clears the cache.
     * Alternatively, we could implement for example some strategy
     * where part of the cache is cleared and part is marked
     */
    CALL(sylvan_clear_cache);

    CALL(sylvan_clear_and_mark);

    // call hooks for resizing and all that
    WRAP(main_hook);

    CALL(sylvan_rehash_all);

    // call post gc hooks
    for (gc_hook_entry_t e = postgc_list; e != NULL; e = e->next) {
        WRAP(e->cb);
    }

    sylvan_timer_stop(SYLVAN_GC);
}

/**
 * Perform garbage collection
 */
VOID_TASK_IMPL_0(sylvan_gc)
{
    if (gc_enabled) {
        if (cas(&gc, 0, 1)) {
            NEWFRAME(sylvan_gc_go);
            gc = 0;
        } else {
            /* wait for new frame to appear */
            while (*(Task* volatile*)&(lace_newframe.t) == 0) {}
            lace_yield(__lace_worker, __lace_dq_head);
        }
    }
}

/**
 * The unique table
 */

llmsset_t nodes;

/**
 * Initializes Sylvan.
 */
void
sylvan_init_package(size_t tablesize, size_t maxsize, size_t cachesize, size_t max_cachesize)
{
    /* Some sanity checks */
    if (tablesize > maxsize) tablesize = maxsize;
    if (cachesize > max_cachesize) cachesize = max_cachesize;

    if (maxsize > 0x000003ffffffffff) {
        fprintf(stderr, "sylvan_init_package error: tablesize must be <= 42 bits!\n");
        exit(1);
    }

    /* Create tables */
    nodes = llmsset_create(tablesize, maxsize);
    cache_create(cachesize, max_cachesize);

    /* Initialize garbage collection */
    gc = 0;
#if SYLVAN_AGGRESSIVE_RESIZE
    main_hook = TASK(sylvan_gc_aggressive_resize);
#else
    main_hook = TASK(sylvan_gc_normal_resize);
#endif

    LACE_ME;
    sylvan_stats_init();
}

struct reg_quit_entry
{
    struct reg_quit_entry *next;
    quit_cb cb;
};

static struct reg_quit_entry *quit_register = NULL;

void
sylvan_register_quit(quit_cb cb)
{
    struct reg_quit_entry *e = (struct reg_quit_entry*)malloc(sizeof(struct reg_quit_entry));
    e->next = quit_register;
    e->cb = cb;
    quit_register = e;
}

void
sylvan_quit()
{
    while (quit_register != NULL) {
        struct reg_quit_entry *e = quit_register;
        quit_register = e->next;
        e->cb();
        free(e);
    }

    while (pregc_list != NULL) {
        gc_hook_entry_t e = pregc_list;
        pregc_list = e->next;
        free(e);
    }

    while (postgc_list != NULL) {
        gc_hook_entry_t e = postgc_list;
        postgc_list = e->next;
        free(e);
    }

    while (mark_list != NULL) {
        gc_hook_entry_t e = mark_list;
        mark_list = e->next;
        free(e);
    }

    cache_free();
    llmsset_free(nodes);
}

/**
 * Calculate table usage (in parallel)
 */
VOID_TASK_IMPL_2(sylvan_table_usage, size_t*, filled, size_t*, total)
{
    size_t tot = llmsset_get_size(nodes);
    if (filled != NULL) *filled = llmsset_count_marked(nodes);
    if (total != NULL) *total = tot;
}

