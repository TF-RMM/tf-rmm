/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TB_COMMON_H
#define TB_COMMON_H

#include "granule.h"
#include "host_defs.h"
#include "stdbool.h"
#include "stdint.h"
#include "string.h"

/* Forces the model-checker to only consider executions where `p` holds. */
#define __ASSUME(p)			\
	do {				\
		__CPROVER_assume((p));	\
	} while (false)

#define ASSUME(p) __ASSUME(p)

/*
 * Challenges the model checker to show that `p` holds in the current execution
 * (in which case this behaves like a no-op), or otherwise come up with a
 * counterexample trace of states and assignments to variables which refutes
 * `p`, associating the name `name` to this trace.
 */
#define __ASSERT(p, name)				\
	do {						\
		__CPROVER_assert((p), (name));	\
	} while (false)

#define ASSERT(p, name) __ASSERT((p), (name))

/*
 * A marker for reachability: running CBMC with `--cover cover` will check that
 * all instances of `COVER` are reachable from the program entry point.
 */
#define __COVER(p)			\
	do {				\
		__CPROVER_cover(p);	\
	} while (false)

#define COVER(p) __COVER(p)

#define REACHABLE COVER(true)

/*
 * An assertion that always fails, useful for checking code-paths are never
 * reachable.
 */
#define UNREACHABLE	ASSERT(false, "UNREACHABLE")

/*
 * Declare nondet_* functions for primitive types.
 * Ref: CBMC automatically returns nondet values, or symbolic values, matching
 * the return types. However, enum is treated as integer hence the value might
 * be out of range.
 */
bool nondet_bool(void);
unsigned char nondet_unsigned_char(void);
unsigned short nondet_unsigned_short(void);
unsigned int nondet_unsigned_int(void);
unsigned long nondet_unsigned_long(void);
char nondet_char(void);
short nondet_short(void);
int nondet_int(void);
long nondet_long(void);
uint32_t nondet_uint32_t(void);
uint64_t nondet_uint64_t(void);
int32_t nondet_int32_t(void);
int64_t nondet_int64_t(void);
size_t nondet_size_t(void);

struct tb_regs {
	uint64_t X0;
	uint64_t X1;
	uint64_t X2;
	uint64_t X3;
	uint64_t X4;
	uint64_t X5;
	uint64_t X6;
};

struct tb_regs __tb_arb_regs(void);

bool ResultEqual_2(unsigned int code, unsigned int expected);
bool ResultEqual_3(unsigned int code, unsigned int expected, unsigned int walk_level);
uint64_t Zeros(void);

/* Some autogen contains this function. */
bool __tb_arb_bool(void);

struct tb_lock_status {
	uint64_t something;
};
void __tb_lock_invariant(struct tb_lock_status *lock_status);

struct tb_lock_status __tb_lock_status(void);

/*
 * Functions that manipulates internal states,
 * including PA, granule metadata and granule buffer, or content.
 */
bool valid_pa(uint64_t addr);
bool valid_granule_metadata_ptr(struct granule *p);
struct granule *pa_to_granule_metadata_ptr(uint64_t addr);
void *granule_metadata_ptr_to_buffer_ptr(struct granule *g_ptr);
uint64_t granule_metadata_ptr_to_pa(struct granule *g_ptr);
void *pa_to_granule_buffer_ptr(uint64_t addr);

/* TODO change the function name */
void init_pa_page(const void *content, size_t size);


/*
 * Return an unused continuous index to both `granules` and `granules_buffer`
 * arrays.
 */
size_t next_index(void);
bool unused_index(size_t index);
/*
 * Initialise granule at an non-deterministic granule. It updates both granule
 * metadata array and physical page array.
 */
struct granule *inject_granule_at(const struct granule *granule_metadata,
				  const void *src_page,
				  size_t src_size,
				  size_t idx);
struct granule *inject_granule(const struct granule *granule_metadata,
			       const void *src_page,
			       size_t src_size);

/* Returns the status of the granule in the GPT. */
enum granule_gpt get_granule_gpt(uint64_t addr);
/* Set the status of the granule in GPT. */
void set_granule_gpt(uint64_t addr, enum granule_gpt granule_gpt);

#endif  /* !TB_COMMON_H */
