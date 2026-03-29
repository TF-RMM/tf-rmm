/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SARRAY_H
#define SARRAY_H

/*
 * Sorted array table with log(n) lookup and nlog(n) insert/delete
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

struct sarray_hdr {
	void   *base;	/* separate caller-provided data buffer */
	size_t  max_elems;	/* max elements this array can hold */
	size_t  num_elems;	/* current number of elements stored */
};

/* helper to add key to the user structure */
#define SARRAY_EMBED_KEY() uint64_t key

/*
 * static checks for the following:
 *  - struct has a member key
 *  - key must be the first member
 *  - sizeof(key) == sizeof(uint64_t)
 */
#define sarray_init(hnd, base, size, data_struct)				\
	_sarray_init((hnd), (base), (size), sizeof(data_struct))

#define binary_search_locked(hnd, data_struct, key, idx)			\
	binary_search_internal((hnd), sizeof(data_struct), (key), (idx))

#define sarray_lookup_locked(hnd, data_struct, key)				\
	_sarray_lookup_locked((hnd), sizeof(data_struct), (key))

#define sarray_insert_locked(hnd, data_struct, key, data)			\
	_sarray_insert_locked((hnd), sizeof(data_struct), (key), (data))

#define sarray_delete_locked(hnd, data_struct, key, deleted_data)		\
	_sarray_delete_locked((hnd), sizeof(data_struct), (key), (deleted_data))

/* typed definition
 * Usage:
 *  struct user_struct {
 *     SARRAY_EMBED_KEY();
 *     user fields
 *     ....
 *  }
 *
 *  DEFINE_SARRAY(user_struct, struct user_struct)
 *
 *  The above defines:
 *   sarray_init_user_struct()
 *   sarray_lookup_user_struct()
 *   sarray_delete_user_struct()
 *   sarray_insert_user_struct()
 *   for_each()
 */
/* cppcheck-suppress [misra-c2012-20.7] */
#define DEFINE_SARRAY(_name, _struct)								\
	COMPILER_ASSERT(offsetof(_struct, key) == 0);					\
	COMPILER_ASSERT((SIZEOF_MEMBER(_struct, key) == sizeof(uint64_t)));			\
	static inline struct sarray_hdr *sarray_init_##_name(					\
	/* NOLINTNEXTLINE(bugprone-macro-parentheses) */					\
		struct sarray_hdr *hnd, _struct * base, size_t size)				\
	{											\
		return sarray_init(hnd, base, size, _struct);					\
	}											\
	/* NOLINTNEXTLINE(bugprone-macro-parentheses) */					\
	static inline _struct *sarray_lookup_##_name(struct sarray_hdr *hnd, uint64_t key)	\
	{											\
		return (_struct *)sarray_lookup_locked(hnd, _struct, key);			\
	}											\
	static inline int sarray_insert_##_name(						\
		struct sarray_hdr *hnd, uint64_t key, const _struct *data)			\
	{											\
		return sarray_insert_locked(hnd, _struct, key, data);				\
	}											\
	static inline int sarray_delete_##_name(						\
		/* NOLINTNEXTLINE(bugprone-macro-parentheses) */				\
		struct sarray_hdr *hnd, uint64_t key, _struct *deleted_data)			\
	{											\
		return sarray_delete_locked(hnd, _struct, key, deleted_data);			\
	}

#define for_each(_hnd, _iter)							\
	for ((_iter) = (typeof(_iter))sarray_first(_hnd);			\
		(_iter) < (typeof(_iter))sarray_last((_hnd), sizeof(*(_iter)));	\
		(_iter)++)

/* non-typed functions - prefer typed ones above */
struct sarray_hdr *_sarray_init(struct sarray_hdr *hnd, void *base, size_t size, size_t elem_sz);

void sarray_destroy(struct sarray_hdr *hnd);

int _verify_sarray_hnd(const struct sarray_hdr *hnd);

bool binary_search_internal(struct sarray_hdr *hnd, size_t elem_sz,
			    uint64_t key, unsigned long *idx);

void *_sarray_lookup_locked(struct sarray_hdr *hnd, size_t elem_sz, uint64_t key);

int _sarray_insert_locked(struct sarray_hdr *hnd, size_t elem_sz,
			   uint64_t key, const void *data);

int _sarray_delete_locked(struct sarray_hdr *hnd, size_t elem_sz,
			   uint64_t key, void *deleted_data);

size_t sarray_num_elems(const struct sarray_hdr *hnd);

const void *_get_element(const struct sarray_hdr *hnd, size_t elem_sz, size_t idx);

const void *sarray_first(const struct sarray_hdr *hnd);

const void *sarray_last(const struct sarray_hdr *hnd, size_t elem_sz);

#endif
