/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <errno.h>
#include <sarray.h>
#include <stdint.h>
#include <string.h>

static unsigned char *_elem_ptr(const struct sarray_hdr *hnd, size_t elem_sz, size_t idx)
{
	if (hnd->base == NULL) {
		return NULL;
	}
	return &((unsigned char *)hnd->base)[idx * elem_sz];
}

static const unsigned char *_elem_const_ptr(
	const struct sarray_hdr *hnd, size_t elem_sz, size_t idx)
{
	if (hnd->base == NULL) {
		return NULL;
	}
	return &((const unsigned char *)hnd->base)[idx * elem_sz];
}

static const uint64_t *_key_const_ptr(const struct sarray_hdr *hnd, size_t elem_sz, size_t idx)
{
	return (const uint64_t *)_elem_const_ptr(hnd, elem_sz, idx);
}

static uint64_t *_key_ptr(void *data)
{
	/* key should be the start of the data struct */
	return (uint64_t *)data;
}

/* cppcheck-suppress misra-c2012-8.7 */
const void *sarray_first(const struct sarray_hdr *hnd)
{
	return (const void *)((hnd != NULL) ? hnd->base : NULL);
}

/* cppcheck-suppress misra-c2012-8.7 */
const void *sarray_last(const struct sarray_hdr *hnd, size_t elem_sz)
{
	if ((hnd == NULL) || (hnd->base == NULL)) {
		return NULL;
	}
	/* coverity[null_field:SUPPRESS] */
	return (const void *)&((unsigned char *)hnd->base)[sarray_num_elems(hnd) * elem_sz];
}

/* cppcheck-suppress misra-c2012-8.7 */
const void *_get_element(const struct sarray_hdr *hnd, size_t elem_sz, size_t idx)
{
	return (const void *)((hnd != NULL) ? _elem_ptr(hnd, elem_sz, idx) : NULL);
}

size_t sarray_num_elems(const struct sarray_hdr *hnd)
{
	if (_verify_sarray_hnd(hnd) != 0) {
		return 0;
	}

	return hnd->num_elems;
}

int _verify_sarray_hnd(const struct sarray_hdr *hnd)
{
	if (hnd == NULL) {
		return -EINVAL;
	}

	if (hnd->base == NULL) {
		return -EINVAL;
	}

	if (hnd->max_elems == 0U) {
		return -EINVAL;
	}

	if (hnd->num_elems > hnd->max_elems) {
		return -EINVAL;
	}

	return 0;
}

/* cppcheck-suppress misra-c2012-8.7 */
struct sarray_hdr *_sarray_init(struct sarray_hdr *hnd, void *base, size_t size, size_t elem_sz)
{
	size_t max_elems;

	if ((hnd == NULL) || (base == NULL)) {
		return NULL;
	}

	/* data struct should at least hold the key */
	if (elem_sz < sizeof(uint64_t)) {
		return NULL;
	}

	if (size < elem_sz) {
		return NULL;
	}

	max_elems = size / elem_sz;
	if (max_elems == 0U) {
		return NULL;
	}

	hnd->base = base;
	hnd->max_elems = max_elems;
	hnd->num_elems = 0U;

	return hnd;
}

/* cppcheck-suppress misra-c2012-8.7 */
void sarray_destroy(struct sarray_hdr *hnd)
{
	if (hnd == NULL) {
		return;
	}

	hnd->base = NULL;
	hnd->max_elems = 0U;
	hnd->num_elems = 0U;
}

bool binary_search_internal(struct sarray_hdr *hnd, size_t elem_sz, uint64_t key,
			    unsigned long *idx)
{
	size_t left;
	size_t right;

	if (idx == NULL) {
		return false;
	}

	if (_verify_sarray_hnd(hnd) != 0) {
		return false;
	}

	left = 0U;
	right = hnd->num_elems;   /* search in [left, right) */

	while (left < right) {
		size_t mid = left + ((right - left) / 2U);
		uint64_t mid_key = *_key_const_ptr(hnd, elem_sz, mid);

		if (mid_key == key) {
			*idx = (unsigned long)mid;
			return true;
		}
		/*
		 * mid < key, jump to [m+1,r)
		 *
		 *       +--k--+
		 * ^     ^     ^
		 * l-----m-----r-----n
		 */
		if (mid_key < key) {
			left = mid + 1U;
		} else {
		/*
		 * mid > key, jump to [l, m)
		 *
		 * +--k--+
		 * ^     ^
		 * l-----m-----r-----n
		 */

			right = mid;
		}
	}

	/*
	 * if the key was not found then:
	 *  keys[left] < k < keys[right]
	 */
	*idx = (unsigned long)left;
	return false;
}

/* cppcheck-suppress misra-c2012-8.7 */
void *_sarray_lookup_locked(struct sarray_hdr *hnd, size_t elem_sz, uint64_t key)
{
	unsigned long idx;

	if (_verify_sarray_hnd(hnd) != 0) {
		return NULL;
	}

	if (!binary_search_internal(hnd, elem_sz, key, &idx)) {
		return NULL;
	}

	return _elem_ptr(hnd, elem_sz, (size_t)idx);
}

/* cppcheck-suppress misra-c2012-8.7 */
int _sarray_insert_locked(struct sarray_hdr *hnd, size_t elem_sz, uint64_t key, const void *data)
{
	unsigned long idx = 0U;
	size_t count;
	void *dst;

	assert(data != NULL);

	if (_verify_sarray_hnd(hnd) != 0) {
		return -EINVAL;
	}

	if (binary_search_internal(hnd, elem_sz, key, &idx)) {
		return -EEXIST;
	}

	if (hnd->num_elems == hnd->max_elems) {
		return -ENOSPC;
	}

	/*
	 * when bsearch fails, idx is such that:
	 *  0....idx-1, idx, idx+1, ... n-1
	 *  i.e., such that the new key > all elements to the left of idx
	 *
	 *  so make space at idx by shifting from idx to idx+1 till n
	 *  0....idx-1, idx, new, idx+1, ... n-1
	 */
	count = hnd->num_elems - idx;
	if (count > 0U) {
		(void)memmove(_elem_ptr(hnd, elem_sz, idx + 1U),
			      _elem_ptr(hnd, elem_sz, idx),
			      count * elem_sz);
	}

	/* insert new element and key */
	dst = _elem_ptr(hnd, elem_sz, idx);
	(void)memcpy(dst, data, elem_sz);

	*_key_ptr(dst) = key;

	hnd->num_elems++;
	return 0;
}

/* cppcheck-suppress misra-c2012-8.7 */
int _sarray_delete_locked(struct sarray_hdr *hnd, size_t elem_sz, uint64_t key, void *deleted_data)
{
	unsigned long idx;
	size_t count;

	if (_verify_sarray_hnd(hnd) != 0) {
		return -EINVAL;
	}

	if (!binary_search_internal(hnd, elem_sz, key, &idx)) {
		return -ENOENT;
	}

	/* copy deleted data if asked for */
	if (deleted_data != NULL) {
		(void)memcpy(deleted_data, (void *)_elem_ptr(hnd, elem_sz, idx), elem_sz);
	}

	/*
	 * when bsearch succeeds, idx is such that:
	 *  0....idx-1, idx, idx+1, ... n-1
	 *  i.e., idx.key == key
	 *
	 * delete idx by overwriting next element to its position until n
	 *  0....idx-1, idx+1, ... n-1
	 */

	count = hnd->num_elems - idx - 1U;
	if (count > 0U) {
		(void)memmove(_elem_ptr(hnd, elem_sz, idx),
			      _elem_ptr(hnd, elem_sz, idx + 1U),
			      count * elem_sz);
	}

	hnd->num_elems--;

	return 0;
}
