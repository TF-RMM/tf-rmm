/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <errno.h>
#include <host_harness.h>
#include <sarray.h>
#include <string.h>
#include <test_helpers.h>
}

struct test_entry {
	SARRAY_EMBED_KEY();
	uint32_t value;
	uint32_t cookie;
};

DEFINE_SARRAY(test_entry, struct test_entry);

/* A differently sized type used to exercise handle/type mismatch checks. */
struct large_test_entry {
	SARRAY_EMBED_KEY();
	uint64_t value[2];
};

DEFINE_SARRAY(large_test_entry, struct large_test_entry);

static test_entry make_entry(uint64_t key, uint32_t value, uint32_t cookie)
{
	struct test_entry entry = {
		.key = key,
		.value = value,
		.cookie = cookie
	};

	return entry;
}

static void check_entry(const struct test_entry *entry, uint64_t key,
			uint32_t value, uint32_t cookie)
{
	LONGS_EQUAL((long)key, (long)entry->key);
	UNSIGNED_LONGS_EQUAL(value, entry->value);
	UNSIGNED_LONGS_EQUAL(cookie, entry->cookie);
}

static void check_keys(struct sarray_hdr *hnd, const uint64_t *keys, size_t count)
{
	const struct test_entry *iter = NULL;
	size_t idx = 0U;

	for_each(hnd, iter) {
		CHECK_TRUE(idx < count);
		LONGS_EQUAL((long)keys[idx], (long)iter->key);
		idx++;
	}

	UNSIGNED_LONGS_EQUAL(count, idx);
	UNSIGNED_LONGS_EQUAL(count, sarray_num_elems(hnd));
}

/* Each test starts with an empty handle and zeroed backing storage. */
TEST_GROUP(sarray_tests) {
	struct sarray_hdr hnd;
	struct test_entry storage[8];

	TEST_SETUP()
	{
		(void)memset(&hnd, 0, sizeof(hnd));
		(void)memset(storage, 0, sizeof(storage));
		test_helpers_init();
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
		test_helpers_expect_assert_fail(false);
	}
};

/* A valid typed initialization records the storage geometry and starts
 * empty.
 */
TEST(sarray_tests, init_valid_buffer_sets_header)
{
	struct sarray_hdr *ret = sarray_init_test_entry(&hnd, storage, sizeof(storage));

	POINTERS_EQUAL(&hnd, ret);
	POINTERS_EQUAL(storage, hnd.base);
	UNSIGNED_LONGS_EQUAL(sizeof(storage[0]), hnd.elem_sz);
	UNSIGNED_LONGS_EQUAL(ARRAY_SIZE(storage), hnd.max_elems);
	UNSIGNED_LONGS_EQUAL(0U, hnd.num_elems);
	UNSIGNED_LONGS_EQUAL(0U, sarray_num_elems(&hnd));
}

/* Trailing bytes smaller than one element do not increase capacity. */
TEST(sarray_tests, init_capacity_uses_floor_division)
{
	union {
		uint64_t align;
		unsigned char data[(sizeof(struct test_entry) * 3U) + 1U];
	} raw;
	struct sarray_hdr *ret = _sarray_init(&hnd, raw.data, sizeof(raw.data),
					      sizeof(struct test_entry));

	POINTERS_EQUAL(&hnd, ret);
	UNSIGNED_LONGS_EQUAL(3U, hnd.max_elems);
	UNSIGNED_LONGS_EQUAL(0U, hnd.num_elems);
}

/* The uint64_t key requires naturally aligned backing storage and elements. */
TEST(sarray_tests, init_rejects_unaligned_backing_storage)
{
	union {
		uint64_t align;
		unsigned char data[sizeof(storage) + 1U];
	} raw;

	CHECK_TRUE(_sarray_init(&hnd, raw.data + 1U, sizeof(raw.data) - 1U,
				 sizeof(struct test_entry)) == NULL);
	CHECK_TRUE(_sarray_init(&hnd, storage, sizeof(storage),
				 sizeof(uint64_t) + 1U) == NULL);
}

/* Initialization requires a handle, backing storage, and space for one key. */
TEST(sarray_tests, init_rejects_invalid_arguments)
{
	CHECK_TRUE(sarray_init_test_entry(NULL, storage, sizeof(storage)) == NULL);
	CHECK_TRUE(sarray_init_test_entry(&hnd, NULL, sizeof(storage)) == NULL);
	CHECK_TRUE(_sarray_init(&hnd, storage, sizeof(struct test_entry) - 1U,
				sizeof(struct test_entry)) == NULL);
	CHECK_TRUE(_sarray_init(&hnd, storage, sizeof(storage),
				sizeof(uint64_t) - 1U) == NULL);
}

/* Malformed handles must be rejected before callers can use their metadata. */
TEST(sarray_tests, verify_handle_rejects_invalid_headers)
{
	uint64_t raw[2];

	hnd.base = NULL;
	hnd.elem_sz = sizeof(storage[0]);
	hnd.max_elems = ARRAY_SIZE(storage);
	hnd.num_elems = 0U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));

	hnd.base = storage;
	hnd.max_elems = 0U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));

	hnd.max_elems = ARRAY_SIZE(storage);
	hnd.num_elems = ARRAY_SIZE(storage) + 1U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));

	hnd.num_elems = 0U;
	hnd.elem_sz = 0U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));

	hnd.base = (unsigned char *)raw + 1U;
	hnd.elem_sz = sizeof(storage[0]);
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));
	UNSIGNED_LONGS_EQUAL(0U, sarray_num_elems(&hnd));

	hnd.base = storage;
	hnd.elem_sz = sizeof(uint64_t) + 1U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(NULL));
}

/*
 * Destroy invalidates every field so the backing storage cannot be reused
 * accidentally.
 */
TEST(sarray_tests, destroy_clears_handle)
{
	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	sarray_destroy(&hnd);

	POINTERS_EQUAL(NULL, hnd.base);
	UNSIGNED_LONGS_EQUAL(0U, hnd.elem_sz);
	UNSIGNED_LONGS_EQUAL(0U, hnd.max_elems);
	UNSIGNED_LONGS_EQUAL(0U, hnd.num_elems);

	sarray_destroy(NULL);
}

/* Accessors expose array boundaries and fail safely for an invalid handle. */
TEST(sarray_tests, accessors_return_expected_addresses)
{
	const struct test_entry *elem;

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	POINTERS_EQUAL(storage, sarray_first(&hnd));
	POINTERS_EQUAL(storage, sarray_last(&hnd, sizeof(storage[0])));
	POINTERS_EQUAL(storage + 3, _get_element(&hnd, sizeof(storage[0]), 3U));
	POINTERS_EQUAL(NULL, sarray_first(NULL));
	POINTERS_EQUAL(NULL, sarray_last(NULL, sizeof(storage[0])));
	POINTERS_EQUAL(NULL, _get_element(NULL, sizeof(storage[0]), 0U));

	elem = sarray_lookup_test_entry(&hnd, 1U);
	POINTERS_EQUAL(NULL, elem);
}

/*
 * Initialize the handle for struct test_entry, then access it through the
 * generated API for a larger type. Every size-dependent operation must reject
 * the mismatch without changing the array.
 */
TEST(sarray_tests, operations_reject_mismatched_element_size)
{
	struct large_test_entry entry = {
		.key = 0U,
		.value = { 1U, 2U }
	};
	unsigned long idx = 0U;

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	LONGS_EQUAL(-EINVAL, sarray_insert_large_test_entry(&hnd, 1U, &entry));
	POINTERS_EQUAL(NULL, sarray_lookup_large_test_entry(&hnd, 1U));
	LONGS_EQUAL(-EINVAL, sarray_delete_large_test_entry(&hnd, 1U, NULL));
	CHECK_FALSE(binary_search_locked(&hnd, struct large_test_entry, 1U, &idx));
	POINTERS_EQUAL(NULL, sarray_last(&hnd, sizeof(entry)));
	POINTERS_EQUAL(NULL, _get_element(&hnd, sizeof(entry), 0U));
	UNSIGNED_LONGS_EQUAL(0U, sarray_num_elems(&hnd));
}

/*
 * Search finds an existing key and returns lower-bound insertion points for
 * misses.
 */
TEST(sarray_tests, binary_search_reports_match_and_insertion_points)
{
	unsigned long idx = ~0UL;
	struct test_entry entries[] = {
		make_entry(0U, 100U, 1000U),
		make_entry(0U, 200U, 2000U),
		make_entry(0U, 300U, 3000U)
	};

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &entries[0]));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 40U, &entries[1]));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 60U, &entries[2]));

	CHECK_TRUE(binary_search_locked(&hnd, struct test_entry, 40U, &idx));
	UNSIGNED_LONGS_EQUAL(1U, idx);

	CHECK_FALSE(binary_search_locked(&hnd, struct test_entry, 10U, &idx));
	UNSIGNED_LONGS_EQUAL(0U, idx);

	CHECK_FALSE(binary_search_locked(&hnd, struct test_entry, 50U, &idx));
	UNSIGNED_LONGS_EQUAL(2U, idx);

	CHECK_FALSE(binary_search_locked(&hnd, struct test_entry, 70U, &idx));
	UNSIGNED_LONGS_EQUAL(3U, idx);

	CHECK_FALSE(binary_search_internal(&hnd, sizeof(struct test_entry), 20U,
					   NULL));
}

/*
 * Insertion orders entries by its key and copies the caller's payload into
 * storage.
 */
TEST(sarray_tests, insert_keeps_entries_sorted_and_overwrites_key_field)
{
	struct test_entry low = make_entry(999U, 10U, 100U);
	struct test_entry mid = make_entry(999U, 20U, 200U);
	struct test_entry high = make_entry(999U, 30U, 300U);
	const uint64_t expected[] = { 10U, 20U, 30U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &mid));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 30U, &high));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &low));

	check_keys(&hnd, expected, ARRAY_SIZE(expected));
	check_entry(&storage[0], 10U, 10U, 100U);
	check_entry(&storage[1], 20U, 20U, 200U);
	check_entry(&storage[2], 30U, 30U, 300U);

	mid.value = 9999U;
	mid.cookie = 9999U;
	check_entry(&storage[1], 20U, 20U, 200U);
}

/* Duplicate keys and exhausted storage return their distinct failure codes. */
TEST(sarray_tests, insert_rejects_duplicate_and_full_array)
{
	struct test_entry entry = make_entry(0U, 7U, 9U);

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	for (size_t i = 0U; i < ARRAY_SIZE(storage); i++) {
		LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, (uint64_t)i, &entry));
	}

	LONGS_EQUAL(-EEXIST, sarray_insert_test_entry(&hnd, 3U, &entry));
	LONGS_EQUAL(-ENOSPC, sarray_insert_test_entry(&hnd, 99U, &entry));
	UNSIGNED_LONGS_EQUAL(ARRAY_SIZE(storage), sarray_num_elems(&hnd));
}

/*
 * A lookup result points into the backing array. Inserting it at an earlier
 * key would shift and overwrite the source before copying it. The operation
 * must reject the aliased source and leave the array unchanged.
 */
TEST(sarray_tests, insert_rejects_data_from_backing_array)
{
	struct test_entry first = make_entry(0U, 10U, 100U);
	struct test_entry second = make_entry(0U, 20U, 200U);
	struct test_entry third = make_entry(0U, 30U, 300U);
	const struct test_entry *source;
	const uint64_t expected[] = { 10U, 30U, 40U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &first));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 30U, &second));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 40U, &third));

	source = sarray_lookup_test_entry(&hnd, 40U);
	CHECK_TRUE(source != NULL);
	LONGS_EQUAL(-EINVAL, sarray_insert_test_entry(&hnd, 20U, source));

	check_keys(&hnd, expected, ARRAY_SIZE(expected));
	check_entry(&storage[1], 30U, 20U, 200U);
	check_entry(&storage[2], 40U, 30U, 300U);
}

/* An unused backing slot can be overwritten by the insertion shift, too. */
TEST(sarray_tests, insert_rejects_data_from_unused_backing_storage)
{
	struct test_entry first = make_entry(0U, 20U, 200U);
	struct test_entry second = make_entry(0U, 30U, 300U);
	const uint64_t expected[] = { 20U, 30U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &first));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 30U, &second));

	storage[2] = make_entry(0U, 10U, 100U);
	LONGS_EQUAL(-EINVAL, sarray_insert_test_entry(&hnd, 10U, &storage[2]));

	check_keys(&hnd, expected, ARRAY_SIZE(expected));
	check_entry(&storage[2], 0U, 10U, 100U);
}

/*
 * Range overflow checks reject fabricated high addresses before either the
 * source or backing storage is dereferenced.
 */
TEST(sarray_tests, insert_rejects_wrapped_address_ranges)
{
	struct test_entry entry = make_entry(0U, 1U, 10U);
	const void *wrapped_data = (const void *)(uintptr_t)(
		UINTPTR_MAX - sizeof(struct test_entry) + 1U);
	void *wrapped_base = (void *)(uintptr_t)(
		UINTPTR_MAX - (2U * sizeof(struct test_entry)) + 1U);

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(-EINVAL, _sarray_insert_locked(&hnd, sizeof(struct test_entry),
		1U, wrapped_data));

	hnd.base = wrapped_base;
	hnd.elem_sz = sizeof(struct test_entry);
	hnd.max_elems = 2U;
	hnd.num_elems = 0U;
	LONGS_EQUAL(-EINVAL, _sarray_insert_locked(&hnd, sizeof(struct test_entry),
		1U, &entry));
}

/*
 * Insertion requires a payload pointer and asserts when the API contract is
 * violated.
 */
ASSERT_TEST(sarray_tests, insert_null_data_asserts)
{
	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	test_helpers_expect_assert_fail(true);
	(void)sarray_insert_test_entry(&hnd, 1U, NULL);
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Lookup returns the matching stored payload and no pointer for a missing or
 * invalid entry.
 */
TEST(sarray_tests, lookup_returns_matching_entry)
{
	struct test_entry first = make_entry(0U, 11U, 111U);
	struct test_entry second = make_entry(0U, 22U, 222U);
	const struct test_entry *found;

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &first));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &second));

	found = sarray_lookup_test_entry(&hnd, 10U);
	CHECK_TRUE(found != NULL);
	check_entry(found, 10U, 11U, 111U);

	found = sarray_lookup_test_entry(&hnd, 20U);
	CHECK_TRUE(found != NULL);
	check_entry(found, 20U, 22U, 222U);

	POINTERS_EQUAL(NULL, sarray_lookup_test_entry(&hnd, 15U));
	POINTERS_EQUAL(NULL, _sarray_lookup_locked(NULL, sizeof(struct test_entry), 1U));
}

/*
 * Deletion returns an optional copy, compacts storage, and preserves array
 * boundaries.
 */
TEST(sarray_tests, delete_removes_entries_and_optionally_returns_payload)
{
	struct test_entry first = make_entry(0U, 10U, 100U);
	struct test_entry second = make_entry(0U, 20U, 200U);
	struct test_entry third = make_entry(0U, 30U, 300U);
	struct test_entry deleted = make_entry(0U, 0U, 0U);
	const uint64_t expected_after_first_delete[] = { 10U, 30U };
	const uint64_t expected_after_second_delete[] = { 30U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &first));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &second));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 30U, &third));

	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 20U, &deleted));
	check_entry(&deleted, 20U, 20U, 200U);
	check_keys(&hnd, expected_after_first_delete, ARRAY_SIZE(expected_after_first_delete));

	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 10U, NULL));
	check_keys(&hnd, expected_after_second_delete, ARRAY_SIZE(expected_after_second_delete));

	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 30U, NULL));
	UNSIGNED_LONGS_EQUAL(0U, sarray_num_elems(&hnd));
	POINTERS_EQUAL(storage, sarray_last(&hnd, sizeof(storage[0])));
}

/*
 * A deletion result cannot use backing storage that compaction will overwrite.
 */
TEST(sarray_tests, delete_rejects_output_in_backing_array)
{
	struct test_entry first = make_entry(0U, 10U, 100U);
	struct test_entry second = make_entry(0U, 20U, 200U);
	struct test_entry third = make_entry(0U, 30U, 300U);
	const uint64_t expected[] = { 10U, 20U, 30U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &first));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &second));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 30U, &third));

	LONGS_EQUAL(-EINVAL, sarray_delete_test_entry(&hnd, 20U, &storage[2]));
	check_keys(&hnd, expected, ARRAY_SIZE(expected));
	check_entry(&storage[2], 30U, 30U, 300U);
}

/*
 * Deletion reports missing keys and invalid handles without modifying the
 * array.
 */
TEST(sarray_tests, delete_rejects_missing_keys_and_invalid_handle)
{
	struct test_entry entry = make_entry(0U, 1U, 2U);

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	LONGS_EQUAL(-ENOENT, sarray_delete_test_entry(&hnd, 1U, NULL));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 2U, &entry));
	LONGS_EQUAL(-ENOENT, sarray_delete_test_entry(&hnd, 1U, NULL));
	LONGS_EQUAL(-EINVAL,
		    _sarray_delete_locked(NULL, sizeof(struct test_entry), 1U, NULL));
}

/* Iteration visits each populated entry once in ascending key order. */
TEST(sarray_tests, iteration_visits_entries_in_sorted_order)
{
	struct test_entry a = make_entry(0U, 1U, 10U);
	struct test_entry b = make_entry(0U, 2U, 20U);
	struct test_entry c = make_entry(0U, 3U, 30U);
	const struct test_entry *iter = NULL;
	const uint64_t expected[] = { 10U, 20U, 40U };
	size_t idx = 0U;

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &b));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 40U, &c));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &a));

	for_each(&hnd, iter) {
		LONGS_EQUAL((long)expected[idx], (long)iter->key);
		idx++;
	}

	UNSIGNED_LONGS_EQUAL(ARRAY_SIZE(expected), idx);
}

/*
 * A mixed insert/delete/reinsert sequence retains sorted order and lookup
 * consistency.
 */
TEST(sarray_tests, mixed_sequence_keeps_invariants)
{
	struct test_entry entries[] = {
		make_entry(0U, 1U, 10U),
		make_entry(0U, 2U, 20U),
		make_entry(0U, 3U, 30U),
		make_entry(0U, 4U, 40U),
		make_entry(0U, 5U, 50U)
	};
	const uint64_t after_insert[] = { 10U, 20U, 30U, 40U, 50U };
	const uint64_t after_delete[] = { 10U, 30U, 50U };
	const uint64_t after_reinsert[] = { 10U, 25U, 30U, 50U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 30U, &entries[2]));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 10U, &entries[0]));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 50U, &entries[4]));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 20U, &entries[1]));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 40U, &entries[3]));
	check_keys(&hnd, after_insert, ARRAY_SIZE(after_insert));

	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 20U, NULL));
	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 40U, NULL));
	check_keys(&hnd, after_delete, ARRAY_SIZE(after_delete));

	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 25U, &entries[1]));
	check_keys(&hnd, after_reinsert, ARRAY_SIZE(after_reinsert));
	CHECK_TRUE(sarray_lookup_test_entry(&hnd, 25U) != NULL);
	CHECK_TRUE(sarray_lookup_test_entry(&hnd, 40U) == NULL);
}

/*
 * Boundary keys, duplicate rejection, and capacity transitions match the
 * model.
 */
TEST(sarray_tests, boundary_sequence_matches_model)
{
	struct test_entry entry = make_entry(0U, 1U, 10U);
	const struct test_entry *found;
	const uint64_t full[] = { 0U, 1U, 2U, 3U, 4U, 5U, 6U, UINT64_MAX };
	const uint64_t deleted[] = { 1U, 2U, 3U, 4U, 5U };
	const uint64_t insert_order[] = { UINT64_MAX, 0U, 4U, 2U, 6U, 1U, 5U, 3U };

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	for (size_t i = 0U; i < ARRAY_SIZE(insert_order); i++) {
		LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, insert_order[i], &entry));
	}
	check_keys(&hnd, full, ARRAY_SIZE(full));

	LONGS_EQUAL(-EEXIST, sarray_insert_test_entry(&hnd, 3U, &entry));
	LONGS_EQUAL(-ENOSPC, sarray_insert_test_entry(&hnd, 7U, &entry));
	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 0U, NULL));
	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, 6U, NULL));
	LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, UINT64_MAX, NULL));
	check_keys(&hnd, deleted, ARRAY_SIZE(deleted));

	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 0U, &entry));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, 6U, &entry));
	LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, UINT64_MAX, &entry));
	check_keys(&hnd, full, ARRAY_SIZE(full));
	for (size_t i = 0U; i < ARRAY_SIZE(full); i++) {
		found = sarray_lookup_test_entry(&hnd, full[i]);
		CHECK_TRUE(found != NULL);
		check_entry(found, full[i], 1U, 10U);
	}
	CHECK_TRUE(sarray_lookup_test_entry(&hnd, 7U) == NULL);
}

/*
 * A fixed pseudo-random sequence is compared with a sorted reference model
 * after every operation, making failures reproducible.
 */
TEST(sarray_tests, randomized_sequence_matches_model)
{
	struct test_entry entry = make_entry(0U, 1U, 10U);
	const struct test_entry *found;
	uint64_t model[ARRAY_SIZE(storage)];
	uint32_t random_state = UINT32_C(0x9e3779b9);
	size_t model_count = 0U;

	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));
	for (size_t step = 0U; step < 128U; step++) {
		size_t idx = 0U;
		uint64_t key;
		bool key_found = false;
		uint32_t operation;

		random_state = (random_state * UINT32_C(1664525)) + UINT32_C(1013904223);
		operation = (random_state >> 16) & 0x3U;
		key = (uint64_t)((random_state >> 8) & 0xfU);

		for (idx = 0U; idx < model_count; idx++) {
			if (model[idx] == key) {
				key_found = true;
				break;
			}
			if (model[idx] > key) {
				break;
			}
		}

		if (operation <= 1U) {
			if (key_found) {
				LONGS_EQUAL(-EEXIST,
					sarray_insert_test_entry(&hnd, key, &entry));
			} else if (model_count == ARRAY_SIZE(model)) {
				LONGS_EQUAL(-ENOSPC,
					sarray_insert_test_entry(&hnd, key, &entry));
			} else {
				for (size_t i = model_count; i > idx; i--) {
					model[i] = model[i - 1U];
				}
				model[idx] = key;
				model_count++;
				LONGS_EQUAL(0, sarray_insert_test_entry(&hnd, key, &entry));
			}
		} else if (operation == 2U) {
			if (key_found) {
				for (size_t i = idx; i < (model_count - 1U); i++) {
					model[i] = model[i + 1U];
				}
				model_count--;
				LONGS_EQUAL(0, sarray_delete_test_entry(&hnd, key, NULL));
			} else {
				LONGS_EQUAL(-ENOENT, sarray_delete_test_entry(&hnd, key, NULL));
			}
		} else {
			found = sarray_lookup_test_entry(&hnd, key);
			if (key_found) {
				CHECK_TRUE(found != NULL);
				check_entry(found, key, 1U, 10U);
			} else {
				POINTERS_EQUAL(NULL, found);
			}
		}

		check_keys(&hnd, model, model_count);
	}
}
