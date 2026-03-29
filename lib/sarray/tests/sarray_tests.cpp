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

TEST(sarray_tests, init_valid_buffer_sets_header)
{
	struct sarray_hdr *ret = sarray_init_test_entry(&hnd, storage, sizeof(storage));

	POINTERS_EQUAL(&hnd, ret);
	POINTERS_EQUAL(storage, hnd.base);
	UNSIGNED_LONGS_EQUAL(ARRAY_SIZE(storage), hnd.max_elems);
	UNSIGNED_LONGS_EQUAL(0U, hnd.num_elems);
	UNSIGNED_LONGS_EQUAL(0U, sarray_num_elems(&hnd));
}

TEST(sarray_tests, init_capacity_uses_floor_division)
{
	unsigned char raw[(sizeof(struct test_entry) * 3U) + 1U];
	struct sarray_hdr *ret = _sarray_init(&hnd, raw, sizeof(raw), sizeof(struct test_entry));

	POINTERS_EQUAL(&hnd, ret);
	UNSIGNED_LONGS_EQUAL(3U, hnd.max_elems);
	UNSIGNED_LONGS_EQUAL(0U, hnd.num_elems);
}

TEST(sarray_tests, init_rejects_invalid_arguments)
{
	CHECK_TRUE(sarray_init_test_entry(NULL, storage, sizeof(storage)) == NULL);
	CHECK_TRUE(sarray_init_test_entry(&hnd, NULL, sizeof(storage)) == NULL);
	CHECK_TRUE(_sarray_init(&hnd, storage, sizeof(struct test_entry) - 1U,
				sizeof(struct test_entry)) == NULL);
	CHECK_TRUE(_sarray_init(&hnd, storage, sizeof(storage),
				sizeof(uint64_t) - 1U) == NULL);
}

TEST(sarray_tests, verify_handle_rejects_invalid_headers)
{
	hnd.base = NULL;
	hnd.max_elems = ARRAY_SIZE(storage);
	hnd.num_elems = 0U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));

	hnd.base = storage;
	hnd.max_elems = 0U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));

	hnd.max_elems = ARRAY_SIZE(storage);
	hnd.num_elems = ARRAY_SIZE(storage) + 1U;
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(&hnd));
	LONGS_EQUAL(-EINVAL, _verify_sarray_hnd(NULL));
}

TEST(sarray_tests, destroy_clears_handle)
{
	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	sarray_destroy(&hnd);

	POINTERS_EQUAL(NULL, hnd.base);
	UNSIGNED_LONGS_EQUAL(0U, hnd.max_elems);
	UNSIGNED_LONGS_EQUAL(0U, hnd.num_elems);

	sarray_destroy(NULL);
}

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

ASSERT_TEST(sarray_tests, insert_null_data_asserts)
{
	(void)sarray_init_test_entry(&hnd, storage, sizeof(storage));

	test_helpers_expect_assert_fail(true);
	(void)sarray_insert_test_entry(&hnd, 1U, NULL);
	test_helpers_fail_if_no_assert_failed();
}

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
