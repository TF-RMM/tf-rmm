/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>	/* Interface to exercise */
#include <buffer_private.h>
#include <cpuid.h>
#include <granule.h>
#include <host_harness.h>
#include <host_utils.h>
#include <realm_test_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_harness.h>
#include <test_helpers.h>
#include <time.h>
#include <xlat_tables.h>
}

/*
 * Size of a chunck of memory on a granule, used for random
 * read and writes
 */
#define GRANULE_BLOCK_SIZE		(GRANULE_SIZE >> 2U)
#define GRANULE_BLOCKS			(GRANULE_SIZE/GRANULE_BLOCK_SIZE)

/*
 * Function to get a random address within the granules range.
 * The address will be aligned to granule size.
 */
static inline uintptr_t get_rand_granule_addr(void) {
	uintptr_t addr;
	int random_granule = test_helpers_get_rand_in_range(0,
					test_helpers_get_nr_granules() - 1);

	addr = (uintptr_t)(random_granule * GRANULE_SIZE)
					+ host_util_get_granule_base();

	return addr;
}

/*
 * Helper function to generate an array of random granule addresses
 * in which none of them repeat.
 */
static void get_rand_granule_array(uintptr_t *arr, unsigned int count)
{
	for (unsigned int i = 0U; i < count; i++) {
		arr[i] = get_rand_granule_addr();
		if (i > 0U) {
			bool match;
			do {
				/* Check for duplicates so far */
				match = false;
				for (unsigned j = 0U; j < i; j++) {
					if (arr[j] == arr[i]) {
						arr[i] =
						    get_rand_granule_addr();
						match = true;
						break;
					}
				}
			} while(match == true);
		}
	}

}

TEST_GROUP(slot_buffer) {
	/*
	 * For this test, TEST_SETUP() initializes RMM which includes
	 * translation table and slot buffer mechanism initialization.
	 * Therefore, all the tests assume that the slot buffer mechanism
	 * has been properly initialized.
	 */
	TEST_SETUP()
	{
		static int random_seed = 0;

		/* Enable the platform with support for multiple PEs */
		test_helpers_rmm_start(true);

		/* Make sure current cpu id is 0 (primary processor) */
		host_util_set_cpuid(0U);

		/* Initialize the random seed */
		while (random_seed == 0) {
			random_seed = (int)time(NULL);
			srand(random_seed);
		}

		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
		/*
		 * Unregister any existing callback that might
		 * have been installed
		 */
		(void)test_helpers_unregister_cb(CB_BUFFER_MAP);
		(void)test_helpers_unregister_cb(CB_BUFFER_UNMAP);
	}
};

TEST(slot_buffer, granule_map_buffer_unmap_TC1)
{
	uintptr_t slot_va, expected_va, granule_addr;
	struct granule *test_granule;
	union test_harness_cbs cb;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * For all possible slot buffer types and all possible CPUs, try to
	 * map a random granule. Then unmap it.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_aarch64_vmsa;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_aarch64_vmsa;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	granule_addr = get_rand_granule_addr();
	test_granule = addr_to_granule(granule_addr);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		host_util_set_cpuid(i);
		for (unsigned int j = 0U; j < NR_CPU_SLOTS; j++) {
			if (j == SLOT_NS) {
				/* Not supported. granule_map() would assert */
				continue;
			}
			slot_va = (uintptr_t)granule_map(test_granule,
							 (enum buffer_slot)j);
			expected_va = slot_to_va((enum buffer_slot)j);

			/* Test the return value from granule_map() */
			POINTERS_EQUAL(slot_va, expected_va);

			/*
			 * Test that the granule is actually mapped to the
			 * expected VA in the Stage 1 xlat tables as per
			 * aarch64 VMSA.
			 */
			POINTERS_EQUAL(expected_va,
				realm_test_util_slot_va_from_pa(granule_addr));

			/* Unmap the buffer */
			buffer_unmap((void *)slot_va);

			/*
			 * realm_test_util_slot_va_from_pa() return NULL
			 * if the address passed to it is not mapped to any
			 * slot buffer.
			 */
			POINTERS_EQUAL(NULL,
				realm_test_util_slot_va_from_pa(granule_addr));

		} /* For each slot type */
	} /* For each CPU */
}

TEST(slot_buffer, granule_map_buffer_unmap_TC2)
{
	uintptr_t mapped_pa;
	struct granule *test_granule;
	uintptr_t granules_per_cpu[MAX_CPUS];
	void *slot_va[MAX_CPUS];
	union test_harness_cbs cb;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * For each possible slot buffer type, map a different random
	 * granule to each one of the available CPUs. Then validate that
	 * the same PA is not mapped to two different CPUs.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_aarch64_vmsa;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_aarch64_vmsa;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	get_rand_granule_array(granules_per_cpu, MAX_CPUS);
	for (unsigned int i = 0U; i < NR_CPU_SLOTS; i++) {
		if (i == SLOT_NS) {
			/* Not supported. granule_map() would assert */
			continue;
		}

		/* Map a granule on each CPU for the same slot */
		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			host_util_set_cpuid(j);
			test_granule = addr_to_granule(granules_per_cpu[j]);
			slot_va[j] = granule_map(test_granule,
						 (enum buffer_slot)i);
		}

		/*
		 * Iterate over all CPUs, ensuring that the granules are mapped
		 * into the slots for the right CPU.
		 */
		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			/*
			 * Get the PA mapped to the slot 'i' for CPU 'j'
			 */
			host_util_set_cpuid(j);
			mapped_pa = realm_test_util_slot_to_pa(
						(enum buffer_slot)i);

			/*
			 * Check that the PA mapped to slot 'i' for CPU 'j'
			 * is only mapped on the same slot for the same CPU.
			 * For the rest of CPUs, the PAs should not match.
			 */
			for (unsigned int k = 0U; k < MAX_CPUS; k++) {
				if (j == k) {
					POINTERS_EQUAL(granules_per_cpu[k],
						       mapped_pa);
				} else {
					CHECK_FALSE(granules_per_cpu[k] ==
						    mapped_pa);
				}
			}

		}

		/* Unmap the granules. */
		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			host_util_set_cpuid(j);
			buffer_unmap((void *)slot_va[j]);
		}
	} /* NR_CPU_SLOTS */

	/*
	 * granule_map() asserts if the granule address is not aligned, so
	 * skip that test.
	 */
};

TEST(slot_buffer, granule_map_buffer_unmap_TC3)
{
	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Test that buffer_unmap() exits gracefully when an unmapped VA
	 * is used.
	 ******************************************************************/

	buffer_unmap((void *)slot_to_va(SLOT_NS));
	TEST_EXIT;
}

TEST(slot_buffer, granule_map_buffer_unmap_TC4)
{
	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Test that buffer_unmap() exits gracefully when an invalid VA
	 * is used.
	 ******************************************************************/

	buffer_unmap((void *)NULL);
	TEST_EXIT;
}

TEST(slot_buffer, ns_buffer_write_TC1)
{
	uintptr_t granule_addrs[3];
	struct granule *test_granule;
	union test_harness_cbs cb;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * For each CPU, map a random granule to NS_SLOT and copy random
	 * data into it through several calls to ns_buffer_write().
	 * Then verify that for each call to ns_buffer_write(), the data
	 * is properly copied without affecting other areas of the dest
	 * granule.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/*
	 * Get two random granules:
	 * granule_addrs[0]: To be used as dest write operations (SLOT_NS).
	 * granule_addrs[1]: will hold a copy of the data to transfer, so we
	 *		     can verify later.
	 * granule_addrs[2]: Just a zeroed granule to easy some tests.
	 */
	get_rand_granule_array(granule_addrs, 3U);

	/* Granule to test zeroes */
	(void)memset((void *)granule_addrs[2], 0, GRANULE_SIZE);

	test_granule = addr_to_granule(granule_addrs[0]);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {

		/* Fill the granule with random data */
		for (unsigned int i = 0U; i < GRANULE_SIZE/sizeof(int); i++) {
			*((int *)granule_addrs[1] + i) = rand();
		}

		/* Clean the granule to test */
		(void)memset((void *)granule_addrs[0], 0, GRANULE_SIZE);

		host_util_set_cpuid(i);

		/*
		 * Copy block by block, verifying that each copied block
		 * doesn't affect anything written before nor a block to be
		 * written yet.
		 */
		for (unsigned int j = 0U; j < GRANULE_BLOCKS; j++) {
			ns_buffer_write(SLOT_NS, test_granule,
					GRANULE_BLOCK_SIZE * j,
					GRANULE_BLOCK_SIZE,
					(void*)(granule_addrs[1] +
						(GRANULE_BLOCK_SIZE * j)));

			MEMCMP_EQUAL((void *)granule_addrs[1],
				     (void *)granule_addrs[0],
				     (size_t)((j + 1U) * GRANULE_BLOCK_SIZE));

			/*
			 * Verify than any block that has not been written yet
			 * is still all zeros.
			 */
			MEMCMP_EQUAL((void *)granule_addrs[2],
				     (void *)(granule_addrs[0] +
					((j + 1U) * GRANULE_BLOCK_SIZE)),
				     (GRANULE_BLOCKS - (j + 1U)) *
					GRANULE_BLOCK_SIZE);
		}
	}
}

TEST(slot_buffer, ns_buffer_write_TC2)
{
	uintptr_t granule_addrs[3];
	struct granule *test_granule;
	union test_harness_cbs cb;
	int val;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * For every CPU, verify that ns_buffer_write() does not alter the
	 * source.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/*
	 * Get three random granules:
	 * granule_addrs[0]: Will contain the original data to write.
	 * granule_addrs[1]: Will hold a copy of the src granule to compare.
	 * granule_addrs[2]: Destination granule.
	 */
	get_rand_granule_array(granule_addrs, 3U);

	/* Generate random data. */
	for (unsigned int j = 0U; j < GRANULE_SIZE/sizeof(int); j++) {
		val = rand();
		*((int *)granule_addrs[0] + j) = val;
		*((int *)granule_addrs[1] + j) = val;
	}

	test_granule = addr_to_granule(granule_addrs[2]);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		host_util_set_cpuid(i);

		ns_buffer_write(SLOT_NS, test_granule, 0U,
			       GRANULE_SIZE, (void *)granule_addrs[0]);

		/* Verify that the source has not been altered */
		MEMCMP_EQUAL((void *)granule_addrs[1],
			     (void *)granule_addrs[0],
			     (size_t)GRANULE_SIZE);
	}

}

TEST(slot_buffer, ns_buffer_write_TC3)
{
	uintptr_t granule_addrs[2];
	unsigned int cpu[2];
	long pattern[2];
	long val;
	union test_harness_cbs cb;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * for two random CPUs, map a random granule to their SLOT_NS, then
	 * copy different random data to it. Verify that the data from one
	 * CPU's SLOT_NS hasn't been leaked to the other's CPU SLOT_NS.
	 * This test helps validating that ns_buffer_write() handles the
	 * translation contexts properly.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/* Get two random granules, one for each CPU to test. */
	get_rand_granule_array(granule_addrs, 2U);

	/* Get two random CPUs where to run the tests. */
	do {
		cpu[0] = test_helpers_get_rand_in_range(0, MAX_CPUS - 1U);
		cpu[1] = test_helpers_get_rand_in_range(0, MAX_CPUS - 1U);
	} while (cpu[0] == cpu[1]);

	/* Get two different patterns of data to copy. */
	do {
		pattern[0] = (long)rand();
		pattern[1] = (long)rand();
	} while (pattern[0] == pattern[1]);

	/* Copy the patterns into the destination granules. */
	for (unsigned int i = 0U; i < 2U; i++) {
		host_util_set_cpuid(cpu[i]);

		ns_buffer_write(SLOT_NS, addr_to_granule(granule_addrs[i]), 0U,
				sizeof(long), (void*)&pattern[i]);
	}

	/*
	 * Verify that the granule for the first CPU doesn't contain the
	 * pattern on the second one.
	 */
	val = *(long *)granule_addrs[0];
	CHECK_FALSE(val == pattern[1]);

	/*
	 * Repeat the same check, this time with the second CPU.
	 */
	val = *(long *)granule_addrs[1];
	CHECK_FALSE(val == pattern[0]);

	/*
	 * ns_buffer_write() will assert if:
	 *	- The slot is not a non-secure one.
	 *	- The granule to read from is NULL.
	 *	- The size is not aligned to a byte size.
	 *	- The offset is not aligned to a byte size.
	 *	- The source is not aligned to a byte size.
	 *	- The offset + size overflows the granule size.
	 * So skip tests for these cases.
	 */
}

TEST(slot_buffer, ns_buffer_read_TC1)
{
	uintptr_t granule_addrs[3];
	struct granule *test_granule;
	union test_harness_cbs cb;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * For each CPU, map a random granule to NS_SLOT and copy random
	 * data into it. Then verify that the data is properly read and
	 * that the source has not been altered.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/*
	 * Get three random granules:
	 * granule_addrs[0]: To be used as src for read operations (SLOT_NS).
	 * granule_addrs[1]: Will be the dst granule for the ns_buffer_read
	 *		     operation.
	 * granule_addrs[2]: Just a zeroed granule to easy some tests.
	 */
	get_rand_granule_array(granule_addrs, 3U);

	/* Granule to test zeroes */
	(void)memset((void *)granule_addrs[2], 0, GRANULE_SIZE);

	test_granule = addr_to_granule(granule_addrs[0]);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		host_util_set_cpuid(i);

		/* Generate random data. */
		for (unsigned int j = 0U; j < GRANULE_SIZE/sizeof(int); j++) {
			*((int *)granule_addrs[0] + j) = rand();
		}

		/* Clean the dest granule */
		(void)memset((void *)granule_addrs[1], 0, GRANULE_SIZE);

		/*
		 * Read block by block, verifying that each copied block
		 * doesn't affect anything read before nor a block to be
		 * read yet.
		 */
		for (unsigned int j = 0U; j < GRANULE_BLOCKS; j++) {
			ns_buffer_read(SLOT_NS, test_granule,
					GRANULE_BLOCK_SIZE * j,
					GRANULE_BLOCK_SIZE,
					(void*)(granule_addrs[1] +
						(GRANULE_BLOCK_SIZE * j)));

			MEMCMP_EQUAL((void *)granule_addrs[1],
				     (void *)granule_addrs[0],
				     (size_t)((j + 1U) * GRANULE_BLOCK_SIZE));

			/*
			 * Verify than any block that has not been read yet
			 * is still all zeros.
			 */
			MEMCMP_EQUAL((void *)granule_addrs[2],
				     (void *)(granule_addrs[1] +
					((j + 1U) * GRANULE_BLOCK_SIZE)),
				     (GRANULE_BLOCKS - (j + 1U)) *
					GRANULE_BLOCK_SIZE);

		}
	}
}

TEST(slot_buffer, ns_buffer_read_TC2)
{
	uintptr_t granule_addrs[3];
	struct granule *test_granule;
	union test_harness_cbs cb;
	int val;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * For every CPU, verify that ns_buffer_read() does not alter the
	 * source.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/*
	 * Get three random granules:
	 * granule_addrs[0]: To be used as src for read operations (SLOT_NS).
	 * granule_addrs[1]: Will hold a copy of the src granule to compare.
	 * granule_addrs[2]: Destination granule.
	 */
	get_rand_granule_array(granule_addrs, 3U);

	/* Generate random data. */
	for (unsigned int j = 0U; j < GRANULE_SIZE/sizeof(int); j++) {
		val = rand();
		*((int *)granule_addrs[0] + j) = val;
		*((int *)granule_addrs[1] + j) = val;
	}

	test_granule = addr_to_granule(granule_addrs[0]);

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		host_util_set_cpuid(i);

		ns_buffer_read(SLOT_NS, test_granule, 0U,
			       GRANULE_SIZE, (void *)granule_addrs[2]);

		/* Verify that the source has not been altered */
		MEMCMP_EQUAL((void *)granule_addrs[1],
			     (void *)granule_addrs[0],
			     (size_t)GRANULE_SIZE);
	}

}

TEST(slot_buffer, ns_buffer_read_TC3)
{
	uintptr_t granule_addrs[2];
	unsigned int cpu[2];
	long dest[2];
	long val;
	union test_harness_cbs cb;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * for two random CPUs, map a random granule with random data to
	 * their SLOT_NS, then read the SLOT_NS on each CPU and ensure that
	 * the destination buffers contain the data from their CPU SLOT_NS
	 * only and no leak from the other CPU has happened.
	 * This test helps validating that ns_buffer_read() handles the
	 * translation contexts properly.
	 ******************************************************************/

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/* Get a random granule for each CPU to use. */
	get_rand_granule_array(granule_addrs, 2U);

	/* Get two random CPUs where to run the tests. */
	do {
		cpu[0] = test_helpers_get_rand_in_range(0, MAX_CPUS - 1U);
		cpu[1] = test_helpers_get_rand_in_range(0, MAX_CPUS - 1U);
	} while (cpu[0] == cpu[1]);

	/* Store random data at the beginning of each granule */
	*(long *)granule_addrs[0] = (long)rand();
	*(long *)granule_addrs[1] = (long)rand();

	/* Read the granules and store the result in dest */
	for (unsigned int i = 0U; i < 2U; i++) {
		host_util_set_cpuid(cpu[i]);

		ns_buffer_read(SLOT_NS, addr_to_granule(granule_addrs[i]), 0U,
			       sizeof(long), (void*)&dest[i]);
	}

	/*
	 * Verify that the dest granule for the first CPU doesn't contain
	 * the pattern for the second one.
	 */
	val = *(long *)granule_addrs[0];
	CHECK_FALSE(val == dest[1]);

	/*
	 * Repeat the same check, this time with the second CPU.
	 */
	val = *(long *)granule_addrs[1];
	CHECK_FALSE(val == dest[0]);

	/*
	 * ns_buffer_read() will assert if:
	 *	- The slot is not a non-secure one.
	 *	- The granule to read from is NULL.
	 *	- The size is not aligned to a byte size.
	 *	- The offset is not aligned to a byte size.
	 *	- The dest is not aligned to a byte size.
	 *	- The offset + size overflows the granule size.
	 * So skip tests for these cases.
	 */
}

TEST(slot_buffer, slot_buf_setup_xlat_TC1)
{
	/*
	 * slot_buf_setup_xlat() has already been used during initialization
	 * for all tests, so skip it.
	 */
}

TEST(slot_buffer, slot_buf_init_TC1)
{
	/*
	 * slot_buf_init() has already been used during initialization
	 * for all tests, so skip it.
	 */
}
