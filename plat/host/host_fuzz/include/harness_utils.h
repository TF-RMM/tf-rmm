/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HARNESS_UTILS_H
#define HARNESS_UTILS_H

#define FUZZ_PROT_LOG(...) INFO(__VA_ARGS__)

#define PACKET(packet_type, b, p) \
struct packet_type p = { 0 }; \
	if (test_buffer_get_data(&b, &p, sizeof(p)) < 0) { \
		return 0; \
	} \
LOG_ ## packet_type ## _FUNC(p)

#define PACKET_LOG(...)	printf(__VA_ARGS__)

struct test_buffer {
	const uint8_t *data;
	size_t length;
	size_t read_index;
};

int test_buffer_get_u8(struct test_buffer *b, uint8_t *val)
{
	if (b->read_index + sizeof(uint8_t) <= b->length) {
		*val = b->data[b->read_index++];
		return 0;
	} else {
		return (-1);
	}
}

int test_buffer_get_u16(struct test_buffer *b, uint16_t *val)
{
	if (b->read_index + sizeof(uint16_t) <= b->length) {
		*val = (uint16_t)b->data[b->read_index] +
		       ((uint16_t)b->data[b->read_index + 1] << 8);
		b->read_index += sizeof(*val);
		return 0;
	} else {
		return (-1);
	}
}

int test_buffer_get_u32(struct test_buffer *b, uint32_t *val)
{
	if (b->read_index + sizeof(uint32_t) <= b->length) {
		*val = (uint32_t)b->data[b->read_index] +
		       ((uint32_t)b->data[b->read_index + 1] << 8) +
		       ((uint32_t)b->data[b->read_index + 2] << 16) +
		       ((uint32_t)b->data[b->read_index + 3] << 24);
		b->read_index += sizeof(*val);
		return 0;
	} else {
		return (-1);
	}
}

int test_buffer_get_u64(struct test_buffer *b, uint64_t *val)
{
	if (b->read_index + sizeof(uint64_t) <= b->length) {
		*val = (uint64_t)b->data[b->read_index] +
		       ((uint64_t)b->data[b->read_index + 1] << 8) +
		       ((uint64_t)b->data[b->read_index + 2] << 16) +
		       ((uint64_t)b->data[b->read_index + 3] << 24) +
		       ((uint64_t)b->data[b->read_index + 4] << 32) +
		       ((uint64_t)b->data[b->read_index + 5] << 40) +
		       ((uint64_t)b->data[b->read_index + 6] << 48) +
		       ((uint64_t)b->data[b->read_index + 7] << 56);
		b->read_index += sizeof(*val);
		return 0;
	} else {
		return (-1);
	}
}

int test_buffer_get_data(struct test_buffer *b, void *data, size_t length)
{
	if (b->read_index + length <= b->length) {
		memcpy(data, &b->data[b->read_index], length);
		b->read_index += length;
		return 0;
	} else {
		return (-1);
	}
}

/*
 * Check whether the granule state at @addr matches the @expected_state.
 *
 * Returns:
 *	True if granule state at @addr matches the @expected_state.
 *
 *	False if any of:
 *	- @addr is not aligned to the size of a granule.
 *	- @addr is out of range.
 *	- if the state of the granule at @addr is not @expected_state.
 * TODO: Move to granule.h?
 */
static inline bool granule_state_is(unsigned long addr, unsigned char expected_state)
{
	struct granule *g_p = find_granule(addr);
	if (!g_p) {
		return false;
	}
	return granule_unlocked_state(g_p) == expected_state;
}

/*
 * Print actual and expected granule state if @addr is valid.
 * Useful only in persistent mode.
 */
void debug_state(void *addr, unsigned short expected_state)
{
#ifndef PERSISTENT_MODE
	const char *g_state_str[] = {
		"GRANULE_STATE_NS",
		"GRANULE_STATE_DELEGATED",
		"GRANULE_STATE_RD",
		"GRANULE_STATE_REC",
		"GRANULE_STATE_REC_AUX",
		"GRANULE_STATE_DATA",
		"GRANULE_STATE_RTT",
		"GRANULE_STATE_PDEV",
		"GRANULE_STATE_PDEV_AUX",
		"GRANULE_STATE_VDEV",
		"GRANULE_STATE_VDEV_AUX"
	};

	struct granule *g_addr = find_granule((uintptr_t)addr);
	if (g_addr == NULL) {
		INFO("%p: Granule address is NULL\n", addr);
		return;
	}

	const unsigned short actual_state = granule_unlocked_state(g_addr);
	const char *actual_state_str = g_state_str[actual_state];
	const bool state_valid = actual_state == expected_state;

	INFO("%p: %s =? %s >> %hhu\n",
	     g_addr, actual_state_str, g_state_str[expected_state], state_valid);

#else /* PERSISTENT_MODE */
	return;
#endif /* PERSISTENT_MODE */
}

/*
 * Break switch if granule is not in expected state.
 */
#ifdef VALIDATE_GRANS
#define validate_state(g, e)	({			\
	if (!granule_state_is((uintptr_t)(g), (e))) {	\
		debug_state((g), (e));			\
		break;					\
	}						\
})
#else /* VALIDATE_GRANS */
#define validate_state(g, e)
#endif /* VALIDATE_GRANS */

#endif /* HARNESS_UTILS_H */
