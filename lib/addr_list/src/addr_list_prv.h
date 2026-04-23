/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef __ADDR_LIST_PRV_H__
#define __ADDR_LIST_PRV_H__

#include <assert.h>
#include <utils_def.h>
#include <xlat_defs.h>

/*
 * Returns true if the given size is a valid XLAT block size, i.e. it equals
 * XLAT_BLOCK_SIZE(level) for some RTT level in [0, XLAT_TABLE_LEVEL_MAX].
 * The SZ field in an RmiAddrRangeDesc is 2 bits wide, so there are exactly
 * four valid block sizes.
 */
#define IS_VALID_XLAT_BLOCK_SIZE(size)					\
	(((size) == XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX))	||	\
	 ((size) == XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX - 1))	||	\
	 ((size) == XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX - 2))	||	\
	 ((size) == XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX - 3)))

/* RmiAddrRangeDesc4KB type definitons */
#define ADDR_RDESC_4K_SZ_SHIFT				(0UL)
#define ADDR_RDESC_4K_SZ_WIDTH				(2UL)
#define ADDR_RDESC_4K_CNT_SHIFT				(2UL)
#define ADDR_RDESC_4K_CNT_WIDTH				(10UL)
#define ADDR_RDESC_4K_ADDR_SHIFT			(12UL)
#define ADDR_RDESC_4K_ADDR_WIDTH			(40UL)
#define ADDR_RDESC_4K_ST_SHIFT				(63UL)
#define ADDR_RDESC_4K_ST_WIDTH				(1UL)

/* RmiAddrRangeDesc16KB type definitons */
#define ADDR_RDESC_16K_SZ_SHIFT				(0UL)
#define ADDR_RDESC_16K_SZ_WIDTH				(2UL)
#define ADDR_RDESC_16K_CNT_SHIFT			(2UL)
#define ADDR_RDESC_16K_CNT_WIDTH			(12UL)
#define ADDR_RDESC_16K_ADDR_SHIFT			(14UL)
#define ADDR_RDESC_16K_ADDR_WIDTH			(38UL)
#define ADDR_RDESC_16K_ST_SHIFT				(63UL)
#define ADDR_RDESC_16K_ST_WIDTH				(1UL)

/* RmiAddrRangeDesc64KB type definitons */
#define ADDR_RDESC_64K_SZ_SHIFT				(0UL)
#define ADDR_RDESC_64K_SZ_WIDTH				(2UL)
#define ADDR_RDESC_64K_CNT_SHIFT			(2UL)
#define ADDR_RDESC_64K_CNT_WIDTH			(14UL)
#define ADDR_RDESC_64K_ADDR_SHIFT			(16UL)
#define ADDR_RDESC_64K_ADDR_WIDTH			(36UL)
#define ADDR_RDESC_64K_ST_SHIFT				(63UL)
#define ADDR_RDESC_64K_ST_WIDTH				(1UL)

/* Set of macros to access fields for RmiAddrRangeDesc of any granule size. */
#define ADDR_RDESC_GET_ADDR(_gsz, _desc)			\
	(EXTRACT(ADDR_RDESC_##_gsz##_ADDR, (_desc)) << (ADDR_RDESC_##_gsz##_ADDR_SHIFT))
#define ADDR_RDESC_GET_ADDR_MASK(_gsz)				\
	(MASK(ADDR_RDESC_##_gsz##_ADDR))
#define ADDR_RDESC_GET_CNT(_gsz, _desc)				\
	EXTRACT(ADDR_RDESC_##_gsz##_CNT, (_desc))
#define ADDR_RDESC_GET_CNT_MASK(_gsz)				\
	(MASK(ADDR_RDESC_##_gsz##_CNT))
#define ADDR_RDESC_GET_SZ(_gsz, _desc)				\
	EXTRACT(ADDR_RDESC_##_gsz##_SZ, (_desc))
#define ADDR_RDESC_GET_SZ_MASK(_gsz)				\
	(MASK(ADDR_RDESC_##_gsz##_SZ))
#define ADDR_RDESC_GET_ST(_gsz, _desc)				\
	EXTRACT(ADDR_RDESC_##_gsz##_ST, (_desc))
#define ADDR_RDESC_GET_ST_MASK(_gsz)				\
	(MASK(ADDR_RDESC_##_gsz##_ST))

#define ADDR_RDESC_SET_ADDR(_gsz, _addr)			\
	INPLACE(ADDR_RDESC_##_gsz##_ADDR, ((_addr) >> (ADDR_RDESC_##_gsz##_ADDR_SHIFT)))
#define ADDR_RDESC_SET_CNT(_gsz, _cnt)				\
	INPLACE(ADDR_RDESC_##_gsz##_CNT, (_cnt))
#define ADDR_RDESC_SET_SZ(_gsz, _sz)				\
	INPLACE(ADDR_RDESC_##_gsz##_SZ, (_sz))
#define ADDR_RDESC_SET_ST(_gsz, _st)				\
	INPLACE(ADDR_RDESC_##_gsz##_ST, (_st))

#define MAX_BLOCK_CNT(_gsz)					\
	((1UL << (ADDR_RDESC_##_gsz##_CNT_WIDTH)) - 1UL)

#define ADDR_RDESC_4K_GET_ADDR(_desc)		ADDR_RDESC_GET_ADDR(4K, _desc)
#define ADDR_RDESC_4K_GET_CNT(_desc)		ADDR_RDESC_GET_CNT(4K, _desc)
#define ADDR_RDESC_4K_GET_SZ(_desc)		ADDR_RDESC_GET_SZ(4K, _desc)
#define ADDR_RDESC_4K_GET_ST(_desc)		ADDR_RDESC_GET_ST(4K, _desc)
#define ADDR_RDESC_4K_SET_ADDR(_addr)		ADDR_RDESC_SET_ADDR(4K, _addr)
#define ADDR_RDESC_4K_SET_CNT(_cnt)		ADDR_RDESC_SET_CNT(4K, _cnt)
#define ADDR_RDESC_4K_SET_SZ(_sz)		ADDR_RDESC_SET_SZ(4K, _sz)
#define ADDR_RDESC_4K_SET_ST(_st)		ADDR_RDESC_SET_ST(4K, _st)
#define MAX_BLOCK_CNT_4K			MAX_BLOCK_CNT(4K)

#define ADDR_RDESC_16K_GET_ADDR(_desc)		ADDR_RDESC_GET_ADDR(16K, _desc)
#define ADDR_RDESC_16K_GET_CNT(_desc)		ADDR_RDESC_GET_CNT(16K, _desc)
#define ADDR_RDESC_16K_GET_SZ(_desc)		ADDR_RDESC_GET_SZ(16K, _desc)
#define ADDR_RDESC_16K_GET_ST(_desc)		ADDR_RDESC_GET_ST(16K, _desc)
#define ADDR_RDESC_16K_SET_ADDR(_addr)		ADDR_RDESC_SET_ADDR(16K, _addr)
#define ADDR_RDESC_16K_SET_CNT(_cnt)		ADDR_RDESC_SET_CNT(16K, _cnt)
#define ADDR_RDESC_16K_SET_SZ(_sz)		ADDR_RDESC_SET_SZ(16K, _sz)
#define ADDR_RDESC_16K_SET_ST(_st)		ADDR_RDESC_SET_ST(16K, _st)
#define MAX_BLOCK_CNT_16K			MAX_BLOCK_CNT(16K)

#define ADDR_RDESC_64K_GET_ADDR(_desc)		ADDR_RDESC_GET_ADDR(64K, _desc)
#define ADDR_RDESC_64K_GET_CNT(_desc)		ADDR_RDESC_GET_CNT(64K, _desc)
#define ADDR_RDESC_64K_GET_SZ(_desc)		ADDR_RDESC_GET_SZ(64K, _desc)
#define ADDR_RDESC_64K_GET_ST(_desc)		ADDR_RDESC_GET_ST(64K, _desc)
#define ADDR_RDESC_64K_SET_ADDR(_addr)		ADDR_RDESC_SET_ADDR(64K, _addr)
#define ADDR_RDESC_64K_SET_CNT(_cnt)		ADDR_RDESC_SET_CNT(64K, _cnt)
#define ADDR_RDESC_64K_SET_SZ(_sz)		ADDR_RDESC_SET_SZ(64K, _sz)
#define ADDR_RDESC_64K_SET_ST(_st)		ADDR_RDESC_SET_ST(64K, _st)
#define MAX_BLOCK_CNT_64K			MAX_BLOCK_CNT(64K)

/* Only 4KB granules are supported at the moment */
/*
 * @TODO: Use RMM Global configuration data to determine configured
 * granule size.
 */
static inline unsigned long get_addr_from_desc(unsigned long desc)
{
	return ADDR_RDESC_4K_GET_ADDR(desc);
}

static inline unsigned long get_addr_mask(void)
{
	return ADDR_RDESC_GET_ADDR_MASK(4K);
}

static inline unsigned long get_cnt_from_desc(unsigned long desc)
{
	return ADDR_RDESC_4K_GET_CNT(desc);
}

static inline unsigned long get_cnt_mask(void)
{
	return ADDR_RDESC_GET_CNT_MASK(4K);
}

static inline unsigned long get_sz_mask(void)
{
	return ADDR_RDESC_GET_SZ_MASK(4K);
}

static inline unsigned long get_st_from_desc(unsigned long desc)
{
	return ADDR_RDESC_4K_GET_ST(desc);
}

static inline unsigned long get_max_block_cnt(void)
{
	return MAX_BLOCK_CNT_4K;
}

static inline unsigned long get_sz_from_desc(unsigned long desc)
{
	return ADDR_RDESC_4K_GET_SZ(desc);
}

static inline unsigned long set_addr_in_desc(unsigned long desc, unsigned long addr)
{
	unsigned long new_desc = desc & ~get_addr_mask();

	return new_desc | ADDR_RDESC_4K_SET_ADDR(addr);
}

static inline unsigned long set_cnt_in_desc(unsigned long desc, unsigned long cnt)
{
	unsigned long new_desc = desc & ~get_cnt_mask();

	return new_desc | ADDR_RDESC_4K_SET_CNT(cnt);
}

static inline unsigned long set_sz_in_desc(unsigned long desc, unsigned long sz)
{
	unsigned long new_desc = desc & ~get_sz_mask();

	return new_desc | ADDR_RDESC_4K_SET_SZ(sz);
}

static inline unsigned long set_st_in_desc(unsigned long desc, unsigned long st)
{
	unsigned long new_desc = desc & ~ADDR_RDESC_GET_ST_MASK(4K);

	return new_desc | ADDR_RDESC_4K_SET_ST(st);
}

static inline unsigned int max_block_count(void)
{
	return (unsigned int)MAX_BLOCK_CNT_4K;
}

static unsigned long increment_block_count(unsigned long desc)
{
	assert(desc != 0UL);
	assert(get_cnt_from_desc(desc) < max_block_count());

	return (desc + (1UL << ADDR_RDESC_4K_CNT_SHIFT));
}

static unsigned long decrement_block_count(unsigned long desc)
{
	assert(desc != 0UL);
	assert(get_cnt_from_desc(desc) > 0UL);

	return (desc - (1UL << ADDR_RDESC_4K_CNT_SHIFT));
}

#endif /* __ADDR_LIST_PRV_H__ */
