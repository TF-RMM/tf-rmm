/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <debug.h>
#include <dev_assign_private.h>
#include <el0_app_helpers.h>
#include <rme_dvsec.h>
#include <sizes.h>

#define PCIE_EXTRACT_BDF_BUS(bdf)	(((bdf) >> 8U) & 0xFFU)
#define PCIE_EXTRACT_BDF_DEV(bdf)	(((bdf) >> 3U) & 0x1FU)
#define PCIE_EXTRACT_BDF_FUNC(bdf)	((bdf) & 0x7U)

/* PCI Express Extended Configuration Space */
#define PCIE_CFG_SIZE			SZ_4K

/* ECAM size is implicitly 256MB */
#define PCIE_ECAM_SIZE			(UL(256) * SZ_1M)

/* PCIe Extended Capability start offset */
#define PCIE_ECAP_START			U(0x100)
#define PCIE_ECAP_END			U(0xFFC)

#define PCIE_MAX_BUS			U(256)
#define PCIE_MAX_DEV			U(32)
#define PCIE_MAX_FUNC			U(8)

/*
 * Check if the DVSEC header matches RME Sys Arch spec
 *
 * DVSEC_REVISION must be 0
 * DVSEC_VENDOR_ID must be Arm
 * DVSEC_ID must be RME_DA
 */
static bool is_dvsec_arm_rme_da(struct dev_assign_info *info,
				unsigned long rp_ecam_addr,
				unsigned int dvsec_offset)
{
	uint32_t hdr1 = 0U;
	uint32_t hdr2 = 0U;

	if (el0_app_service_call(APP_SERVICE_NS_MMIO_READ_4,
	    rp_ecam_addr, (unsigned long)dvsec_offset + PCIE_ECAP_DVSEC_HDR1_OFFSET, 0, 0) == 0U) {
		return false;
	}
	assert(info->shared_buf != NULL);
	hdr1 = *((uint32_t *)info->shared_buf);

	if (el0_app_service_call(APP_SERVICE_NS_MMIO_READ_4,
	    rp_ecam_addr, (unsigned long)dvsec_offset + PCIE_ECAP_DVSEC_HDR2_OFFSET, 0, 0) == 0U) {
		return false;
	}
	hdr2 = *((uint32_t *)info->shared_buf);

	if ((EXTRACT(DVSEC_HDR1_VENDOR_ID, hdr1) == DVSEC_VENDOR_ID_ARM) &&
	    (EXTRACT(DVSEC_HDR1_REVISION, hdr1) == DVSEC_REVISION_0) &&
	    (EXTRACT(DVSEC_HDR2_DVSEC_ID, hdr2) == DVSEC_ID_RME_DA)) {
		return true;
	}

	return false;
}

/*
 * Find DVSEC extended capability and check if the header, revision are
 * expected as mentioned in RME System Architecture.
 */
static unsigned int pcie_find_arm_dvsec(struct dev_assign_info *info,
					unsigned long rp_ecam_addr)
{
	uint32_t ech;
	unsigned int dvsec_offset;
	uint16_t next_cap_offset;

	dvsec_offset = PCIE_ECAP_START;
	do {
		assert((dvsec_offset + sizeof(ech)) < PCIE_CFG_SIZE);

		if (el0_app_service_call(APP_SERVICE_NS_MMIO_READ_4,
		    rp_ecam_addr, dvsec_offset, 0, 0) == 0U) {
			break;
		}
		assert(info->shared_buf != NULL);
		ech = *((uint32_t *)info->shared_buf);

		/* Check for PCIE_ECH_CAP_VER_1 as well? */
		if ((EXTRACT(PCIE_ECH_ID, ech) == PCIE_ECH_ID_DVSEC) &&
		    is_dvsec_arm_rme_da(info, rp_ecam_addr, dvsec_offset)) {
			return dvsec_offset;
		}

		next_cap_offset = (uint16_t)EXTRACT(PCIE_ECH_NEXT_CAP_OFFSET, ech);
		dvsec_offset += next_cap_offset;
	} while ((next_cap_offset != 0U) && (dvsec_offset < PCIE_ECAP_END));

	return 0U;
}

/*
 * Find Root Port Extended Capability DVSEC and check attributes matches RME SA
 */
int dvsec_init(struct dev_assign_info *info)
{
	unsigned long rp_ecam_addr;
	unsigned int rp_dvsec_offset;

	rp_ecam_addr = info->ecam_addr +
		(((unsigned long)PCIE_EXTRACT_BDF_BUS(info->rp_id) * PCIE_MAX_DEV *
		  PCIE_MAX_FUNC * PCIE_CFG_SIZE) +
		 ((unsigned long)PCIE_EXTRACT_BDF_DEV(info->rp_id) * PCIE_MAX_FUNC *
		  PCIE_CFG_SIZE) +
		 ((unsigned long)PCIE_EXTRACT_BDF_FUNC(info->rp_id) * PCIE_CFG_SIZE));

	if ((info->ecam_addr + PCIE_ECAM_SIZE) < (rp_ecam_addr + PCIE_CFG_SIZE)) {
		ERROR("%s: failed. 0x%lx not in ecam\n", __func__, rp_ecam_addr);
		return -1;
	}

	rp_dvsec_offset = pcie_find_arm_dvsec(info, rp_ecam_addr);
	if (rp_dvsec_offset == 0U) {
		ERROR("%s: failed. no ARM DVSEC found\n", __func__);
		return -1;
	}

	INFO("%s: RP ECAM 0x%lx, DVSEC offset 0x%x\n",
		__func__, rp_ecam_addr, rp_dvsec_offset);
	info->rp_ecam_addr = rp_ecam_addr;
	info->rp_dvsec_offset = rp_dvsec_offset;

	return 0;
}

/*
 * Deinit DVSEC info
 */
int dvsec_deinit(struct dev_assign_info *info)
{
	info->rp_ecam_addr = 0UL;
	info->rp_dvsec_offset = 0U;

	return 0;
}

static int _dvsec_stream_lock(struct dev_assign_info *info, bool to_lock)
{
	uint32_t ctl2_reg = 0U;
	uint32_t ctl2_off;

	if (info->rp_ecam_addr == 0UL) {
		return -1;
	}

	ctl2_off = info->rp_dvsec_offset + PCIE_ECAP_DVSEC_RME_DA_CTL_REG2_OFFSET;

	/* Read existing control register2 and lock stream id */

	if (el0_app_service_call(APP_SERVICE_NS_MMIO_READ_4,
	    info->rp_ecam_addr, ctl2_off, 0, 0) == 0U) {
		ERROR("dvsec_stream_%slock: ctl2 read failed\n",
		      to_lock ? "" : "un");
		return -1;
	}
	assert(info->shared_buf != NULL);
	ctl2_reg = *((uint32_t *)info->shared_buf);

	assert(info->ide_sid < 32U);
	if (to_lock) {
		ctl2_reg |= (U(1) << info->ide_sid);
	} else {
		ctl2_reg &= ~(U(1) << info->ide_sid);
	}

	if (el0_app_service_call(APP_SERVICE_REALM_MMIO_WRITE_4,
	    info->rp_ecam_addr, ctl2_off, ctl2_reg, 0) == 0U) {
		ERROR("dvsec_stream_%slock: failed\n", to_lock ? "" : "un");
		return -1;
	}

	INFO("dvsec_stream_%slock: done\n", to_lock ? "" : "un");
	return 0;
}

/* Lock stream in RME_DA control register */
int dvsec_stream_lock(struct dev_assign_info *info)
{
	return _dvsec_stream_lock(info, true);
}

/* Unlock stream in RME_DA control register */
int dvsec_stream_unlock(struct dev_assign_info *info)
{
	return _dvsec_stream_lock(info, false);
}

/* Check if IDE stream in locked state */
bool dvsec_is_stream_locked(struct dev_assign_info *info)
{
	uint32_t ctl2_reg = 0U;
	uint32_t ctl2_off;

	assert(info->rp_ecam_addr != 0UL);

	ctl2_off = info->rp_dvsec_offset + PCIE_ECAP_DVSEC_RME_DA_CTL_REG2_OFFSET;

	/* Read existing control register2 and lock stream id */
	if (el0_app_service_call(APP_SERVICE_NS_MMIO_READ_4,
	    info->rp_ecam_addr, ctl2_off, 0, 0) == 0U) {
		ERROR("%s: ctl2 read failed\n", __func__);
		return false;
	}
	assert(info->shared_buf != NULL);
	ctl2_reg = *((uint32_t *)info->shared_buf);

	if ((ctl2_reg & (U(1) << info->ide_sid)) != 0U) {
		INFO("%s: returning true, ide_sid is %lu\n", __func__, info->ide_sid);
		return true;
	}

	INFO("%s: returning false, ide_sid is %lu\n", __func__, info->ide_sid);
	return false;
}

static int _dvsec_tdisp_enable(struct dev_assign_info *info)
{
	uint32_t ctl1_reg = 0U;
	uint32_t ctl1_off;

	if (info->rp_ecam_addr == 0UL) {
		return -1;
	}

	ctl1_off = info->rp_dvsec_offset + PCIE_ECAP_DVSEC_RME_DA_CTL_REG1_OFFSET;

	/* Read existing control register and enable TDISP */
	if (el0_app_service_call(APP_SERVICE_NS_MMIO_READ_4,
	    info->rp_ecam_addr, ctl1_off, 0, 0) == 0U) {
		ERROR("%s: ctl1 read failed\n", __func__);
		return -1;
	}
	assert(info->shared_buf != NULL);
	ctl1_reg = *((uint32_t *)info->shared_buf);

	ctl1_reg |= (uint32_t)INPLACE(DVSEC_RMEDA_CTL_REG1_TDISP_EN,
					RME_DA_TDISP_ENABLE);

	if (el0_app_service_call(APP_SERVICE_REALM_MMIO_WRITE_4,
	    info->rp_ecam_addr, ctl1_off, ctl1_reg, 0) == 0U) {
		ERROR("%s: TDISP enable/disable failed\n", __func__);
		return -1;
	}

	return 0;
}

/* Enable TDISP in RME_DA control register2 */
int dvsec_tdisp_enable(struct dev_assign_info *info)
{
	return _dvsec_tdisp_enable(info);
}
