/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FIRME_H
#define FIRME_H

#include <rmm_el3_ifc.h>
#include <smc.h>
#include <stdbool.h>

/* FIRME SMC return codes */
#define FIRME_SUCCESS			UL(0)
#define FIRME_NOT_SUPPORTED		UL(-1)
#define FIRME_INVALID_PARAMETERS	UL(-2)
#define FIRME_ABORTED			UL(-3)
#define FIRME_INCOMPLETE		UL(-4)
#define FIRME_DENIED			UL(-5)
#define FIRME_BUSY			UL(-6)
#define FIRME_OP_CONFLICT		UL(-7)
#define FIRME_EXISTS			UL(-8)
#define FIRME_NO_ENTRY			UL(-9)
#define FIRME_NO_MEMORY			UL(-10)
#define FIRME_BAD_DATA			UL(-11)

/* GPI values known to RMM */
#define GPT_GPI_NS			U(0x9)
#define GPT_GPI_REALM			U(0xB)

/* Supported FIRME function IDs*/
#define SMC_FIRME_BASE_VERSION		SMC64_STD_FID(FIRME, U(0)) /* FID 0xC400 0400 */
#define SMC_FIRME_BASE_FEATURES		SMC64_STD_FID(FIRME, U(1)) /* FID 0xC400 0401 */
#define SMC_FIRME_GM_GPI_SET		SMC64_STD_FID(FIRME, U(2)) /* FID 0xC400 0402 */
#define SMC_FIRME_IDE_KEYSET_PROG	SMC64_STD_FID(FIRME, U(3)) /* FID 0xC400 0403 */
#define SMC_FIRME_IDE_KEYSET_GO		SMC64_STD_FID(FIRME, U(4)) /* FID 0xC400 0404 */
#define SMC_FIRME_IDE_KEYSET_STOP	SMC64_STD_FID(FIRME, U(5)) /* FID 0xC400 0405 */
#define SMC_FIRME_MECID_REFRESH		SMC64_STD_FID(FIRME, U(7)) /* FID 0xC400 0407 */

/* FIRME_VERSION definitions */

#define FIRME_VERSION_MAJOR_SHIFT	U(16)
#define FIRME_VERSION_MINOR_SHIFT	U(0)
#define FIRME_VERSION_MAJOR_MASK	U(0x3FFF)
#define FIRME_VERSION_MINOR_MASK	U(0xFFFF)
#define FIRME_VERSION_MAJOR(v)		(((v) >> FIRME_VERSION_MAJOR_SHIFT) & \
						FIRME_VERSION_MAJOR_MASK)
#define FIRME_VERSION_MASK		U((FIRME_VERSION_MAJOR_MASK << \
						FIRME_VERSION_MAJOR_SHIFT) | \
						(FIRME_VERSION_MINOR_MASK << \
						FIRME_VERSION_MINOR_SHIFT))

/* FIRME service IDs */
#define FIRME_BASE_SERVICE_ID			U(0)
#define FIRME_GM_SERVICE_ID			U(1)
#define FIRME_IDE_SERVICE_ID			U(2)
#define FIRME_MECID_SERVICE_ID			U(3)
#define FIRME_NUM_SERVICES			U(4)

/* Base feature register definitions. */
#define FIRME_BASE_FR1_SVC_BIT(svc_id)		UL(0x1UL << UL(16U + ((svc_id) - 1U)))

/* GM service feature register definitions */
#define FIRME_GM_FR0_MASK			UL(0x3)
#define FIRME_GM_FR0_GPI_SET_BIT		UL(0x1)

/* GPI_SET definitions */
#define FIRME_GPI_SET_ATTR_TARGET_GPI_MASK	U(0xF)

/* Supported FIRME service versions */
#define SUPPORTED_FIRME_BASE_VERSION	0x10000U /* 1.0 */
#define SUPPORTED_FIRME_GM_VERSION	0x10000U /* 1.0 */
#define SUPPORTED_FIRME_IDE_VERSION	0x10000U /* 1.0 */
#define SUPPORTED_FIRME_MECID_VERSION	0x10000U /* 1.0 */

/* IDE KM service feature register definitions. */
#define FIRME_IDE_FR0_MASK		UL(0x7)
#define FIRME_IDE_FR0_KEYSET_PROG_BIT	BIT(0)
#define FIRME_IDE_FR0_KEYSET_GO_BIT	BIT(1)
#define FIRME_IDE_FR0_KEYSET_STOP_BIT	BIT(2)

/* IDE KM only has feature register 0. */
#define FIRME_IDE_FR0_DEFAULT		(FIRME_IDE_FR0_KEYSET_PROG_BIT	| \
					 FIRME_IDE_FR0_KEYSET_GO_BIT	| \
					 FIRME_IDE_FR0_KEYSET_STOP_BIT)

/* KeySet ID */
#define FIRME_KEYSET_ID_KEYSET_SHIFT			U(0)
#define FIRME_KEYSET_ID_KEYSET_WIDTH			U(1)
#define FIRME_KEYSET_ID_DIRECTION_SHIFT			U(1)
#define FIRME_KEYSET_ID_DIRECTION_WIDTH			U(1)
#define FIRME_KEYSET_ID_SUBSTREAM_ID_SHIFT		U(2)
#define FIRME_KEYSET_ID_SUBSTREAM_ID_WIDTH		U(4)
#define FIRME_KEYSET_ID_STREAM_ID_SHIFT			U(6)
#define FIRME_KEYSET_ID_STREAM_ID_WIDTH			U(8)
#define FIRME_KEYSET_ID_ROOTPORT_ID_SHIFT		U(14)
#define FIRME_KEYSET_ID_ROOTPORT_ID_WIDTH		U(16)
#define FIRME_KEYSET_ID_SEGMENT_NUMBER_SHIFT		U(30)
#define FIRME_KEYSET_ID_SEGMENT_NUMBER_WIDTH		U(8)

/* Construct Keyset ID from key set, key direction, key substream, stream id */
#define FIRME_IDE_MAKE_KEYSET_ID(_kset, _dir, _substream, _stream, _rp, _seg) \
	(INPLACE(FIRME_KEYSET_ID_KEYSET, (_kset))			| \
	 INPLACE(FIRME_KEYSET_ID_DIRECTION, (_dir))			| \
	 INPLACE(FIRME_KEYSET_ID_SUBSTREAM_ID, (_substream))		| \
	 INPLACE(FIRME_KEYSET_ID_STREAM_ID, (_stream))			| \
	 INPLACE(FIRME_KEYSET_ID_ROOTPORT_ID, (_rp))			| \
	 INPLACE(FIRME_KEYSET_ID_SEGMENT_NUMBER, (_seg)))

#define DEFINE_FIRME_ABI_QUERY(SVC_ID, abi, ABI) 			\
static inline bool firme_supports_ ## abi(void) 			\
{									\
	return (get_present_abis(FIRME_ ## SVC_ID ## _SERVICE_ID)	\
		& FIRME_ ## SVC_ID ## _FR0_ ## ABI ## _BIT) != 0UL;	\
}

#define MEC_REFRESH_REASON_REALM_CREATE		U(0)
#define MEC_REFRESH_REASON_REALM_DESTROY	U(1)

#define MEC_PARAM_MECID_SHIFT			U(32)
#define MEC_PARAM_MECID_MASK			U(0xFFFF)

#define FIRME_MECID_FEATURE_REG_COUNT		U(2)
#define FIRME_MECID_FR0_MEC_REFRESH_BIT	BIT(0)
#define FIRME_MECID_FR0_MASK \
	FIRME_MECID_FR0_MEC_REFRESH_BIT
#define FIRME_MECID_FR1_COMMON_MECID_WIDTH_BITS_SHIFT	U(0)
#define FIRME_MECID_FR1_COMMON_MECID_WIDTH_BITS_WIDTH	UL(4)

/* This helper converts FIRME status to RMM EL3 interface status */
static inline int firme_errno_to_rmm_errno(uint64_t firme_errno)
{
	int rc;

	switch (firme_errno) {
	case FIRME_SUCCESS:
		rc = E_RMM_OK;
		break;
	case FIRME_NOT_SUPPORTED:
		rc = E_RMM_NOTSUP;
		break;
	case FIRME_INVALID_PARAMETERS:
		rc = E_RMM_INVAL;
		break;
	case FIRME_BUSY:
		rc = E_RMM_BUSY;
		break;
	case FIRME_DENIED:
		rc = E_RMM_DENIED;
		break;
	default:
		rc = E_RMM_UNK;
		break;
	}

	return rc;
}

/* Public APIs */

bool firme_init(void);
uint32_t firme_get_version(unsigned char service_id);
unsigned long get_present_abis(unsigned int service_id);
unsigned long firme_get_feature_register(unsigned int service_id,
					 unsigned int feature_reg_idx);

/* Helper functions to query service ABIs */
DEFINE_FIRME_ABI_QUERY(GM, gpi_set, GPI_SET)

DEFINE_FIRME_ABI_QUERY(IDE, keyset_prog, KEYSET_PROG)
DEFINE_FIRME_ABI_QUERY(IDE, keyset_go, KEYSET_GO)
DEFINE_FIRME_ABI_QUERY(IDE, keyset_stop, KEYSET_STOP)

DEFINE_FIRME_ABI_QUERY(MECID, mec_refresh, MEC_REFRESH)

static inline bool firme_supports_ide_service(void)
{
	return (firme_supports_keyset_prog() &&
		firme_supports_keyset_go() &&
		firme_supports_keyset_stop());
}
#endif /* FIRME_H */
