/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FIRME_H
#define FIRME_H

#include <smc.h>
#include <stdbool.h>

/* FIRME SMC return codes */
#define FIRME_SUCCESS			UL(0)
#define FIRME_NOT_SUPPORTED		UL(-1)
#define FIRME_INVALID_PARAMETERS	UL(-2)
#define FIRME_ABORTED			UL(-3)
#define FIRME_INCOMPLETE		UL(-4)
#define FIRME_DENIED			UL(-5)
#define FIRME_RETRY			UL(-6)
#define FIRME_IN_PROGRESS		UL(-7)
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
#define FIRME_NUM_SERVICES			U(2)

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

#define DEFINE_FIRME_ABI_QUERY(SVC_ID, abi, ABI) 			\
static inline bool firme_supports_ ## abi(void) 			\
{									\
	return (get_present_abis(FIRME_ ## SVC_ID ## _SERVICE_ID)	\
		& FIRME_ ## SVC_ID ## _FR0_ ## ABI ## _BIT) != 0UL;	\
}

/* Public APIs */

bool firme_init(void);
uint32_t firme_get_version(unsigned char service_id);
unsigned long get_present_abis(unsigned int service_id);

/* Helper functions to query service ABIs */
DEFINE_FIRME_ABI_QUERY(GM, gpi_set, GPI_SET)

#endif /* FIRME_H */
