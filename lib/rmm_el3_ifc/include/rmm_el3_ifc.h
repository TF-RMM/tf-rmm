/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_IFC_H
#define RMM_EL3_IFC_H

#include <sizes.h>
#include <smc.h>

#ifndef __ASSEMBLER__
#include <stddef.h>
#endif

/*************************************
 * SMC codes for the EL3-RMM interface
 *************************************/
					/* 0x1B0 - 0x1B3 */
#define SMC_RMM_GTSI_DELEGATE		SMC64_STD_FID(RMM_EL3, U(0))
#define SMC_RMM_GTSI_UNDELEGATE		SMC64_STD_FID(RMM_EL3, U(1))

					/* 0x1B2 - 0x1B3 */
#define SMC_RMM_GET_REALM_ATTEST_KEY	SMC64_STD_FID(RMM_EL3, U(2))
#define SMC_RMM_GET_PLAT_TOKEN		SMC64_STD_FID(RMM_EL3, U(3))

					/* 0x1CF */
#define SMC_RMM_BOOT_COMPLETE		SMC64_STD_FID(RMM_EL3, U(0x1F))

/* SMC_RMM_BOOT_COMPLETE return codes */
#define E_RMM_BOOT_SUCCESS				(0)
#define E_RMM_BOOT_UNKNOWN_ERROR			(-1)
#define E_RMM_BOOT_VERSION_MISMATCH			(-2)
#define E_RMM_BOOT_CPUS_OUT_OF_RANGE			(-3)
#define E_RMM_BOOT_CPU_ID_OUT_OF_RANGE			(-4)
#define E_RMM_BOOT_INVALID_SHARED_POINTER		(-5)
#define E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED	(-6)
#define E_RMM_BOOT_MANIFEST_DATA_ERROR			(-7)

/************************
 * Version related macros
 ************************/

/*
 * Boot Interface version encoding:
 *	- Bit[31] RES0
 *	- Bits [30:16] Major version
 *	- Bits [15:0] Minor version
 */
#define RMM_EL3_IFC_GET_VERS_MAJOR(_version)				\
				(((_version) >> 16) & 0x7FFF)
#define RMM_EL3_IFC_GET_VERS_MINOR(_version)				\
				((_version) & 0xFFFF)
#define RMM_EL3_IFC_SUPPORTED_VERSION (					\
		(((RMM_EL3_IFC_VERS_MAJOR) & 0x7FFF) << 16) |		\
		((RMM_EL3_IFC_VERS_MINOR) & 0xFFFF)			\
	)

/*
 * The Major version value for the Boot Interface supported by this
 * implementation of RMM.
 */
#define RMM_EL3_IFC_VERS_MAJOR		(U(0))

/*
 * The Minor version value for the Boot interface supported by this
 * implementation of RMM.
 */
#define RMM_EL3_IFC_VERS_MINOR		(U(1))

/*
 * The Major version value for the Boot Manifest supported by this
 * implementation of RMM.
 */
#define RMM_EL3_MANIFEST_VERS_MAJOR	(U(0))

/*
 * The Minor version value for the Boot Manifest supported by this
 * implementation of RMM.
 */
#define RMM_EL3_MANIFEST_VERS_MINOR	(U(1))

#define RMM_EL3_MANIFEST_GET_VERS_MAJOR					\
				RMM_EL3_IFC_GET_VERS_MAJOR
#define RMM_EL3_MANIFEST_GET_VERS_MINOR					\
				RMM_EL3_IFC_GET_VERS_MINOR
#define RMM_EL3_MANIFEST_VERSION					\
				RMM_EL3_IFC_SUPPORTED_VERSION

#ifndef __ASSEMBLER__
/****************************************************************************
 * Boot interface related functions
 ***************************************************************************/

/*
 * Accessors to the parameters obtained through the boot interface arguments.
 */
unsigned int rmm_el3_ifc_get_version(void);
uintptr_t rmm_el3_ifc_get_shared_buf_pa(void);

static inline size_t rmm_el3_ifc_get_shared_buf_size(void)
{
	return SZ_4K;
}

/*
 * Validate the boot arguments and Initialize the rmm_el3_ifc library.
 * This function must be called only once during cold boot.
 *
 * This function must be called prior to enable the MMU and data cache for
 * RMM execution.
 *
 * Args:
 *	- x0 - x3: Arguments passed through registers x0 to x3.
 *	- shared_buf_va: Virtual address where the RMM-EL3 shared
 *	  will be mapped by the platform.
 *
 * Return:
 *	- 0 on success or a negative error code otherwise.
 */
int rmm_el3_ifc_init(unsigned long x0, unsigned long x1, unsigned long x2,
		     unsigned long x3, uintptr_t shared_buf_va);

/*
 * This function performs an early validation of the CPU Id received
 * during warm boot and stores it into tpidr_el2.
 *
 * If the validation fails it will call into EL3 and will not return
 * to the caller.
 *
 * Args:
 *	- x0: CPU Id received from EL3.
 * Return:
 *	- Validated CPU Id or will not return on an error.
 */
unsigned int rmm_el3_ifc_validate_cpuid(unsigned long x0);

/*
 * Return a pointer to the RMM <-> EL3 shared pointer and lock it to prevent
 * concurrent access.
 *
 * Return:	Exclusive pointer to the RMM <-> EL3 shared area.
 */
uintptr_t rmm_el3_ifc_get_shared_buf_locked(void);

/*
 * Release the RMM <-> EL3 buffer.
 */
void rmm_el3_ifc_release_shared_buf(void);

/*****************************************************************************
 * Boot Manifest functions and structures.
 ****************************************************************************/

/* Boot manifest core structure as per v0.1 */
struct rmm_core_manifest {
	uint32_t version;	/* Manifest version */
	uintptr_t plat_data;	/* Manifest platform data */
};

COMPILER_ASSERT(offsetof(struct rmm_core_manifest, version) == 0);
COMPILER_ASSERT(offsetof(struct rmm_core_manifest, plat_data) == 8);

/*
 * Accessors to the Boot Manifest data.
 */
unsigned int rmm_el3_ifc_get_manifest_version(void);

/*
 * Return a pointer to the platform manifest data if setup by EL3 Firmware.
 *
 * This function must be called only after the core manifest has
 * been processed (See rmm_el3_ifc_process_boot_manifest()). Also, since
 * the shared buffer can be reclaimed for communication during rmm_main(), we
 * restrict this call to be allowed before the MMU is enabled by the platform.
 */
uintptr_t rmm_el3_ifc_get_plat_manifest_pa(void);

/****************************************************************************
 * RMM-EL3 Runtime APIs
 ***************************************************************************/

/*
 * Get the realm attestation key to sign the realm attestation token. It is
 * expected that only the private key is retrieved in raw format.
 *
 * Args:
 *	- buf:		Pointer to the buffer used to get the attestation key
 *			from EL3. This must belong to the RMM-EL3 shared memory
 *			and must be locked before use.
 *	- buflen	Maximum size for the Realm Attestation Key.
 *	- len:		Pointer to a size_t variable to store the size of the
 *			received realm attestation key.
 *	- crv:		ECC Crve type for querying attestation key from monitor.
 *
 * Return:
 *	- 0 On success or a negative error code otherwise.
 */
int rmm_el3_ifc_get_realm_attest_key(uintptr_t buf, size_t buflen,
				     size_t *len, unsigned int crv);

/*
 * Get the platform token from the EL3 firmware and pass the public hash
 * value to it.
 * The caller of this API should have filled the public key hash at `buf`
 * and the length of the key hash must be stored in hash_size.
 *
 * Args:
 *	- buf:		Pointer to the buffer used to get the platform token
 *			from EL3. This must belong to the RMM-EL3 shared memory
 *			and must be locked before use.
 *	- buflen	Maximum size for the Platform Token.
 *	- len:		Pointer where the size of the retrieved platform token
 *			will be stored.
 *	- hash_size:	Size of the SHA digest used for the token generation.
 *
 * Return:
 *	- 0 On success or a negative error code otherwise.
 */
int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
				   size_t *len, size_t hash_size);

static inline unsigned long rmm_el3_ifc_gtsi_delegate(unsigned long addr)
{
	return monitor_call(SMC_RMM_GTSI_DELEGATE, addr,
				0UL, 0UL, 0UL, 0UL, 0UL);
}

static inline unsigned long rmm_el3_ifc_gtsi_undelegate(unsigned long addr)
{
	return monitor_call(SMC_RMM_GTSI_UNDELEGATE, addr,
				0UL, 0UL, 0UL, 0UL, 0UL);
}
#endif /* __ASSEMBLER__ */
#endif /* RMM_EL3_IFC_H */
