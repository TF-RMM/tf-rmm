/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_IFC_H
#define RMM_EL3_IFC_H

#ifndef __ASSEMBLER__
#include <dev_type.h>
#endif

#include <sizes.h>
#include <smc.h>

#ifndef __ASSEMBLER__
#include <stdbool.h>
#include <stddef.h>
#endif

/***************************************
 * Error codes for the EL3-RMM interface
 ***************************************/

#define E_RMM_OK			 (0)
#define E_RMM_UNK			(-1)
#define E_RMM_BAD_ADDR			(-2)
#define E_RMM_BAD_PAS			(-3)
#define E_RMM_NOMEM			(-4)
#define E_RMM_INVAL                     (-5)
#define E_RMM_AGAIN			(-6)
#define E_RMM_FAULT			(-7)
#define E_RMM_IN_PROGRESS		(-8)

/****************************************
 * Generic defines for RMM-EL3 interface
 ****************************************/

/* Signature Algorithm ID */
#define ATTEST_KEY_CURVE_ECC_SECP384R1  (0U)

/* Hash Algorithm ID */
#define EL3_TOKEN_SIGN_HASH_ALG_SHA384	(1U)

/********************************************
 * SMC Function IDs for the EL3-RMM interface
 ********************************************/

					/* 0xc40001b0 - 0xc40001b1 */
#define SMC_RMM_GTSI_DELEGATE		SMC64_STD_FID(RMM_EL3, U(0))
#define SMC_RMM_GTSI_UNDELEGATE		SMC64_STD_FID(RMM_EL3, U(1))

					/* 0xc40001b2 - 0xc40001b3 */
#define SMC_RMM_GET_REALM_ATTEST_KEY	SMC64_STD_FID(RMM_EL3, U(2))
#define SMC_RMM_GET_PLAT_TOKEN		SMC64_STD_FID(RMM_EL3, U(3))

					/* 0xc40001cf */
#define SMC_RMM_BOOT_COMPLETE		SMC64_STD_FID(RMM_EL3, U(0x1F))

/* SMC_RMM_BOOT_COMPLETE return codes */
#define E_RMM_BOOT_SUCCESS				(0)
#define E_RMM_BOOT_UNKNOWN_ERROR			(-1)
#define E_RMM_BOOT_VERSION_NOT_VALID			(-2)
#define E_RMM_BOOT_CPUS_OUT_OF_RANGE			(-3)
#define E_RMM_BOOT_CPU_ID_OUT_OF_RANGE			(-4)
#define E_RMM_BOOT_INVALID_SHARED_BUFFER		(-5)
#define E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED	(-6)
#define E_RMM_BOOT_MANIFEST_DATA_ERROR			(-7)
#define E_RMM_BOOT_NO_MEM				(-8)

/* Starting RMM-EL3 interface version 0.4 */
					/* 0xc40001b4 */
#define SMC_RMM_EL3_FEATURES		SMC64_STD_FID(RMM_EL3, U(4))

					/* 0xc40001b5 */
#define SMC_RMM_EL3_TOKEN_SIGN		SMC64_STD_FID(RMM_EL3, U(5))

					/* 0xc40001b6 */
#define SMC_RMM_MEC_REFRESH		SMC64_STD_FID(RMM_EL3, U(6))

/* Starting RMM-EL3 interface version 0.5 */
					/* 0xc40001b7 */
#define SMC_RMM_RP_IDE_KEY_PROG		SMC64_STD_FID(RMM_EL3, U(7))

					/* 0xc40001b8 */
#define SMC_RMM_RP_IDE_KEY_SET_GO	SMC64_STD_FID(RMM_EL3, U(8))

					/* 0xc40001b9 */
#define SMC_RMM_RP_IDE_KEY_SET_STOP	SMC64_STD_FID(RMM_EL3, U(9))

					/* 0xc40001ba */
#define SMC_RMM_RP_IDE_KM_POLL		SMC64_STD_FID(RMM_EL3, U(10))

					/* 0xc40001bb */
#define SMC_RMM_RESERVE_MEMORY		SMC64_STD_FID(RMM_EL3, U(11))

#define RESERVE_MEM_ALIGN_SHIFT		56UL
#define RESERVE_MEM_ALIGN_WIDTH		8UL
#define RESERVE_MEM_FLAGS_SHIFT		0UL
#define RESERVE_MEM_FLAGS_WIDTH		56UL

/************************
 * Version related macros
 ************************/

/*
 * RMM-EL3 Interface and Boot Manifest versions encoding:
 *	- Bit[31] RES0
 *	- Bits [30:16] Major version
 *	- Bits [15:0] Minor version
 */
#define RMM_EL3_IFC_GET_VERS_MAJOR(_version)			\
				(((_version) >> 16) & 0x7FFFU)
#define RMM_EL3_IFC_GET_VERS_MINOR(_version)			\
				((_version) & 0xFFFFU)

#define RMM_EL3_IFC_MAKE_VERSION(_major, _minor)		\
	(((((_major) & 0x7FFFU) << 16) | ((_minor) & 0xFFFFU)))

/*
 * The Major version value for the RMM-EL3 Interface supported by this
 * implementation of RMM.
 */
#define RMM_EL3_IFC_VERS_MAJOR		(U(0))

/*
 * The Minor version value for the RMM-EL3 Interface supported by this
 * implementation of RMM.
 */
#define RMM_EL3_IFC_VERS_MINOR		(U(5))

/*
 * Check if RMM-EL3 Interface is compatible. The Major version should match
 * and the minor version should be >= the number expected by RMM.
 */
#define IS_RMM_EL3_IFC_COMPATIBLE(_version)				\
	((RMM_EL3_IFC_GET_VERS_MAJOR(_version) == RMM_EL3_IFC_VERS_MAJOR) && \
	 (RMM_EL3_IFC_GET_VERS_MINOR(_version) >= RMM_EL3_IFC_VERS_MINOR))


#define RMM_EL3_MANIFEST_GET_VERS_MAJOR					\
				RMM_EL3_IFC_GET_VERS_MAJOR
#define RMM_EL3_MANIFEST_GET_VERS_MINOR					\
				RMM_EL3_IFC_GET_VERS_MINOR
#define RMM_EL3_MANIFEST_MAKE_VERSION					\
				RMM_EL3_IFC_MAKE_VERSION

/*
 * The Major version value for the Boot Manifest supported by this
 * implementation of RMM.
 */
#define RMM_EL3_MANIFEST_VERS_MAJOR	(U(0))

/*
 * The Minor version value for the Boot Manifest supported by this
 * implementation of RMM.
 */
#define RMM_EL3_MANIFEST_VERS_MINOR	(U(3))

/*
 * Check if EL3 Manifest is compatible. The Major version should match
 * and the minor version should be >= the number expected by RMM.
 */
#define IS_RMM_EL3_MANIFEST_COMPATIBLE(_version)				\
	((RMM_EL3_MANIFEST_GET_VERS_MAJOR(_version) == RMM_EL3_MANIFEST_VERS_MAJOR) && \
	 (RMM_EL3_MANIFEST_GET_VERS_MINOR(_version) >= RMM_EL3_MANIFEST_VERS_MINOR))

#ifndef __ASSEMBLER__

/***************************************************************************
 * SMC_RMM_EL3_FEATURES related definitions
 ***************************************************************************/
#define RMM_EL3_IFC_FEAT_REG_0_IDX			U(0)
#define RMM_EL3_IFC_FEAT_REG_0_EL3_TOKEN_SIGN_SHIFT	U(0)
#define RMM_EL3_IFC_FEAT_REG_0_EL3_TOKEN_SIGN_WIDTH	U(1)

/***************************************************************************
 * SMC_RMM_EL3_TOKEN_SIGN related definitions and structures
 ***************************************************************************/

/* Command code for SMC_RMM_EL3_TOKEN_SIGN SMC */
#define SMC_RMM_EL3_TOKEN_SIGN_PUSH_REQ_OP		U(1)
#define SMC_RMM_EL3_TOKEN_SIGN_PULL_RESP_OP		U(2)
#define SMC_RMM_EL3_TOKEN_SIGN_GET_RAK_PUB_OP		U(3)

/* The Max hash size is set to be SHA-512 Digest size */
#define EL3_TOKEN_REQUEST_MAX_HASH_LEN			64
/* The Max Signature is set to be a buffer of 512 Bytes (4096 bits) */
#define EL3_TOKEN_RESPONSE_MAX_SIG_LEN			512

/* Structure format in which EL3 expects a request */
struct el3_token_sign_request {
	SET_MEMBER(uint32_t sign_alg_id, 0x0, 0x8);
	SET_MEMBER(uint64_t cookie, 0x8, 0x10);		/* Passthrough to response */
	SET_MEMBER(uint64_t req_ticket, 0x10, 0x18);	/* Passthrough to response */
	SET_MEMBER(uint32_t hash_alg_id, 0x18, 0x20);
	SET_MEMBER(uint8_t hash_buf[EL3_TOKEN_REQUEST_MAX_HASH_LEN], 0x20, 0x60);
};
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request, sign_alg_id)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request, cookie)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request, req_ticket)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request, hash_alg_id)) == 0x18U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_request, hash_buf)) == 0x20U);

/* Structure format in which EL3 is expected to return data */
struct el3_token_sign_response {
	SET_MEMBER(uint64_t cookie, 0x0, 0x8);		/* Passthrough from request */
	SET_MEMBER(uint64_t req_ticket, 0x8, 0x10);	/* Passthrough from request */
	SET_MEMBER(uint16_t sig_len, 0x10, 0x12);
	SET_MEMBER(uint8_t signature_buf[EL3_TOKEN_RESPONSE_MAX_SIG_LEN], 0x12, 0x212);
};

COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response, cookie)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response, req_ticket)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response, sig_len)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct el3_token_sign_response, signature_buf)) == 0x12U);

/***************************************************************************
 * SMC_RMM_EL3_RP_IDE_KM related macros
 ***************************************************************************/
#define EL3_IFC_IDE_STREAM_INFO_ID_SHIFT		U(0)
#define EL3_IFC_IDE_STREAM_INFO_ID_WIDTH		U(8)
#define EL3_IFC_IDE_STREAM_INFO_KEY_SUBSTREAM_SHIFT	U(8)
#define EL3_IFC_IDE_STREAM_INFO_KEY_SUBSTREAM_WIDTH	U(3)
#define EL3_IFC_IDE_STREAM_INFO_KEY_DIRECTION_SHIFT	U(11)
#define EL3_IFC_IDE_STREAM_INFO_KEY_DIRECTION_WIDTH	U(1)
#define EL3_IFC_IDE_STREAM_INFO_KEY_SLOT_SHIFT		U(12)
#define EL3_IFC_IDE_STREAM_INFO_KEY_SLOT_WIDTH		U(1)

/* Number of times to retry a IDE KM call if the SMC returns E_RMM_AGAIN */
#define EL3_IFC_IDE_KM_RETRY_COUNT_MAX			U(3)

/* Construct stream_info from key set, key direction, key substream, stream id */
#define EL3_IFC_IDE_MAKE_STREAM_INFO(_kslot, _kdir, _ksubstream, _id)	\
	(INPLACE(EL3_IFC_IDE_STREAM_INFO_KEY_SLOT, (_kslot)) |\
	 INPLACE(EL3_IFC_IDE_STREAM_INFO_KEY_DIRECTION, (_kdir)) | \
	 INPLACE(EL3_IFC_IDE_STREAM_INFO_KEY_SUBSTREAM, (_ksubstream)) | \
	 INPLACE(EL3_IFC_IDE_STREAM_INFO_ID, (_id)))

/***************************************************************************
 * SMC_RMM_RESERVE_MEMORY related definitions
 ***************************************************************************/
#define RESERVE_MEM_FLAG_LOCAL		(1UL << 0)

/***************************************************************************
 * RMM-EL3 Interface related functions
 ***************************************************************************/

/*
 * Accessors to the parameters obtained through the RMM-EL3 Interface arguments.
 */
unsigned int rmm_el3_ifc_get_version(void);
uintptr_t rmm_el3_ifc_get_shared_buf_pa(void);

static inline size_t rmm_el3_ifc_get_shared_buf_size(void)
{
	return SZ_4K;
}

/*
 * Validate the RMM-EL3 Interface boot arguments and initialize the
 * rmm_el3_ifc library. This function must be called only once during cold
 * boot.
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
 * Boot Manifest definitions, functions and structures (v0.5)
 ****************************************************************************/

/* Console info structure */
struct console_info {
	uintptr_t base;			/* Console base address */
	uint64_t map_pages;		/* Num of pages to be mapped in RMM for the console MMIO */
	char name[8];			/* Name of console */
	uint64_t clk_in_hz;		/* UART clock (in Hz) for the console */
	uint64_t baud_rate;		/* Baud rate */
	uint64_t flags;			/* Additional flags RES0 */
};

struct console_list {
	uint64_t num_consoles;		/* Number of consoles */
	struct console_info *consoles;	/* Pointer to console_info[] */
	uint64_t checksum;		/* Checksum of console_info data */
};

/* Memory bank/IO region structure */
struct memory_bank {
	uintptr_t base;			/* Base address */
	uint64_t size;			/* Size of bank/IO region */
};

/* Memory/IO region layout info structure */
struct memory_info {
	uint64_t num_banks;		/* Number of memory banks/IO regions */
	struct memory_bank *banks;	/* Pointer to memory_banks[] */
	uint64_t checksum;		/* Checksum of memory_info data */
};

/* SMMUv3 Info structure */
struct smmu_info {
	uint64_t smmu_base;		/* SMMUv3 base address */
	uint64_t smmu_r_base;		/* SMMUv3 Realm Pages base address */
};

/* SMMUv3 Info List structure */
struct smmu_list {
	uint64_t num_smmus;		/* Number of smmu_info entries */
	struct smmu_info *smmus;	/* Pointer to smmu_info[] array */
	uint64_t checksum;		/* Checksum of smmu_list data */
};

/* PCIe BDF Mapping Info structure */
struct bdf_mapping_info {
	uint16_t mapping_base;	/* Base of BDF mapping (inclusive) */
	uint16_t mapping_top;	/* Top of BDF mapping (exclusive) */
	uint16_t mapping_off;	/* Mapping offset, as per Arm Base System Architecture: */
				/* StreamID = zero_extend(RequesterID[N-1:0]) + (1<<N)*Constant_B */
	uint16_t smmu_idx;	/* SMMU index in smmu_info[] array */
};

/* PCIe Root Port Info structure */
struct root_port_info {
	uint16_t root_port_id;			/* Root Port identifier */
	uint16_t padding;			/* RES0 */
	uint32_t num_bdf_mappings;		/* Number of BDF mappings */
	struct bdf_mapping_info *bdf_mappings;	/* Pointer to bdf_mapping_info[] array */
};

/* PCIe Root Complex info structure v0.1 */
struct root_complex_info {
	uint64_t ecam_base;			/* ECAM base address. */
	uint8_t segment;			/* PCIe segment identifier */
	uint8_t padding[3];			/* RES0 */
	uint32_t num_root_ports;		/* Number of root ports */
	struct root_port_info *root_ports;	/* Pointer to root_port_info[] array */
};

/* PCIe Root Complex List structure */
struct root_complex_list {
	/* Number of pci_rc_info entries */
	uint64_t num_root_complex;

	/* PCIe Root Complex info structure version */
	uint32_t rc_info_version;

	/* RES0 */
	uint32_t padding;

	/* Pointer to pci_rc_info[] array */
	struct root_complex_info *root_complex;

	/* Checksum of pci_rc_list data */
	uint64_t checksum;
};

/* Boot Manifest core structure as per v0.5 */
struct rmm_core_manifest {
	uint32_t version;		/* Manifest version */
	uint32_t padding;		/* RES0 */
	uintptr_t plat_data;		/* Manifest platform data */
	/* Platform DRAM data (v0.2) */
	struct memory_info plat_dram;
	/* Platform console list (v0.3) */
	struct console_list plat_console;
	/* Platform device address ranges (v0.4) */
	struct memory_info plat_ncoh_region;
	struct memory_info plat_coh_region;
	/* Platform SMMUv3 list (v0.5) */
	struct smmu_list plat_smmu;
	/* Platform PCIe Root Complex list (v0.5) */
	struct root_complex_list plat_root_complex;
};

COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, version)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_data)) == 8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_dram)) == 16U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_console)) == 40U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_ncoh_region)) == 64U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_coh_region)) == 88U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_smmu)) == 112U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_root_complex)) == 136U);

/*
 * Accessors to the Boot Manifest data
 */
unsigned int rmm_el3_ifc_get_manifest_version(void);

/*
 * These functions must be called only after the core manifest has
 * been processed (See rmm_el3_ifc_process_boot_manifest()). Also, since
 * the shared buffer can be reclaimed for communication during rmm_main(), we
 * restrict this call to be allowed before the MMU is enabled by the platform.
 */
/*
 * Return a pointer to the platform manifest data if setup by EL3 Firmware
 */
uintptr_t rmm_el3_ifc_get_plat_manifest_pa(void);

/*
 * Return validated DRAM data passed in plat_dram pointer
 * from the Boot Manifest v0.2 onwards.
 *
 * Args:
 *	- max_num_banks:	Maximum number of platform's DRAM banks
 *				supported.
 *	- plat_dram_info:	Return physical address to the platform
 *				DRAM info structure setup by EL3 Firmware,
 *				or NULL in case of error.
 *
 * Return:
 *	- E_RMM_BOOT_SUCCESS			    Success.
 *	- E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED Version reported by the
 *						    Boot Manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 */
int rmm_el3_ifc_get_dram_data_validated_pa(unsigned long max_num_banks,
					   struct memory_info **plat_dram_info);

/*
 * Return validated Console list passed in plat_console pointer
 * from the Boot Manifest v0.3 onwards.
 *
 * Args:
 *	- plat_console_list:	Return physical address to platform console
				list structure setup by EL3 Firmware,
 *				or NULL in case of error.
 *
 * Return:
 *	- E_RMM_BOOT_SUCCESS			    Success.
 *	- E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED Version reported by the
 *						    Boot Manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 */
int rmm_el3_ifc_get_console_list_pa(struct console_list **plat_console_list);

/*
 * Return validated device address ranges data passed in plat_ncoh_region and
 * plat_coh_region fields from the Boot Manifest v0.4 onwards.
 *
 * Args:
 *	- max_num_banks:	Maximum number device memory banks supported
 *				by platform for a particular device memory range.
 *	- plat_dev_region_info:	Return physical address to the platform
 *				device address ranges info structure setup by EL3
 *				Firmware, or NULL in case it is not available.
 *	- type:			Device address ranges coherency type.
 *
 * Return:
 *	- E_RMM_BOOT_SUCCESS			    Success.
 *	- E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED Version reported by the
 *						    Boot Manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 *
 * Note:
 *	Function can return E_RMM_BOOT_SUCCESS and set *plat_dev_range_info to NULL
 *	in case when a particular device memory range is not available.
 */
int rmm_el3_ifc_get_dev_range_validated_pa(unsigned long max_num_banks,
					   struct memory_info **plat_dev_range_info,
					   enum dev_coh_type type);

/*
 * Return validated SMMUv3 list passed in plat_smmu pointer
 * from the Boot Manifest v0.5 onwards. Note that the SMMUv3 list
 * is cached in RMM after processing the Boot Manifest.
 *
 * Args:
 *	- plat_smmu_list:	Return physical address to platform SMMUv3
				list structure setup by EL3 Firmware,
 *				or NULL in case of error.
 *
 * Return:
 *	- E_RMM_BOOT_SUCCESS			    Success.
 *	- E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED Version reported by the
 *						    Boot Manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 */
int rmm_el3_ifc_get_cached_smmu_list_pa(struct smmu_list **plat_smmu_list);

/*
 * Return validated Root Complex list from the Boot Manifest v0.5 onwards.
 *
 * Args:
 *	- plat_rc_list:	Pointer to return Root Complext list
 * Return:
 *	- E_RMM_BOOT_SUCCESS			    Success.
 *	- E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED Version reported by the
 *						    Boot Manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 */
int rmm_el3_ifc_get_root_complex_list_pa(struct root_complex_list **plat_rc_list);

/****************************************************************************
 * RMM-EL3 Runtime interface APIs
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
 *	- E_RMM_OK	On Success.
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	EL3 is busy and the key cannot be retrieved at this
 *			time. At least one further call will be needed in
 *			order to retrieve the key.
 */
int rmm_el3_ifc_get_realm_attest_key(uintptr_t buf, size_t buflen,
					size_t *len, unsigned int crv);

/*
 * Get the platform token from the EL3 firmware and pass the public hash
 * value to it.
 * If the whole token does not fit in the buffer, a piece of the token will be
 * returned in the buffer, and this function will have to be called
 * sequentially in order to obtain the full token. Output variable
 * remaining_len will indicate how much of the token remains to be retrieved.
 *
 * Args:
 *	- buf:			Pointer to the buffer used to get the platform
 *				token from EL3. This must belong to the
 *				RMM-EL3 shared memory and must be locked
 *				before use.
 *	- buflen		Buffer size.
 *	- token_hunk_len:	Return the size of the retrieved token hunk.
 *	- hash_size:		Size of the SHA digest used for the token
 *				generation.
 *				If hash_size contains a valid size (> 0), the
 *				buffer will contain the first part of the token
 *				after returning. Further calls to this API need
 *				to have hash_size set to 0 to retrieve rest of
 *				the platform token.
 *	- remaining_len:	Return the number of bytes of the token that are
 *				pending transfer.
 *
 * Return:
 *	- E_RMM_OK		if part (or entirety) of the token has been
 *				received successfully.
 *	- E_RMM_INVAL		An error in input arguments. This could also be
 *				due to the fact that the token has been
 *				retrieved fully in a prior call and the
 *				arguments should correspond to token generation
 *				phase.
 *	- E_RMM_AGAIN		EL3 is busy and the platform token cannot be
 *				retrieved at this time. At least one further
 *				call will be needed in order to retrieve the
 *				token.
 */
int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
					size_t hash_size,
					size_t *token_hunk_len,
					size_t *remaining_len);

/*
 * Update MEC corresponding to the given MECID.
 *
 * Args:
 *	- mecid:	MECID to update the key generated by the monitor
 *			firmware/TCB.
 *	- is_destroy:	Indicates whether this update is requested due to a
 *			Realm creation or a Realm destruction.
 *
 * Return:
 *	- E_RMM_OK	Key has been updated for the mecid.
 *	- E_RMM_INVAL	An error in input arguments.
 *	- E_RMM_UNK	If the SMC is not implemented or an unknown error
 */
unsigned long rmm_el3_ifc_mec_refresh(unsigned short mecid,
					bool is_destroy);

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

/*
 * Reserve RMM private memory from EL3.
 * available from the RMM-EL3 interface v0.7 onwards.
 *
 * Args:
 *	- size:		Size of memory to be reserved, in bytes.
 *	- flags:	Properties of the memory reservation.
 *			bit 0: reserve memory close to the calling MPIDR
 *	- alignment:	Alignment requirement, in bytes. Can be 1 for the
 *			smallest (byte) alignment, or 4096 for granule
 *			alignment. Must be a power of 2.
 *	- address:	Buffer to receive the physical address of the reserved
 *			memory region.
 *
 * Return:
 *	- E_RMM_OK	success
 *	- E_RMM_UNK	memory reservation call not available (interface < v0.7)
 *	- E_RMM_NOMEM	not enough memory available
 *	- E_RMM_INVAL	unsupported flag
 */
int rmm_el3_ifc_reserve_memory(size_t size, unsigned int flags,
			       unsigned long alignment, uintptr_t *address);

/*
 * Abort the boot process and return to EL3 FW reporting
 * the ec error code.
 *
 * Args:
 *	- ec:		SMC_RMM_BOOT_COMPLETE return code
 */
__dead2 void rmm_el3_ifc_report_fail_to_el3(int ec);

/*
 * Query if EL3_TOKEN_SIGN feature is supported by EL3 firmware.
 * Return true or false depending on the support.
 */
bool rmm_el3_ifc_el3_token_sign_supported(void);

/*
 * Push the attestation signing request to EL3 firmware.
 * Optional interface from the RMM-EL3 interface v0.4 onwards.
 *
 * Args:
 *	- req:		Pointer to the token sign request to be pushed to EL3.
 *			The structure must be located in the RMM-EL3 shared
 *			memory buffer and must be locked before use.
 *
 * Return:
 *	- E_RMM_OK	On Success.
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	Indicates that the request was not queued since the
 *			queue in EL3 is full.
 *	- E_RMM_UNK	If the SMC is not implemented or if interface
 *			version is < 0.4.
 */
int rmm_el3_ifc_push_el3_token_sign_request(const struct el3_token_sign_request *req);

/*
 * Pull the attestation signing response from the EL3 firmware.
 * Optional interface from the RMM-EL3 interface v0.4 onwards.
 * Args:
 *	- resp:		Pointer to the token sign response to get from EL3.
 *			The structure must be located in the RMM-EL3 shared
 *			memory buffer and must be locked before use.
 *
 * Return:
 *	- E_RMM_OK	On Success.
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	Indicates that a response is not ready yet.
 *	- E_RMM_UNK	If the SMC is not implemented or if interface
 *			version is < 0.4.
 */
int rmm_el3_ifc_pull_el3_token_sign_response(const struct el3_token_sign_response *resp);

/*
 * Get the realm attestation public key when EL3 is used to sign attestaion
 * tokens.
 * Optional interface from the RMM-EL3 interface v0.4 onwards.
 * Args:
 *	- buf		Pointer to the buffer used to get the attestation public key
 *			This must belong to the RMM-EL3 shared memory and must be locked
 *			before use.
 *	- buflen	The size of the buffer `buf`.
 *	- len		Pointer to a size_t variable to store the size of the
 *			received response.
 *	- crv		The ECC curve for which the public key is requested.
 *
 * Return:
 *	- E_RMM_OK	On Success.
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	Indicates that a response is not ready yet.
 *	- E_RMM_UNK	If the SMC is not implemented or if interface
 *			version is < 0.4.
 */
int rmm_el3_ifc_get_realm_attest_pub_key_from_el3(uintptr_t buf, size_t buflen,
					size_t *len, unsigned int crv);

/*
 * Access the feature register. This is supported for interface version 0.4 and
 * later.
 *
 * Args:
 * 	- feat_reg_idx	The feature register index.
 *	- feat_reg	Pointer to store the value of the register.
 * Return:
 *	- E_RMM_OK	On Success.
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_UNK	If the SMC is not present if interface
 *			version is < 0.4.
 */
int rmm_el3_ifc_get_feat_register(unsigned int feat_reg_idx, uint64_t *feat_reg);

struct el3_ifc_rp_ide_key {
	unsigned long kq_w0;
	unsigned long kq_w1;
	unsigned long kq_w2;
	unsigned long kq_w3;
};

struct el3_ifc_rp_ide_iv {
	unsigned long iq_w0;
	unsigned long iq_w1;
};

/*
 * Set the key/IV info for a stream. The key is 256 bits and IV is 96 bits. The
 * caller needs to call this SMC to program this key to the {Rx, Tx} ports and
 * for each sub-stream corresponding to a single keyset.
 *
 * Args:
 *	- ecam_addr	Identify the root complex (RC).
 *	- rp_id		Identify the RP within the RC
 *	- stream_info	IDE selective stream information
 *	- key		IDE key buffer
 *	- iv		IV buffer
 *
 * Return:
 *	- E_RMM_OK	On Success. The key programming succeeded.
 *	- E_RMM_FAULT	On Failure. The key programming failed
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	The RP KM interface is busy, and the call needs to be
 *			retried.
 *	- E_RMM_UNK	If the SMC is not implemented or if interface
 *			version is < 0.5.
 */
int rmm_el3_ifc_rp_ide_key_prog(unsigned long ecam_addr, unsigned long rp_id,
				unsigned long stream_info, struct el3_ifc_rp_ide_key *key,
				struct el3_ifc_rp_ide_iv *iv);

/*
 * Activate the IDE stream once all the keys have been programmed. The caller
 * needs to ensure that the corresponding rmm_el3_ifc_ide_key_prog() has
 * succeeded prior to this call.
 *
 * Args:
 *	- ecam_addr	Identify the root complex (RC).
 *	- rp_id		Identify the RP within the RC
 *	- stream_info	IDE selective stream information
 *
 * Return:
 *	- E_RMM_OK	On Success. The key programming succeeded.
 *	- E_RMM_FAULT	On Failure. The key programming failed
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	The RP KM interface is busy, and the call needs to be
 *			retried.
 *	- E_RMM_UNK	If the SMC is not implemented or if interface
 *			version is < 0.5.
 */
int rmm_el3_ifc_rp_ide_key_set_go(unsigned long ecam_addr, unsigned long rp_id,
				  unsigned long stream_info);

/*
 * Stop the IDE stream. This SMC is typically only used in tear down of the IDE
 * Stream.
 *
 * Args:
 *	- ecam_addr	Identify the root complex (RC).
 *	- rp_id		Identify the RP within the RC
 *	- stream_info	IDE selective stream information
 *
 * Return:
 *	- E_RMM_OK	On Success. The key programming succeeded.
 *	- E_RMM_FAULT	On Failure. The key programming failed
 *	- E_RMM_INVAL	If the arguments are invalid.
 *	- E_RMM_AGAIN	The RP KM interface is busy, and the call needs to be
 *			retried.
 *	- E_RMM_UNK	If the SMC is not implemented or if interface
 *			version is < 0.5.
 */
int rmm_el3_ifc_rp_ide_key_set_stop(unsigned long ecam_addr, unsigned long rp_id,
				    unsigned long stream_info);

#endif /* __ASSEMBLER__ */
#endif /* RMM_EL3_IFC_H */
