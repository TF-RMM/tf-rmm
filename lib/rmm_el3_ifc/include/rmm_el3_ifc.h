/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_IFC_H
#define RMM_EL3_IFC_H

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

					/* 0x1B0 - 0x1B1 */
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
#define E_RMM_BOOT_VERSION_NOT_VALID			(-2)
#define E_RMM_BOOT_CPUS_OUT_OF_RANGE			(-3)
#define E_RMM_BOOT_CPU_ID_OUT_OF_RANGE			(-4)
#define E_RMM_BOOT_INVALID_SHARED_BUFFER		(-5)
#define E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED	(-6)
#define E_RMM_BOOT_MANIFEST_DATA_ERROR			(-7)

/* Starting RMM-EL3 interface version 0.4 */
					/* 0x1B4 */
#define SMC_RMM_EL3_FEATURES		SMC64_STD_FID(RMM_EL3, U(4))

					/* 0x1B5 */
#define SMC_RMM_EL3_TOKEN_SIGN		SMC64_STD_FID(RMM_EL3, U(5))


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
#define RMM_EL3_IFC_VERS_MINOR		(U(3))

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
 * Boot Manifest functions and structures (v0.3)
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

/* NS DRAM bank structure */
struct ns_dram_bank {
	uintptr_t base;			/* Base address */
	uint64_t size;			/* Size of bank */
};

/* NS DRAM layout info structure */
struct ns_dram_info {
	uint64_t num_banks;		/* Number of DRAM banks */
	struct ns_dram_bank *banks;	/* Pointer to dram_banks[] */
	uint64_t checksum;		/* Checksum of ns_dram_info data */
};

/* Boot manifest core structure as per v0.3 */
struct rmm_core_manifest {
	uint32_t version;		/* Manifest version */
	uint32_t padding;		/* RES0 */
	uintptr_t plat_data;		/* Manifest platform data */
	struct ns_dram_info plat_dram;	/* Platform DRAM data (from v0.2) */
	struct console_list plat_console; /* Platform console list (from 0.3) */
};

COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, version)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_data)) == 8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_dram)) == 16U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmm_core_manifest, plat_console)) == 40U);

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
 * from the Boot manifest v0.2 onwards.
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
 *						    Boot manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 */
int rmm_el3_ifc_get_dram_data_validated_pa(unsigned long max_num_banks,
					   struct ns_dram_info **plat_dram_info);


/*
 * Return validated Console list passed in plat_console pointer
 * from the Boot manifest v0.3 onwards.
 *
 * Args:
 *	- plat_console_list:	Return physical address to platform console
				list structure setup by EL3 Firmware,
 *				or NULL in case of error.
 *
 * Return:
 *	- E_RMM_BOOT_SUCCESS			    Success.
 *	- E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED Version reported by the
 *						    Boot manifest is not
 *						    supported by this API.
 *	- E_RMM_BOOT_MANIFEST_DATA_ERROR	    Error parsing data.
 */
int rmm_el3_ifc_get_console_list_pa(struct console_list **plat_console_list);

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

#endif /* __ASSEMBLER__ */
#endif /* RMM_EL3_IFC_H */
