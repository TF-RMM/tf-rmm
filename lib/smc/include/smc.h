/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_H
#define SMC_H

#include <utils_def.h>

/* FID: Type - Fast Call */
#define SMC_TYPE_SHIFT		U(31)
#define SMC_TYPE_MASK		U(1)
#define SMC_TYPE_FAST		U(1)

/* FID: Calling convention - SMC32/SMC64 */
#define SMC_CC_SHIFT		U(30)
#define SMC_CC_MASK		U(1)
#define SMC_CC_SMC32		U(0)
#define SMC_CC_SMC64		U(1)

/* FID: Owning entity number - Standard Secure Service Calls */
#define SMC_OEN_SHIFT		U(24)
#define SMC_OEN_MASK		U(0x3F)
#define SMC_OEN_STD		U(0x4)
#define SMC_OEN_ARCH		U(0x0)

/* FID: Must be zero (MBZ) */
#define SMC_MBZ_SHIFT		U(16)
#define SMC_MBZ_MASK		U(0xFF)
#define SMC_MBZ_ZERO		U(0x0)

/*
 * SVE Hint bit (SMCCCv1.3), denoting the absence of SVE specific live state.
 *
 * MISRA treats 1U as 8-bit type variables. So use 1UL and typecast the value
 * to 'unsigned int'
 */
#define SMC_SVE_HINT		(U(1) << 16)

/* FID: Function number */
#define SMC_FNUM_SHIFT		U(0)
#define SMC_FNUM_MASK		U(0xFFFF)

#define SMC_FIELD_VAL(_field, _val)					    \
	(((_val) & SMC_##_field##_MASK) << SMC_##_field##_SHIFT)

#define SMC_SET_FIELD(_init_val, _field, _val)                              \
	(((_init_val) & ~SMC_FIELD_VAL(_field, SMC_##_field##_MASK)) |	    \
	 SMC_FIELD_VAL(_field, _val))

#define SMC_GET_FIELD(_fid, _field)					    \
	(((_fid) >> SMC_##_field##_SHIFT) & SMC_##_field##_MASK)

/* Arm Architecture Call range function IDs */
				/* 0x80000000 */
#define SMC_ARCH_CALL_BASE	(SMC_SET_FIELD(U(0), TYPE, SMC_TYPE_FAST) | \
				SMC_SET_FIELD(U(0), OEN, SMC_OEN_ARCH))

				/* 0x8000FFFF */
#define SMC_ARCH_CALL_LIMIT	(SMC_SET_FIELD(SMC_ARCH_CALL_BASE, FNUM,    \
					       U(0xFFFF)))

/*
 * We allocate all RMM calls as function IDs within the Standard Secure
 * Service Call range category defined in the SMCCC.
 */
				/* 0x84000000 */
#define SMC_STD_CALL_BASE	(SMC_SET_FIELD(U(0), TYPE, SMC_TYPE_FAST) | \
				SMC_SET_FIELD(U(0), OEN, SMC_OEN_STD))

				/* 0x840001CF */
#define SMC_STD_CALL_LIMIT	(SMC_SET_FIELD(SMC_STD_CALL_BASE, FNUM,     \
					       U(0x1CF)))

/* STD calls FNUM Min/Max ranges */
#define SMC32_PSCI_FNUM_MIN	(U(0x0))
#define SMC32_PSCI_FNUM_MAX	(U(0x14))

#define SMC64_PSCI_FNUM_MIN	(U(0x0))
#define SMC64_PSCI_FNUM_MAX	(U(0x14))

/*
 * TODO: This range includes a range that is not a valid RMI func ID. If an
 * invalid SMC from that range does manage to come through the RMI SMC, RMM
 * will gracefully handle it.
 */
#define SMC64_RMI_FNUM_MIN	(U(0x150))
#define SMC64_RMI_FNUM_MAX	(U(0x1D3))

#define SMC64_RSI_FNUM_MIN	(U(0x190))
#define SMC64_RSI_FNUM_MAX	(U(0x1AF))

#define SMC64_RMM_EL3_FNUM_MIN	(U(0x1B0))
#define SMC64_RMM_EL3_FNUM_MAX	(U(0x1CF))

/* Utility macros for FID range values */
#define SMC32_ARCH_FID(_offset)						   \
	(SMC_SET_FIELD(SMC_ARCH_CALL_BASE, CC, SMC_CC_SMC32)		|  \
	 SMC_SET_FIELD(SMC_ARCH_CALL_BASE, FNUM, (_offset)))

#define SMC64_ARCH_FID(_offset)						   \
	(SMC_SET_FIELD(SMC_ARCH_CALL_BASE, CC, SMC_CC_SMC64)		|  \
	 SMC_SET_FIELD(SMC_ARCH_CALL_BASE, FNUM, (_offset)))

#define SMC32_STD_FID(_range, _offset)					   \
	(SMC_SET_FIELD(SMC_STD_CALL_BASE, CC, SMC_CC_SMC32)		|  \
	 SMC_SET_FIELD(SMC_STD_CALL_BASE, FNUM,				   \
	 (SMC32_##_range##_FNUM_MIN + (_offset))))

#define SMC64_STD_FID(_range, _offset)					   \
	(SMC_SET_FIELD(SMC_STD_CALL_BASE, CC, SMC_CC_SMC64)		|  \
	 SMC_SET_FIELD(SMC_STD_CALL_BASE, FNUM,				   \
	 (SMC64_##_range##_FNUM_MIN + (_offset))))

#define IS_SMC64_FID_IN_RANGE(_range, _fid)				   \
	((SMC_GET_FIELD(_fid, FNUM)	>= SMC64_##_range##_FNUM_MIN)	&& \
	 (SMC_GET_FIELD(_fid, FNUM)	<= SMC64_##_range##_FNUM_MAX))

#define IS_SMC32_FID_IN_RANGE(_range, _fid)				   \
	((SMC_GET_FIELD(_fid, FNUM)	>= SMC32_##_range##_FNUM_MIN)	&& \
	 (SMC_GET_FIELD(_fid, FNUM)	<= SMC32_##_range##_FNUM_MAX))

#define IS_SMC64_FID_STD_FAST(_fid)					   \
	(((_fid) & ~SMC_FIELD_VAL(FNUM, SMC_FNUM_MASK)) ==		   \
	 ((SMC_FIELD_VAL(CC, SMC_CC_SMC64)				|  \
	   SMC_FIELD_VAL(TYPE, SMC_TYPE_FAST)				|  \
	   SMC_FIELD_VAL(OEN, SMC_OEN_STD))))

#define IS_SMC32_FID_STD_FAST(_fid)					   \
	(((_fid) & ~SMC_FIELD_VAL(FNUM, SMC_FNUM_MASK)) ==		   \
	 ((SMC_FIELD_VAL(CC, SMC_CC_SMC32)				|  \
	   SMC_FIELD_VAL(TYPE, SMC_TYPE_FAST)				|  \
	   SMC_FIELD_VAL(OEN, SMC_OEN_STD))))

#define IS_SMC64_STD_FAST_IN_RANGE(_range, _fid)			   \
	(IS_SMC64_FID_STD_FAST(_fid) && IS_SMC64_FID_IN_RANGE(_range, _fid))

#define IS_SMC32_STD_FAST_IN_RANGE(_range, _fid)			   \
	(IS_SMC32_FID_STD_FAST(_fid) && IS_SMC32_FID_IN_RANGE(_range, _fid))

#define SMC64_NUM_FIDS_IN_RANGE(_range)					   \
	(SMC64_##_range##_FNUM_MAX - SMC64_##_range##_FNUM_MIN + 1U)

/* Gets the offset in a range. Inputs must be pre-verified */
#define SMC64_FID_OFFSET_FROM_RANGE_MIN(_range, _fid)			   \
	(SMC_GET_FIELD(_fid, FNUM) - SMC64_##_range##_FNUM_MIN)

/* Implementation defined FID values */
					/* 0x18F */
#define SMC_RMM_REQ_COMPLETE		SMC64_STD_FID(RMI, U(0x3F))

/* ARM ARCH call FIDs */
#define SMCCC_VERSION			SMC32_ARCH_FID(U(0))
#define SMCCC_ARCH_FEATURES		SMC32_ARCH_FID(U(1))
#define SMCCC_ARCH_SOC_ID		SMC32_ARCH_FID(U(2))

#define SMCCC_ARCH_WORKAROUND_2		SMC32_ARCH_FID(U(0x7FFF))
#define SMCCC_ARCH_WORKAROUND_1		SMC32_ARCH_FID(U(0x8000))

#define SMCCC_ARCH_FEATURE_AVAILABILITY SMC64_ARCH_FID(U(3))

/* Implemented version of the SMC Calling Convention */
#define SMCCC_VERSION_MAJOR	U(1)
#define SMCCC_VERSION_MINOR	U(2)

/*
 * SMCCC version encoding:
 *  Bit[31] must be zero
 *  Bits [30:16] Major version
 *  Bits [15:0] Minor version
 */
#define SMCCC_VERSION_NUMBER						  \
	((SMCCC_VERSION_MAJOR << U(16)) | SMCCC_VERSION_MINOR)

/* SMCCC return codes */
#define SMC_SUCCESS		(unsigned long)(0)
#define SMC_NOT_SUPPORTED	(unsigned long)(-1)
#define SMC_NOT_REQUIRED	(unsigned long)(-2)
#define SMC_INVALID_PARAMETER	(unsigned long)(-3)

#define SMC_UNKNOWN		(unsigned long)(-1)

/* Result registers X0-X4 */
#define SMC_RESULT_REGS		5U
/* Argument registers X1-X12 */
#define SMC_ARGS_MAX		12U

/*
 * opcode of system register for SMCCC_ARCH_FEATURE_AVAILABILITY as
 * defined by opcode = (op0 << 19) | (op1 << 16) | (CRn << 12) | (CRm << 8) | (op2 << 5)
 */
#define SCR_EL3_OPCODE		U(0x1E1100)
#define CPTR_EL3_OPCODE		U(0x1E1140)
#define MDCR_EL3_OPCODE		U(0x1E1320)
#define MPAM3_EL3_OPCODE	U(0x1EA500)

#define SMC_ARG_X1_X2	U(0)
#define SMC_ARG_X3_X4	U(16)
#define SMC_ARG_X5_X6	U(32)
#define SMC_ARG_X7_X8	U(48)
#define SMC_ARG_X9_X10	U(64)
#define SMC_ARG_X11_X12	U(80)

#define SMC_RES_X0_X1	U(0)
#define SMC_RES_X2_X3	U(16)
#define SMC_RES_X4	U(32)

#ifndef __ASSEMBLER__

struct smc_result {
	unsigned long x[SMC_RESULT_REGS];
};

/* Used to pass more than 8 arguments to SMC call */
struct smc_args {
	unsigned long v[SMC_ARGS_MAX];
};

/*
 * Helper macros for providing full designated initializer for the v array in
 * the 'v' array of 'struct smc_args'. Using the below macro instead of
 * providing an incomplete array initializer makes Misra checkers pass.
 */
#define SMC_ARGS_1(v1) \
	((struct smc_args){{(v1), 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_2(v1, v2) \
	((struct smc_args){{(v1), (v2), 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_3(v1, v2, v3) \
	((struct smc_args){{(v1), (v2), (v3), 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_4(v1, v2, v3, v4) \
	((struct smc_args){{(v1), (v2), (v3), (v4), 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_5(v1, v2, v3, v4, v5) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), 0U, 0U, 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_6(v1, v2, v3, v4, v5, v6) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), 0U, 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_7(v1, v2, v3, v4, v5, v6, v7) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), (v7), 0U, 0U, 0U, 0U, 0U}})
#define SMC_ARGS_8(v1, v2, v3, v4, v5, v6, v7, v8) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), (v7), (v8), 0U, 0U, 0U, 0U}})
#define SMC_ARGS_9(v1, v2, v3, v4, v5, v6, v7, v8, v9) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), (v7), (v8), (v9), 0U, 0U, 0U}})
#define SMC_ARGS_10(v1, v2, v3, v4, v5, v6, v7, v8, v9, v10) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), (v7), (v8), (v9), (v10), 0U, 0U}})
#define SMC_ARGS_11(v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), (v7), (v8), (v9), (v10), (v11), \
		0U}})
#define SMC_ARGS_12(v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12) \
	((struct smc_args){{(v1), (v2), (v3), (v4), (v5), (v6), (v7), (v8), (v9), (v10), (v11), \
		(v12)}})

unsigned long monitor_call(unsigned long id,
			unsigned long arg0,
			unsigned long arg1,
			unsigned long arg2,
			unsigned long arg3,
			unsigned long arg4,
			unsigned long arg5);

void monitor_call_with_arg_res(unsigned long fid, struct smc_args *args, struct smc_result *res);

#endif /* __ASSEMBLER__ */

#endif /* SMC_H */
