/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <status.h>
#include <utils_def.h>

#define STATUS_HANDLER(_id)[_id] = #_id

const char *status_handler[] = {
	STATUS_HANDLER(RMI_SUCCESS),
	STATUS_HANDLER(RMI_ERROR_INPUT),
	STATUS_HANDLER(RMI_ERROR_REALM),
	STATUS_HANDLER(RMI_ERROR_REC),
	STATUS_HANDLER(RMI_ERROR_RTT),
	STATUS_HANDLER(RMI_ERROR_IN_USE)
};
COMPILER_ASSERT(ARRAY_LEN(status_handler) == RMI_ERROR_COUNT);

/*
 * At this level (in handle_ns_smc) we distinguish the RMI calls only on:
 * - The number of input arguments [0..4], and whether
 * - The function returns up to three output values in addition
 *   to the return status code.
 * Hence, the naming syntax is:
 * - `*_[0..4]` when no output values are returned, and
 * - `*_[0..4]_o` when the function returns some output values.
 */

typedef unsigned long (*handler_0)(void);
typedef unsigned long (*handler_1)(unsigned long arg0);
typedef unsigned long (*handler_2)(unsigned long arg0, unsigned long arg1);
typedef unsigned long (*handler_3)(unsigned long arg0, unsigned long arg1,
				   unsigned long arg2);
typedef unsigned long (*handler_4)(unsigned long arg0, unsigned long arg1,
				   unsigned long arg2, unsigned long arg3);
typedef unsigned long (*handler_5)(unsigned long arg0, unsigned long arg1,
				   unsigned long arg2, unsigned long arg3,
				   unsigned long arg4);
typedef void (*handler_1_o)(unsigned long arg0, struct smc_result *ret);
typedef void (*handler_3_o)(unsigned long arg0, unsigned long arg1,
			    unsigned long arg2, struct smc_result *ret);

enum rmi_type {
	rmi_type_0,
	rmi_type_1,
	rmi_type_2,
	rmi_type_3,
	rmi_type_4,
	rmi_type_5,
	rmi_type_1_o,
	rmi_type_3_o
};

struct smc_handler {
	const char	*fn_name;
	enum rmi_type	type;
	union {
		handler_0	f0;
		handler_1	f1;
		handler_2	f2;
		handler_3	f3;
		handler_4	f4;
		handler_5	f5;
		handler_1_o	f1_o;
		handler_3_o	f3_o;
		void		*fn_dummy;
	};
	bool		log_exec;	/* print handler execution */
	bool		log_error;	/* print in case of error status */
	unsigned int	out_values;	/* number of output values */
};

/*
 * Get handler ID from FID
 * Precondition: FID is an RMI call
 */
#define SMC_RMI_HANDLER_ID(_fid) SMC64_FID_OFFSET_FROM_RANGE_MIN(RMI, _fid)

#define HANDLER_0(_id, _fn, _exec, _error)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_0, .f0 = _fn, .log_exec = _exec, .log_error = _error,	   \
	.out_values = 0U }
#define HANDLER_1(_id, _fn, _exec, _error)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_1, .f1 = _fn, .log_exec = _exec, .log_error = _error,	   \
	.out_values = 0U }
#define HANDLER_2(_id, _fn, _exec, _error)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_2, .f2 = _fn, .log_exec = _exec, .log_error = _error,     \
	.out_values = 0U }
#define HANDLER_3(_id, _fn, _exec, _error)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_3, .f3 = _fn, .log_exec = _exec, .log_error = _error,	   \
	.out_values = 0U }
#define HANDLER_4(_id, _fn, _exec, _error)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_4, .f4 = _fn, .log_exec = _exec, .log_error = _error,	   \
	.out_values = 0U }
#define HANDLER_5(_id, _fn, _exec, _error)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_5, .f5 = _fn, .log_exec = _exec, .log_error = _error,	   \
	.out_values = 0U }
#define HANDLER_1_O(_id, _fn, _exec, _error, _values)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_1_o, .f1_o = _fn, .log_exec = _exec, .log_error = _error, \
	.out_values = _values }
#define HANDLER_3_O(_id, _fn, _exec, _error, _values)[SMC_RMI_HANDLER_ID(_id)] = { \
	.fn_name = #_id, \
	.type = rmi_type_3_o, .f3_o = _fn, .log_exec = _exec, .log_error = _error, \
	.out_values = _values }

/*
 * The 3rd value enables the execution log.
 * The 4th value enables the error log.
 */
static const struct smc_handler smc_handlers[] = {
	HANDLER_0(SMC_RMM_VERSION,		 smc_version,			true,  true),
	HANDLER_1_O(SMC_RMM_FEATURES,		 smc_read_feature_register,	true,  true, 1U),
	HANDLER_1(SMC_RMM_GRANULE_DELEGATE,	 smc_granule_delegate,		false, true),
	HANDLER_1(SMC_RMM_GRANULE_UNDELEGATE,	 smc_granule_undelegate,	false, true),
	HANDLER_2(SMC_RMM_REALM_CREATE,		 smc_realm_create,		true,  true),
	HANDLER_1(SMC_RMM_REALM_DESTROY,	 smc_realm_destroy,		true,  true),
	HANDLER_1(SMC_RMM_REALM_ACTIVATE,	 smc_realm_activate,		true,  true),
	HANDLER_3(SMC_RMM_REC_CREATE,		 smc_rec_create,		true,  true),
	HANDLER_1(SMC_RMM_REC_DESTROY,		 smc_rec_destroy,		true,  true),
	HANDLER_2(SMC_RMM_REC_ENTER,		 smc_rec_enter,			false, true),
	HANDLER_5(SMC_RMM_DATA_CREATE,		 smc_data_create,		false, false),
	HANDLER_3(SMC_RMM_DATA_CREATE_UNKNOWN,	 smc_data_create_unknown,	false, false),
	HANDLER_2(SMC_RMM_DATA_DESTROY,		 smc_data_destroy,		false, true),
	HANDLER_4(SMC_RMM_RTT_CREATE,		 smc_rtt_create,		false, true),
	HANDLER_4(SMC_RMM_RTT_DESTROY,		 smc_rtt_destroy,		false, true),
	HANDLER_4(SMC_RMM_RTT_FOLD,		 smc_rtt_fold,			false, true),
	HANDLER_4(SMC_RMM_RTT_MAP_UNPROTECTED,	 smc_rtt_map_unprotected,	false, false),
	HANDLER_3(SMC_RMM_RTT_UNMAP_UNPROTECTED, smc_rtt_unmap_unprotected,	false, false),
	HANDLER_3_O(SMC_RMM_RTT_READ_ENTRY,	 smc_rtt_read_entry,		false, true, 4U),
	HANDLER_2(SMC_RMM_PSCI_COMPLETE,	 smc_psci_complete,		true,  true),
	HANDLER_1_O(SMC_RMM_REC_AUX_COUNT,	 smc_rec_aux_count,		true,  true, 1U),
	HANDLER_3(SMC_RMM_RTT_INIT_RIPAS,	 smc_rtt_init_ripas,		false, true),
	HANDLER_5(SMC_RMM_RTT_SET_RIPAS,	 smc_rtt_set_ripas,		false, true)
};

COMPILER_ASSERT(ARRAY_LEN(smc_handlers) == SMC64_NUM_FIDS_IN_RANGE(RMI));

static bool rmi_call_log_enabled = true;

static void rmi_log_on_exit(unsigned long handler_id,
			    unsigned long arg0,
			    unsigned long arg1,
			    unsigned long arg2,
			    unsigned long arg3,
			    unsigned long arg4,
			    struct smc_result *ret)
{
	const struct smc_handler *handler = &smc_handlers[handler_id];
	unsigned long function_id = SMC64_RMI_FID(handler_id);
	return_code_t rc;

	if (!handler->log_exec && !handler->log_error) {
		return;
	}

	if (function_id == SMC_RMM_VERSION) {
		/*
		 * RMM_VERSION is special because it returns the
		 * version number, not the error code.
		 */
		INFO("%-29s %8lx %8lx %8lx %8lx %8lx > %lx\n",
		     handler->fn_name, arg0, arg1, arg2, arg3, arg4,
		     ret->x[0]);
		return;
	}

	rc = unpack_return_code(ret->x[0]);

	if ((handler->log_exec) ||
	    (handler->log_error && (rc.status != RMI_SUCCESS))) {
		INFO("%-29s %8lx %8lx %8lx %8lx %8lx > ",
			handler->fn_name, arg0, arg1, arg2, arg3, arg4);
		if (rc.status >= RMI_ERROR_COUNT) {
			INFO("%lx", ret->x[0]);
		} else {
			INFO("%s", status_handler[rc.status]);
		}

		/* Check for index */
		if (((function_id == SMC_RMM_REC_ENTER) &&
		     (rc.status == RMI_ERROR_REALM)) ||
		     (rc.status == RMI_ERROR_RTT)) {
			INFO(" %x", rc.index);
		}

		/* Print output values */
		for (unsigned int i = 1U; i <= handler->out_values; i++) {
			INFO(" %8lx", ret->x[i]);
		}

		INFO("\n");
	}
}

void handle_ns_smc(unsigned long function_id,
		   unsigned long arg0,
		   unsigned long arg1,
		   unsigned long arg2,
		   unsigned long arg3,
		   unsigned long arg4,
		   unsigned long arg5,
		   struct smc_result *ret)
{
	unsigned long handler_id;
	const struct smc_handler *handler = NULL;

	if (IS_SMC64_RMI_FID(function_id)) {
		handler_id = SMC_RMI_HANDLER_ID(function_id);
		if (handler_id < ARRAY_LEN(smc_handlers)) {
			handler = &smc_handlers[handler_id];
		}
	}

	/*
	 * Check if handler exists and 'fn_dummy' is not NULL
	 * for not implemented 'function_id' calls in SMC RMI range.
	 */
	if ((handler == NULL) || (handler->fn_dummy == NULL)) {
		VERBOSE("[%s] unknown function_id: %lx\n",
			__func__, function_id);
		ret->x[0] = SMC_UNKNOWN;
		return;
	}

	assert_cpu_slots_empty();

	switch (handler->type) {
	case rmi_type_0:
		ret->x[0] = handler->f0();
		break;
	case rmi_type_1:
		ret->x[0] = handler->f1(arg0);
		break;
	case rmi_type_2:
		ret->x[0] = handler->f2(arg0, arg1);
		break;
	case rmi_type_3:
		ret->x[0] = handler->f3(arg0, arg1, arg2);
		break;
	case rmi_type_4:
		ret->x[0] = handler->f4(arg0, arg1, arg2, arg3);
		break;
	case rmi_type_5:
		ret->x[0] = handler->f5(arg0, arg1, arg2, arg3, arg4);
		break;
	case rmi_type_1_o:
		handler->f1_o(arg0, ret);
		break;
	case rmi_type_3_o:
		handler->f3_o(arg0, arg1, arg2, ret);
		break;
	default:
		assert(false);
	}

	if (rmi_call_log_enabled) {
		rmi_log_on_exit(handler_id, arg0, arg1, arg2, arg3, arg4, ret);
	}

	assert_cpu_slots_empty();
}

static void report_unexpected(void)
{
	unsigned long spsr = read_spsr_el2();
	unsigned long esr = read_esr_el2();
	unsigned long elr = read_elr_el2();
	unsigned long far = read_far_el2();

	INFO("----\n");
	INFO("Unexpected exception:\n");
	INFO("SPSR_EL2: 0x%016lx\n", spsr);
	INFO("ESR_EL2:  0x%016lx\n", esr);
	INFO("ELR_EL2:  0x%016lx\n", elr);
	INFO("FAR_EL2:  0x%016lx\n", far);
	INFO("----\n");

}

unsigned long handle_realm_trap(unsigned long *regs)
{
	report_unexpected();

	while (1) {
		wfe();
	}
}

/*
 * Identifies an abort that the RMM may recover from.
 */
struct rmm_trap_element {
	/*
	 * The PC at the time of abort.
	 */
	unsigned long aborted_pc;
	/*
	 * New value of the PC.
	 */
	unsigned long new_pc;
};

#define RMM_TRAP_HANDLER(_aborted_pc, _new_pc) \
	{ .aborted_pc = (unsigned long)(&_aborted_pc), \
	  .new_pc = (unsigned long)(&_new_pc) }

/*
 * The registered locations of load/store instructions that access NS memory.
 */
extern void *ns_read;
extern void *ns_write;

/*
 * The new value of the PC when the GPF occurs on a registered location.
 */
extern void *ns_access_ret_0;

struct rmm_trap_element rmm_trap_list[] = {
	RMM_TRAP_HANDLER(ns_read, ns_access_ret_0),
	RMM_TRAP_HANDLER(ns_write, ns_access_ret_0),
};
#define RMM_TRAP_LIST_SIZE (sizeof(rmm_trap_list)/sizeof(struct rmm_trap_element))

static void fatal_abort(void)
{
	report_unexpected();

	while (1) {
		wfe();
	}
}

static bool is_el2_data_abort_gpf(unsigned long esr)
{
	if (((esr & ESR_EL2_EC_MASK) == ESR_EL2_EC_DATA_ABORT_SEL) &&
	    ((esr & ESR_EL2_ABORT_FSC_MASK) == ESR_EL2_ABORT_FSC_GPF))
		return true;
	return false;
}

/*
 * Handles the RMM's aborts.
 * It compares the PC at the time of the abort with the registered addresses.
 * If it finds a match, it returns the new value of the PC that the RMM should
 * continue from. Other register values are preserved.
 * If no match is found, it aborts the RMM.
 */
unsigned long handle_rmm_trap(void)
{
	int i;

	unsigned long esr = read_esr_el2();
	unsigned long elr = read_elr_el2();

	/*
	 * Only the GPF data aborts are recoverable.
	 */
	if (!is_el2_data_abort_gpf(esr)) {
		fatal_abort();
	}

	for (i = 0; i < RMM_TRAP_LIST_SIZE; i++) {
		if (rmm_trap_list[i].aborted_pc == elr) {
			return rmm_trap_list[i].new_pc;
		}
	}

	fatal_abort();
	return 0;
}
