/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <debug.h>

/* Maximum number of entries in the backtrace to display */
#define UNWIND_LIMIT	20U

/*
 * If "-fno-omit-frame-pointer" is used:
 *
 * The AArch64 AAPCS defines the format of the frame records and mandates the
 * usage of x29 as frame pointer.
 */

/* Frame records form a linked list in the stack */
struct frame_record {
	/* Previous frame record in the list */
	struct frame_record *parent;
	/* Return address of the function at this level */
	uintptr_t return_addr;
};

static inline uintptr_t extract_address(uintptr_t address)
{
	/*
	 * When pointer authentication is enabled, the LR value saved on the
	 * stack contains a PAC. It must be stripped to retrieve the return
	 * address.
	 */
	xpaci(address);
	return address;
}

/*
 * Returns true if the address points to a virtual address that can be read at
 * the current EL, false otherwise.
 */
static bool is_address_readable(uintptr_t address)
{
	ats1e2r(address);
	isb();

	/* If PAR_EL1.F == 1 the address translation was aborted */
	return ((read_par_el1() & PAR_EL1_F_BIT) == 0UL);
}

/*
 * Returns true if all the bytes in a given object are in mapped memory and an
 * LDR using this pointer would succeed, false otherwise.
 */
static bool is_valid_object(uintptr_t addr, size_t size)
{
	/* Check address and detect overflows */
	if ((addr == 0UL) || ((addr + size) < addr)) {
		return false;
	}

	/* A pointer not aligned properly could trigger an alignment fault */
	if ((addr & (sizeof(uintptr_t) - 1UL)) != 0UL) {
		return false;
	}

	/* Check that all the object is readable */
	for (size_t i = 0UL; i < size; i++) {
		if (!is_address_readable(addr + i)) {
			return false;
		}
	}

	return true;
}

/*
 * Returns true if the specified address is correctly aligned and points to a
 * valid memory region.
 */
static bool is_valid_jump_address(uintptr_t addr)
{
	/* Check 32-bit alignment */
	if ((addr == 0UL) || ((addr & (sizeof(uint32_t) - 1UL)) != 0U)) {
		return false;
	}

	return is_address_readable(addr);
}

/*
 * Returns true if the pointer points at a valid frame record, false otherwise.
 */
static bool is_valid_frame_record(struct frame_record *fr)
{
	return is_valid_object((uintptr_t)fr, sizeof(struct frame_record));
}

static void __unused unwind_stack(struct frame_record *fr)
{
	if (!is_valid_frame_record(fr)) {
		INFO("Corrupted frame pointer (frame record address = 0x%lx)\n",
			(uintptr_t)fr);
		return;
	}

	/*
	 * The last frame record pointer in the linked list at the beginning of
	 * the stack should be NULL unless stack is corrupted.
	 */
	for (unsigned int i = 0U; i < UNWIND_LIMIT; i++) {
		uintptr_t call_site;

		/* If an invalid frame record is found, exit. */
		if (!is_valid_frame_record(fr)) {
			return;
		}

		/*
		 * AArch64 instructions are fixed length so the address from
		 * where the call was made is the instruction before the return
		 * address, which is always 4 bytes before it.
		 */
		call_site = extract_address(fr->return_addr) - 4UL;

		/*
		 * If the address is invalid it means that the frame record is
		 * probably corrupted.
		 */
		if (!is_valid_jump_address(call_site)) {
			return;
		}

		INFO("%s", (i == 0U) ? "BACKTRACE:" : "\t");
		INFO("\t0x%016lx\n", call_site);

		fr = fr->parent;
	}

	INFO("Max backtrace depth reached\n");
}

/*
 * Display a backtrace.
 *
 * Many things can prevent displaying the expected backtrace. For example,
 * compiler optimizations can use a branch instead of branch with link when it
 * detects a tail call. The backtrace level for this caller will not be
 * displayed, as it does not appear in the call stack anymore. Also, assembly
 * functions will not be displayed unless they setup AAPCS compliant frame
 * records on AArch64.
 *
 * Usage of the trace: addr2line can be used to map the addresses to function
 * and source code location when given the ELF file compiled with debug
 * information. The "-i" flag is highly recommended to improve display of
 * inlined function. The *.dump files generated when building each image can
 * also be used.
 *
 * WARNING: In case of corrupted stack, this function could display security
 * sensitive information past the beginning of the stack so it must not be used
 * in production build. This function is only called for Debug builds with
 * "-fno-omit-frame-pointer" option.
 */
void backtrace(uintptr_t frame_pointer)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)frame_pointer;

#if !defined(NDEBUG) && (LOG_LEVEL >= LOG_LEVEL_INFO)
	unwind_stack((struct frame_record *)frame_pointer);
#endif
}
