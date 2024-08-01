/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_HEADER_H
#define APP_HEADER_H

#ifndef __ASSEMBLER__
#include <app_header_structures.h>
#endif

#define APP_COUNT		0U

#ifndef __ASSEMBLER__

/*
 * Return the RMM image start address.
 *
 * Return:
 *	- The physical address of the start of the RMM image.
 */
uint64_t app_get_rmm_start(void);

/*
 * Return a pointer to the app_header structure at an index.
 *
 * Arguments:
 *	- app_idx: The index of the app
 *	- app_header: Out parameter, pointer to the app header of the `app_idx`.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int app_get_header_ptr_at_index(unsigned long app_index, struct app_header **app_header);

/*
 * Initialise the internal app header structures.
 *
 * This function must be called once during cold boot to initialise the internal
 * app header structures.
 */
void app_info_setup(void);
#endif

#endif /* APP_HEADER_H */
