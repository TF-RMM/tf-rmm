/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_HEADER_PRIVATE_H
#define APP_HEADER_PRIVATE_H

#ifndef __ASSEMBLER__
#include <app_header_structures.h>
#include <stddef.h>
#include <stdint.h>
#endif

#define APP_HEADER_MAGIC	0x000E10ABB4EAD000UL  /* El0 APP HEAD */

#define HEADER_VERSION_MAJOR	0U
#define HEADER_VERSION_MINOR	1U
#define HEADER_VERSION		((HEADER_VERSION_MAJOR << 16) | HEADER_VERSION_MINOR)

#ifndef __ASSEMBLER__

/*
 * Get the index of the app from the app_id.
 *
 * Apps are indexed starting from 0, in the same order they appear in the RMM
 * image.
 *
 * Arguments:
 *	- app_id: The id of the app.
 *	- app_idx: Out parameter, the index of the app with `app_id`.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int app_get_index(unsigned long app_id, size_t *app_index);

/*
 * Return a pointer to the app_header structure of an app of an app_id.
 *
 * Arguments:
 *	- app_id: The id of the app.
 *	- app_header: Out parameter, pointer to the app header of the `app_id`.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int app_get_header_ptr(unsigned long app_id, struct app_header **app_header);

/*
 * Get the number of instance specific pages that are necessary for the app.
 *
 * This can be used to get the number of instance specific granules necessary
 * to instantiate an application that is identified by the app_header.
 *
 * Arguments:
 *	- app_header: pointer to the app header.
 *
 * Return:
 *	- The number of granules necessary.
 */
size_t app_get_required_granule_count_from_header(struct app_header *app_header);

#endif

#endif /* APP_HEADER_PRIVATE_H */
