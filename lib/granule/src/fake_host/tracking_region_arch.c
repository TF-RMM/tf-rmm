/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <errno.h>
#ifndef CBMC
#include <linux/memfd.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#endif
#include <tracking_region_arch.h>
#ifndef CBMC
#include <unistd.h>
#endif
#include <utils_def.h>

#ifndef CBMC
/*
 * One VA reservation each for the struct tracking_region array, the
 * conventional fine-granule array and the device fine-granule array.
 */
#define TRACKING_ARCH_MAX_RESERVATIONS	U(3)

struct tracking_arch_reservation {
	uintptr_t base;
	size_t size;
	uintptr_t *pages;
};

static struct tracking_arch_reservation
	tracking_arch_reservations[TRACKING_ARCH_MAX_RESERVATIONS];

/* Return the host reservation containing @va, or NULL if none does. */
static struct tracking_arch_reservation *tracking_arch_find(uintptr_t va)
{
	for (unsigned int i = 0U; i < TRACKING_ARCH_MAX_RESERVATIONS; i++) {
		struct tracking_arch_reservation *reservation =
			&tracking_arch_reservations[i];

		if ((reservation->size != 0UL) &&
		    (va >= reservation->base) &&
		    (va < (reservation->base + reservation->size))) {
			return reservation;
		}
	}

	return NULL;
}

#endif /* CBMC */

/* Reserve a host-selected contiguous VA without constructing xlat tables. */
int tracking_region_arch_reserve(size_t size, uintptr_t *va)
{
#ifdef CBMC
	(void)size;
	*va = 0x1000UL;
#else
	struct tracking_arch_reservation *reservation = NULL;
	void *ptr;

	ptr = mmap(NULL, size, PROT_NONE,
		   MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
	if (ptr == MAP_FAILED) {
		return -ENOMEM;
	}
	*va = (uintptr_t)ptr;

	for (unsigned int i = 0U; i < TRACKING_ARCH_MAX_RESERVATIONS; i++) {
		if (tracking_arch_reservations[i].size == 0UL) {
			reservation = &tracking_arch_reservations[i];
			break;
		}
	}
	if (reservation == NULL) {
		(void)munmap(ptr, size);
		return -ENOMEM;
	}

	reservation->pages = mmap(NULL,
			(size / GRANULE_SIZE) * sizeof(uintptr_t),
			PROT_READ | PROT_WRITE,
			MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
	if (reservation->pages == MAP_FAILED) {
		(void)munmap(ptr, size);
		reservation->pages = NULL;
		return -ENOMEM;
	}
	reservation->base = *va;
	reservation->size = size;
#endif

	return 0;
}

/* Alias one EL3 allocation into its reserved contiguous host VA. */
int tracking_region_arch_populate(uintptr_t va, uintptr_t pa,
				  size_t size)
{
#ifdef CBMC
	(void)va;
	(void)pa;
	(void)size;
#else
	struct tracking_arch_reservation *reservation;
	int fd;
	void *ptr;
	unsigned long page;

	reservation = tracking_arch_find(va);
	if ((reservation == NULL) ||
	    ((va + size) > (reservation->base + reservation->size))) {
		return -EINVAL;
	}

	fd = (int)syscall(SYS_memfd_create, "tracking_region", MFD_CLOEXEC);
	if (fd < 0) {
		return -ENOMEM;
	}
	if (ftruncate(fd, (off_t)size) != 0) {
		(void)close(fd);
		return -ENOMEM;
	}

	ptr = mmap((void *)pa, size, PROT_READ | PROT_WRITE,
		   MAP_FIXED | MAP_SHARED, fd, 0);
	if (ptr == MAP_FAILED) {
		(void)close(fd);
		return -ENOMEM;
	}
	/* Replace only the subrange reserved by tracking_region_arch_reserve(). */
	ptr = mmap((void *)va, size, PROT_READ | PROT_WRITE,
		   MAP_FIXED | MAP_SHARED, fd, 0);
	(void)close(fd);
	if (ptr == MAP_FAILED) {
		return -ENOMEM;
	}

	page = (va - reservation->base) / GRANULE_SIZE;
	for (unsigned long i = 0UL; i < (size / GRANULE_SIZE); i++) {
		/* Bit zero records presence without excluding a valid physical page zero. */
		reservation->pages[page + i] =
			(pa + (i * GRANULE_SIZE)) | 1UL;
	}
#endif

	return 0;
}

/* Return the simulated PA aliased at a tracking-metadata VA. */
uintptr_t tracking_region_arch_to_pa(uintptr_t va)
{
#ifdef CBMC
	return va;
#else
	struct tracking_arch_reservation *reservation = tracking_arch_find(va);
	unsigned long page;

	assert(reservation != NULL);
	page = (va - reservation->base) / GRANULE_SIZE;
	assert(reservation->pages[page] != 0UL);
	return (reservation->pages[page] & ~1UL) +
	       (va & (GRANULE_SIZE - 1UL));
#endif
}

/* Return whether @va already has a simulated backing page. */
bool tracking_region_arch_is_mapped(uintptr_t va)
{
#ifdef CBMC
	(void)va;
	return true;
#else
	struct tracking_arch_reservation *reservation = tracking_arch_find(va);
	unsigned long page;

	if (reservation == NULL) {
		return false;
	}
	page = (va - reservation->base) / GRANULE_SIZE;
	return reservation->pages[page] != 0UL;
#endif
}

/* Restore PROT_NONE over a host tracking-metadata VA subrange. */
int tracking_region_arch_depopulate(uintptr_t va, size_t size)
{
#ifdef CBMC
	(void)va;
	(void)size;
#else
	struct tracking_arch_reservation *reservation = tracking_arch_find(va);
	void *ptr;
	unsigned long page;

	if ((reservation == NULL) ||
	    ((va + size) > (reservation->base + reservation->size))) {
		return -EINVAL;
	}
	ptr = mmap((void *)va, size, PROT_NONE,
		   MAP_ANONYMOUS | MAP_FIXED | MAP_PRIVATE, -1, 0);
	if (ptr == MAP_FAILED) {
		return -ENOMEM;
	}

	page = (va - reservation->base) / GRANULE_SIZE;
	for (unsigned long i = 0UL; i < (size / GRANULE_SIZE); i++) {
		reservation->pages[page + i] = 0UL;
	}
#endif

	return 0;
}
