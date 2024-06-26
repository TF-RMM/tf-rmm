/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef STRING_H
#define STRING_H

#include <stddef.h>

int memcmp(const void *s1, const void *s2, size_t n);
void *memcpy(void *dest, const void *src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
void *memset(void *s, int c, size_t n);

int strcmp(const char *s1, const char *s2);
size_t strlen(const char *s);
size_t strlcpy(char *dst, const char *src, size_t dsize);
int strncmp(const char *s1, const char *s2, size_t n);
size_t strnlen(const char *s, size_t maxlen);
char *strchr(const char *s, int c);

#endif
