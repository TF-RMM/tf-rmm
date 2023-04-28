/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <stdint.h>

uint8_t sve_rdvl(void)
{
	return 0;
}

void sve_save_zcr_fpu_state(unsigned long *data)
{
	(void)data;
}

void sve_save_z_state(unsigned char *data)
{
	(void)data;
}

void sve_save_p_ffr_state(unsigned char *data)
{
	(void)data;
}

void sve_restore_zcr_fpu_state(unsigned long *data)
{
	(void)data;
}

void sve_restore_z_state(unsigned char *data)
{
	(void)data;
}

void sve_restore_ffr_p_state(unsigned char *data)
{
	(void)data;
}
