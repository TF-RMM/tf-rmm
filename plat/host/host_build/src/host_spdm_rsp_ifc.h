/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_SPDM_RSP_IFC_H
#define HOST_SPDM_RSP_IFC_H

#include <stdbool.h>

#define SPDM_RSP_DEFAULT_HOST_ADDR	"127.0.0.1"
#define SPDM_RSP_EMU1_PORT		2323
#define SPDM_RSP_EMU2_PORT		2324
#define SPDM_RSP_EMU_MAX		2

/*
 * spdm_responder_emu commands and format
 * command: 4 byte
 * transport_type: 4 bytes
 * Payload
 */

/* Commmand types used */
#define SOCKET_SPDM_COMMAND_NORMAL	0x0001
#define SOCKET_SPDM_COMMAND_SHUTDOWN	0xFFFE

/* Transport type used */
#define SOCKET_TRANSPORT_TYPE_PCI_DOE	0x02

int host_spdm_rsp_init(const char *host_addr, uint32_t port, int *spdm_rsp_id);
int host_spdm_rsp_connect(int *spdm_rsp_id);
int host_spdm_rsp_deinit(int spdm_rsp_id);
int host_spdm_rsp_communicate(int spdm_rsp_id, void *req_buf, size_t req_sz,
			      void *rsp_buf, size_t *rsp_sz, bool is_sspdm);

#endif /* HOST_SPDM_RSP_IFC_H */
