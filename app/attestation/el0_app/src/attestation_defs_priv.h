/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * TODO: Include a reference the RMM spec once the attestation
 * token spec is included on the former.
 */

#ifndef ATTESTATION_DEFS_PRIV_H
#define ATTESTATION_DEFS_PRIV_H

#define CCA_REALM_CHALLENGE			(10)
#define CCA_REALM_PERSONALIZATION_VALUE		(44235)
#define CCA_REALM_HASH_ALGM_ID			(44236)
#define CCA_REALM_PUB_KEY			(44237)
#define CCA_REALM_INITIAL_MEASUREMENT		(44238)
#define CCA_REALM_EXTENSIBLE_MEASUREMENTS	(44239)
#define CCA_REALM_PUB_KEY_HASH_ALGO_ID		(44240)
#define CCA_REALM_PROFILE			(265)

#define TAG_CCA_TOKEN				(399)
#define CCA_PLAT_TOKEN				(44234)
#define CCA_REALM_DELEGATED_TOKEN		(44241)

#define CCA_REALM_PROFILE_STR			"tag:arm.com,2023:realm#1.0.0"

#endif /* ATTESTATION_DEFS_PRIV_H */
