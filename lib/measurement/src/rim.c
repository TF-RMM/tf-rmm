/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <measurement.h>
#include <measurement_descs.h>
#include <string.h>

void measurement_data_granule_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      void *data,
				      unsigned long ipa,
				      unsigned long flags)
{
	struct measurement_desc_data measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_DATA;
	measure_desc.len = sizeof(struct measurement_desc_data);
	measure_desc.ipa = ipa;
	measure_desc.flags = flags;
	(void)memcpy(measure_desc.rim, rim_measurement,
					measurement_get_size(algorithm));

	if (flags == RMI_MEASURE_CONTENT) {
		/*
		 * Hashing the data granules and store the result in the
		 * measurement descriptor structure.
		 */
		measurement_hash_compute(algorithm,
					data,
					GRANULE_SIZE,
					measure_desc.content);
	}

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(measure_desc),
			       rim_measurement);
}

void measurement_realm_params_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      struct rmi_realm_params *realm_params)
{
	/*
	 * Allocate a zero-filled RmiRealmParams data structure
	 * to hold the measured Realm parameters.
	 */
	struct rmi_realm_params rim_params = {0};

	/*
	 * The following attributes are used for calculation of the
	 * initial RIM value of the Realm:
	 * - flags
	 * - s2sz
	 * - sve_vl
	 * - num_bps
	 * - num_wps
	 * - pmu_num_ctrs
	 * - hash_algo
	 */
	rim_params.flags = realm_params->flags;
	rim_params.s2sz = realm_params->s2sz;
	rim_params.sve_vl = realm_params->sve_vl;
	rim_params.num_bps = realm_params->num_bps;
	rim_params.num_wps = realm_params->num_wps;
	rim_params.pmu_num_ctrs = realm_params->pmu_num_ctrs;
	rim_params.algorithm = realm_params->algorithm;

	/* Measure relevant realm params this will be the init value of RIM */
	measurement_hash_compute(algorithm,
			       &rim_params,
			       sizeof(struct rmi_realm_params),
			       rim_measurement);
}

void measurement_rec_params_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    struct rmi_rec_params *rec_params)
{
	struct measurement_desc_rec measure_desc = {0};
	struct rmi_rec_params rec_params_measured = {0};

	/*
	 * Copy the following attributes of the RmiRecParams data
	 * structure into the measured REC parameters data structure:
	 * - gprs
	 * - pc
	 * - flags
	 */
	rec_params_measured.flags = rec_params->flags;
	rec_params_measured.pc = rec_params->pc;
	(void)memcpy(&rec_params_measured.gprs, rec_params->gprs,
					sizeof(rec_params->gprs));

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_REC;
	measure_desc.len = sizeof(struct measurement_desc_rec);
	(void)memcpy(measure_desc.rim, rim_measurement,
					measurement_get_size(algorithm));
	/*
	 * Hash the REC params structure and store the result in the
	 * measurement descriptor structure.
	 */
	measurement_hash_compute(algorithm,
				&rec_params_measured,
				sizeof(struct rmi_rec_params),
				measure_desc.content);
	/*
	 * Hash the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(struct measurement_desc_rec),
			       rim_measurement);
}

void measurement_init_ripas_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    unsigned long base,
				    unsigned long top)
{
	struct measurement_desc_ripas measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_RIPAS;
	measure_desc.len = sizeof(struct measurement_desc_ripas);
	measure_desc.base = base;
	measure_desc.top = top;
	(void)memcpy(measure_desc.rim,
		     rim_measurement,
		     measurement_get_size(algorithm));

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(algorithm,
				 &measure_desc,
				 sizeof(measure_desc),
				 rim_measurement);
}
