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
	/* coverity[overrun-buffer-val:SUPPRESS] */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(measure_desc),
			       rim_measurement);
}

void measurement_init_rim(unsigned char rim_measurement[],
				      enum hash_algo algorithm)
{
	(void)memset(rim_measurement, 0, measurement_get_size(algorithm));
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
	/* coverity[overrun-buffer-val:SUPPRESS] */
	measurement_hash_compute(algorithm,
				&rec_params_measured,
				sizeof(struct rmi_rec_params),
				measure_desc.content);
	/*
	 * Hash the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	/* coverity[overrun-buffer-val:SUPPRESS] */
	measurement_hash_compute(algorithm,
			       &measure_desc,
			       sizeof(struct measurement_desc_rec),
			       rim_measurement);
}
