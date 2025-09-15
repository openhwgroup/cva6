// Copyright (c) 2025 Thales Research and Technology
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
/**
 * \file bootrom_errno.h
 * \brief Contains error numbers useful for our bootrom.
 * \author Julien Mallet
*/

#ifndef BOOTROM_ERRNO_H
#define BOOTROM_ERRNO_H


#define	EIO		 5	/* I/O error */
#define	EBUSY		16	/* Device or resource busy */
#define	EINVAL		22	/* Invalid argument */
#define	ECOMM		70	/* Communication error on send */
#define	EOPNOTSUPP	95	/* Operation not supported on transport endpoint */
#define	ETIMEDOUT	110	/* Connection timed out */

#define ENOTSUPP	255	/* Operation is not supported */

#ifndef ENOMEM
#define ENOMEM 12
#endif
#endif