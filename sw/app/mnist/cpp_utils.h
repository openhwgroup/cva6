/*
    (C) Copyright 2017 CEA LIST. All Rights Reserved.
    Contributor(s): Olivier BICHLER (olivier.bichler@cea.fr)
                    David BRIAND (david.briand@cea.fr)

    This software is governed by the CeCILL-C license under French law and
    abiding by the rules of distribution of free software.  You can  use,
    modify and/ or redistribute the software under the terms of the CeCILL-C
    license as circulated by CEA, CNRS and INRIA at the following URL
    "http://www.cecill.info".

    As a counterpart to the access to the source code and  rights to copy,
    modify and redistribute granted by the license, users are provided only
    with a limited warranty  and the software's author,  the holder of the
    economic rights,  and the successive licensors  have only  limited
    liability.

    The fact that you are presently reading this means that you have had
    knowledge of the CeCILL-C license and that you accept its terms.
*/

#ifndef CPP_UTILS_H
#define CPP_UTILS_H

#include "typedefs.h"
#include "env.h"

#ifdef NO_EXCEPT
#define N2D2_THROW_OR_ABORT(ex, msg) \
do { printf("%s\n", std::string(msg).c_str()); abort(); } while (false)
#else
// #include <stdexcept>
#define N2D2_THROW_OR_ABORT(ex, msg) throw ex(msg)
#endif
#define N2D2_ALWAYS_INLINE __attribute__((always_inline))

void envRead(unsigned int size,
             unsigned int channelsHeight,
             unsigned int channelsWidth,
             DATA_T* data,
             unsigned int outputsSize,
             Target_T* outputTargets);



#endif
