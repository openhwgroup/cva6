// N2D2 auto-generated file.
// @ Fri Sep 10 16:23:21 2021

#ifndef N2D2_EXPORTC_CONV1_LAYER_H
#define N2D2_EXPORTC_CONV1_LAYER_H

#include "typedefs.h"
#include "utils.h"
#define CONV1_NB_OUTPUTS 16
#define CONV1_NB_CHANNELS 1
#define CONV1_OUTPUTS_WIDTH 11
#define CONV1_OUTPUTS_HEIGHT 11
#define CONV1_OX_SIZE 11
#define CONV1_OY_SIZE 11
#define CONV1_CHANNELS_WIDTH 24
#define CONV1_CHANNELS_HEIGHT 24
#define CONV1_KERNEL_WIDTH 4
#define CONV1_KERNEL_HEIGHT 4
#define CONV1_SUB_SAMPLE_X 1
#define CONV1_SUB_SAMPLE_Y 1
#define CONV1_STRIDE_X 2
#define CONV1_STRIDE_Y 2
#define CONV1_PADDING_X 0
#define CONV1_PADDING_Y 0
#define CONV1_NO_BIAS 1

#define CONV1_ACTIVATION Rectifier
#define CONV1_SHIFT 8
static const int32_t CONV1_SCALING_FACTOR_PER_OUTPUT[] = {0};

#define CONV1_OUTPUTS_SIZE (CONV1_NB_OUTPUTS*CONV1_OUTPUTS_WIDTH*CONV1_OUTPUTS_HEIGHT)
#define CONV1_CHANNELS_SIZE (CONV1_NB_CHANNELS*CONV1_CHANNELS_WIDTH*CONV1_CHANNELS_HEIGHT)

static const BDATA_T conv1_biases[CONV1_NB_OUTPUTS] = {0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, 0 + 128, };

#define CONV1_WEIGHTS_SIZE (CONV1_NB_OUTPUTS*CONV1_KERNEL_WIDTH*CONV1_KERNEL_HEIGHT*CONV1_NB_CHANNELS)

// Flatten weights with the order [NB_OUTPUTS][KERNEL_HEIGHT][KERNEL_WIDTH][NB_CHANNELS]
static const WDATA_T conv1_weights[CONV1_WEIGHTS_SIZE] = {13, 8, -6, -3, -10, -10, 1, 5, -4, 1, -5, 7, -2, -2, -6, -14, 6, -10, -7, -21, -32, -38, -40, -40, 
-42, -15, 9, 2, 17, 42, 37, 51, -45, -58, -61, -46, -7, -1, -6, -9, 35, 40, 47, 36, 16, 10, 17, 11, 
-33, -15, 6, 37, -33, -17, 13, 44, -31, -15, 29, 28, -30, -14, 5, 26, -13, 0, 10, 11, -28, -21, 24, 21, 
-27, 2, 23, 12, 0, -7, 13, -3, -5, 1, 22, 32, 0, -2, -13, 2, 1, -18, -38, -29, 3, 14, 25, 0, 
-9, -31, -22, 25, -15, -24, -7, 36, -24, -28, 6, 43, -18, -17, 10, 32, 37, 23, -1, -2, -4, -16, -1, -5, 
-21, -3, -11, 19, -15, -2, 12, 29, 16, 36, -4, -43, 52, 20, 35, -8, 44, 29, 14, -5, 20, 10, 32, 6, 
-56, 3, 27, 27, -28, 25, 27, 21, 23, 28, 39, -11, 22, 16, -25, -59, 1, 20, 35, 28, -19, -16, 22, 27, 
-33, -42, -27, -5, 1, -14, -9, -13, 8, -28, -11, 28, 26, -12, -46, 4, 25, 6, -12, 1, -3, 20, 1, -6, 
17, 17, 37, 54, 29, 26, 17, 33, -7, -12, -14, 3, -48, -48, -51, -33, -4, -5, -21, -21, 25, -1, -32, -65, 
19, 13, 5, -38, 22, 54, 49, 15, 8, 29, 53, 52, -34, -45, -13, 50, -30, -30, -52, -3, -4, -11, -26, -28, 
-1, -17, -12, -16, 16, -9, -2, 3, 12, 12, -7, -1, 21, -4, -10, -13, 
};

#endif // N2D2_EXPORTC_CONV1_LAYER_H
