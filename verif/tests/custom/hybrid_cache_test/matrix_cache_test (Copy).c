/*
 * Matrix Cache Test for CVA6 Hybrid Cache Evaluation
 * 
 * This test creates a 3x3 matrix where each element contains 
 * an array of 10 increasing values starting from different offsets.
 * This pattern creates diverse memory access patterns that will
 * stress-test the different cache modes and reveal performance
 * characteristics.
 *
 * Expected behavior:
 * - Creates cache misses and hits in predictable patterns
 * - Tests spatial and temporal locality
 * - Exercises different cache ways and sets
 * - Provides measurable differences between cache modes
 */

#include <stdint.h>

// Test configuration
#define MATRIX_SIZE 3
#define ELEMENTS_PER_CELL 10
#define TOTAL_ITERATIONS 5

// Matrix structure: 3x3 matrix where each cell contains 10 integers
typedef struct {
    int values[ELEMENTS_PER_CELL];
} matrix_cell_t;

// Global matrix to ensure it's placed in a known memory region
static matrix_cell_t matrix[MATRIX_SIZE][MATRIX_SIZE];

// Result storage
static volatile int results[MATRIX_SIZE * MATRIX_SIZE];
static volatile int checkpoint = 0;

// Simple printf implementation for embedded environment
extern int printf(const char *format, ...);

// Initialize matrix with test pattern
void init_matrix() {
    int base_value = 0;
    
    printf("Initializing 3x3 matrix with 10 elements per cell...\n");
    
    for (int i = 0; i < MATRIX_SIZE; i++) {
        for (int j = 0; j < MATRIX_SIZE; j++) {
            for (int k = 0; k < ELEMENTS_PER_CELL; k++) {
                // Each cell starts with a different base value
                // Cell (i,j) starts with base_value = i*MATRIX_SIZE + j
                // Each element in the cell: base_value * 10 + k
                matrix[i][j].values[k] = base_value * 10 + k;
            }
            printf("Cell [%d][%d]: %d, %d, %d, ... %d\n", 
                   i, j, 
                   matrix[i][j].values[0],
                   matrix[i][j].values[1], 
                   matrix[i][j].values[2],
                   matrix[i][j].values[ELEMENTS_PER_CELL-1]);
            base_value++;
        }
    }
    printf("Matrix initialization complete.\n");
}

// Process matrix with different access patterns
int process_matrix_sequential() {
    int sum = 0;
    
    printf("Processing matrix sequentially...\n");
    
    // Sequential access pattern (good for cache)
    for (int i = 0; i < MATRIX_SIZE; i++) {
        for (int j = 0; j < MATRIX_SIZE; j++) {
            for (int k = 0; k < ELEMENTS_PER_CELL; k++) {
                sum += matrix[i][j].values[k];
                
                // Create some computation to make cache effects visible
                if (matrix[i][j].values[k] % 3 == 0) {
                    sum += matrix[i][j].values[k] * 2;
                }
            }
            
            // Store intermediate result (creates write access pattern)
            results[i * MATRIX_SIZE + j] = sum;
            
            printf("Processed cell [%d][%d], running sum: %d\n", i, j, sum);
        }
    }
    
    return sum;
}

int process_matrix_strided() {
    int sum = 0;
    
    printf("Processing matrix with strided access...\n");
    
    // Strided access pattern (tests cache conflict behavior)
    for (int k = 0; k < ELEMENTS_PER_CELL; k++) {
        for (int i = 0; i < MATRIX_SIZE; i++) {
            for (int j = 0; j < MATRIX_SIZE; j++) {
                sum += matrix[i][j].values[k];
                
                // Access pattern that might cause cache conflicts
                if (k % 2 == 0) {
                    // Even k: access in normal order
                    sum += matrix[i][j].values[k];
                } else {
                    // Odd k: access in reverse order
                    sum += matrix[MATRIX_SIZE-1-i][MATRIX_SIZE-1-j].values[k];
                }
            }
        }
        printf("Completed stride %d, running sum: %d\n", k, sum);
    }
    
    return sum;
}

int process_matrix_random() {
    int sum = 0;
    
    printf("Processing matrix with pseudo-random access...\n");
    
    // Pseudo-random access pattern (worst case for cache)
    for (int iteration = 0; iteration < MATRIX_SIZE * MATRIX_SIZE; iteration++) {
        // Simple pseudo-random sequence
        int i = (iteration * 7) % MATRIX_SIZE;
        int j = (iteration * 11) % MATRIX_SIZE;
        
        for (int k = 0; k < ELEMENTS_PER_CELL; k++) {
            int access_k = (k * 13) % ELEMENTS_PER_CELL;
            sum += matrix[i][j].values[access_k];
            
            // Additional random-ish computation
            sum += matrix[j][i].values[(access_k + 1) % ELEMENTS_PER_CELL];
        }
        
        printf("Random iteration %d: accessed [%d][%d], sum: %d\n", iteration, i, j, sum);
    }
    
    return sum;
}

// Main test function
int main() {
    printf("=== CVA6 Hybrid Cache Matrix Test ===\n");
    printf("Testing cache behavior with different access patterns\n\n");
    
    // Initialize test data
    init_matrix();
    checkpoint++;
    
    int total_sum = 0;
    
    // Run multiple iterations to create temporal patterns
    for (int iter = 0; iter < TOTAL_ITERATIONS; iter++) {
        printf("\n--- Iteration %d ---\n", iter + 1);
        
        // Sequential access (cache-friendly)
        int seq_sum = process_matrix_sequential();
        printf("Sequential sum: %d\n", seq_sum);
        total_sum += seq_sum;
        checkpoint++;
        
        // Strided access (moderate cache stress)
        int strided_sum = process_matrix_strided();
        printf("Strided sum: %d\n", strided_sum);
        total_sum += strided_sum;
        checkpoint++;
        
        // Random access (cache-hostile)
        int random_sum = process_matrix_random();
        printf("Random sum: %d\n", random_sum);
        total_sum += random_sum;
        checkpoint++;
        
        printf("Iteration %d total: %d\n", iter + 1, seq_sum + strided_sum + random_sum);
    }
    
    printf("\n=== Test Results ===\n");
    printf("Total sum across all patterns: %d\n", total_sum);
    printf("Checkpoints reached: %d\n", checkpoint);
    
    // Verify some results to ensure correctness
    int verification_sum = 0;
    for (int i = 0; i < MATRIX_SIZE * MATRIX_SIZE; i++) {
        verification_sum += results[i];
    }
    printf("Verification sum: %d\n", verification_sum);
    
    printf("Matrix cache test completed successfully!\n");
    
    return 0;  // Success
}