#define ARRAY_SIZE 256
#define ITERATIONS 10

// Global arrays to exercise the cache
int data_array[ARRAY_SIZE];
int result_array[ARRAY_SIZE];

// Simple cache test function
void cache_test() {
    // Initialize data array
    for (int i = 0; i < ARRAY_SIZE; i++) {
        data_array[i] = i * 2;
    }
    
    // Perform multiple iterations of array operations
    for (int iter = 0; iter < ITERATIONS; iter++) {
        // Sequential access pattern (good for set-associative cache)
        for (int i = 0; i < ARRAY_SIZE; i++) {
            result_array[i] = data_array[i] + iter;
        }
        
        // Random access pattern (more challenging for cache)
        for (int i = 0; i < ARRAY_SIZE; i += 16) {
            result_array[i] += data_array[(i + 64) % ARRAY_SIZE];
        }
        
        // Backward access pattern
        for (int i = ARRAY_SIZE - 1; i >= 0; i--) {
            data_array[i] = result_array[i] + 1;
        }
    }
}

int main() {
    cache_test();
    
    // Calculate checksum to ensure test completed
    int checksum = 0;
    for (int i = 0; i < ARRAY_SIZE; i++) {
        checksum += data_array[i] + result_array[i];
    }
    
    // Signal success (test completed)
    return 0;
}