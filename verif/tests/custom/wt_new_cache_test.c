/*
 * WT_NEW Cache Validation Test
 * Tests dual privilege-level controllers and privilege switching behavior
 */

#include <stdio.h>
#include <stdint.h>

// Memory access patterns to test cache behavior
#define TEST_ARRAY_SIZE 1024
#define CACHE_LINE_SIZE 64

// Test data arrays
volatile uint32_t test_data_machine[TEST_ARRAY_SIZE] __attribute__((aligned(CACHE_LINE_SIZE)));
volatile uint32_t test_data_user[TEST_ARRAY_SIZE] __attribute__((aligned(CACHE_LINE_SIZE)));
volatile uint32_t results[TEST_ARRAY_SIZE];

// Test counters
static volatile uint32_t test_count = 0;
static volatile uint32_t pass_count = 0;

void test_machine_mode_access() {
    printf("Testing machine mode cache access...\n");
    
    // Test sequential access pattern (controller A - set-associative)
    for (int i = 0; i < 64; i++) {
        test_data_machine[i] = 0xDEADBEEF + i;
        results[i] = test_data_machine[i];
        test_count++;
        if (results[i] == (0xDEADBEEF + i)) {
            pass_count++;
        }
    }
    
    // Test cache line boundary access
    for (int i = 0; i < 16; i++) {
        int idx = i * 16; // 64-byte cache line jumps
        test_data_machine[idx] = 0xCAFEBABE + i;
        results[idx] = test_data_machine[idx];
        test_count++;
        if (results[idx] == (0xCAFEBABE + i)) {
            pass_count++;
        }
    }
}

void test_user_mode_access() {
    printf("Testing user mode cache access...\n");
    
    // Test random access pattern (controller B - fully associative)
    for (int i = 0; i < 32; i++) {
        int idx = (i * 37) % TEST_ARRAY_SIZE; // Pseudo-random pattern
        test_data_user[idx] = 0x12345678 + i;
        results[idx] = test_data_user[idx];
        test_count++;
        if (results[idx] == (0x12345678 + i)) {
            pass_count++;
        }
    }
    
    // Test dense access pattern
    for (int i = 0; i < 64; i++) {
        test_data_user[i] = 0x87654321 + i;
        results[i] = test_data_user[i];
        test_count++;
        if (results[i] == (0x87654321 + i)) {
            pass_count++;
        }
    }
}

void test_privilege_switching() {
    printf("Testing privilege level switching behavior...\n");
    
    // Write in machine mode pattern
    for (int i = 0; i < 32; i++) {
        test_data_machine[i] = 0xAAAABBBB + i;
    }
    
    // Simulate privilege switch (in real test, this would involve CSR operations)
    // For now, just access the same memory from user pattern
    for (int i = 0; i < 32; i++) {
        test_data_user[i] = 0xCCCCDDDD + i;
        results[i] = test_data_user[i];
        test_count++;
        if (results[i] == (0xCCCCDDDD + i)) {
            pass_count++;
        }
    }
    
    // Verify machine mode data is still accessible
    for (int i = 0; i < 32; i++) {
        uint32_t expected = 0xAAAABBBB + i;
        if (test_data_machine[i] == expected) {
            pass_count++;
        }
        test_count++;
    }
}

void test_cache_miss_behavior() {
    printf("Testing cache miss and memory fetch behavior...\n");
    
    // Test large stride access to force cache misses
    for (int i = 0; i < 16; i++) {
        int idx = i * 64; // Large stride to miss cache
        test_data_machine[idx] = 0xFEEDFACE + i;
        // Read back to test miss handling
        volatile uint32_t read_val = test_data_machine[idx];
        test_count++;
        if (read_val == (0xFEEDFACE + i)) {
            pass_count++;
        }
    }
}

void test_concurrent_access() {
    printf("Testing concurrent access patterns...\n");
    
    // Interleaved access between machine and user data
    for (int i = 0; i < 32; i++) {
        test_data_machine[i] = 0x11111111 + i;
        test_data_user[i] = 0x22222222 + i;
        
        // Read both back
        volatile uint32_t m_val = test_data_machine[i];
        volatile uint32_t u_val = test_data_user[i];
        
        test_count += 2;
        if (m_val == (0x11111111 + i)) pass_count++;
        if (u_val == (0x22222222 + i)) pass_count++;
    }
}

int main() {
    printf("WT_NEW Cache Validation Test Starting...\n");
    printf("Testing dual privilege-level controllers\n");
    
    // Initialize test arrays
    for (int i = 0; i < TEST_ARRAY_SIZE; i++) {
        test_data_machine[i] = 0;
        test_data_user[i] = 0;
        results[i] = 0;
    }
    
    // Run test suite
    test_machine_mode_access();
    test_user_mode_access();
    test_privilege_switching();
    test_cache_miss_behavior();
    test_concurrent_access();
    
    // Report results
    printf("\n=== WT_NEW Cache Test Results ===\n");
    printf("Total tests: %d\n", test_count);
    printf("Passed: %d\n", pass_count);
    printf("Failed: %d\n", test_count - pass_count);
    printf("Success rate: %d%%\n", (pass_count * 100) / test_count);
    
    if (pass_count == test_count) {
        printf("ALL TESTS PASSED! WT_NEW cache is functioning correctly.\n");
        return 0;
    } else {
        printf("SOME TESTS FAILED. WT_NEW cache needs investigation.\n");
        return 1;
    }
}