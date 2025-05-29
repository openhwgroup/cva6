// Simple loop test to verify hybrid cache functionality
// This test performs a simple loop that should be easy to trace

volatile int result = 0;

int main() {
    int a = 0;
    
    // Simple loop that accumulates values
    for (int i = 0; i < 5; i++) {
        a += i;
    }
    
    // Store result in volatile variable to prevent optimization
    result = a;
    
    // Expected result: 0 + 1 + 2 + 3 + 4 = 10
    // Return 0 for success
    return (a == 10) ? 0 : 1;
}