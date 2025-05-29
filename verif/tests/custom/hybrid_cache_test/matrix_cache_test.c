#include <stdio.h>
#include <stdint.h>

// Simple matrix cache test - very lightweight
#define MATRIX_SIZE 10

// Global matrix to test cache behavior
int matrix[MATRIX_SIZE][MATRIX_SIZE];

int main() {
    printf("Starting simple matrix cache test...\n");
    
    // Simple nested loop to test cache patterns
    for (int i = 0; i < MATRIX_SIZE; i++) {
        for (int j = 0; j < MATRIX_SIZE; j++) {
            // Simple computation to generate cache activity
            matrix[i][j] = j;
        }
    }
    
    // Read back to verify and generate more cache activity
    int sum = 0;
    for (int i = 0; i < MATRIX_SIZE; i++) {
        for (int j = 0; j < MATRIX_SIZE; j++) {
            sum += matrix[i][j];
        }
    }
    
    printf("Matrix test completed. Sum = %d\n", sum);
    printf("Expected sum = %d\n", MATRIX_SIZE*(((MATRIX_SIZE-1) * ((MATRIX_SIZE-1)+1)) / 2));
    
    return 0;
}
