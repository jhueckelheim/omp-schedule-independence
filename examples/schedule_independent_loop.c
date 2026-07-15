#include <omp.h>
#include <stdio.h>

// This is the arbitrary pure function.
// For the proof, we don't need to know what it does, just that it's pure.
int pure_function(int i) {
    return i * i;
}

int main() {
    int n = 100;
    int output_array[100];

    #pragma omp parallel for
    for (int i = 0; i < n; i++) {
        output_array[i] = pure_function(i);
    }

    // Optional: verification step to demonstrate correctness in practice
    int correct = 1;
    for (int i = 0; i < n; i++) {
        if (output_array[i] != pure_function(i)) {
            correct = 0;
            break;
        }
    }

    if (correct) {
        printf("The loop is correct.\n");
    } else {
        printf("The loop is incorrect.\n");
    }

    return 0;
}
