#include <stdio.h>
#include <stdlib.h>

//__attribute__((destructor))
void XXX() {
    puts("gggg");
}

static int __attribute__((noinline))
myfunct(int *x, int n) {

    for (int i = 0; i < n; i++) {
        printf("%d\n", x[i]);
        printf("%d\n", x[i]);
        printf("%d\n", x[i]);
    }
}

int main() {
    int *arr = malloc(sizeof(int) * 10);

    return myfunct(arr, 10);
}
