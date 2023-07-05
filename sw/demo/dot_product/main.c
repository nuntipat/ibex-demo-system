#include "demo_system.h"

#define NUM_ELEMENT 5

int main(void)
{
    uint8_t a[NUM_ELEMENT];
    uint8_t b[NUM_ELEMENT] = {10, 20, 30, 40, 50};

    while (1) {
        uint32_t sum = 0;
    
        // get input
        int tmp;
        for (int i=0; i<NUM_ELEMENT; i++) {
            while ((tmp = getchar()) == UART_EOF);
            a[i] = tmp;
        }

        // send input back to host for verification
        for (int i=0; i<NUM_ELEMENT; i++) {
            uart_out(DEFAULT_UART, a[i]);
        }

        // perform calulation
        asm volatile ("fence.i");
        set_outputs(GPIO_OUT, 0x01);
        asm volatile ("fence.i");
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        for (int i=0; i<NUM_ELEMENT; i++) {
            sum += a[i] * b[i];
        }
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("fence.i");
        set_outputs(GPIO_OUT, 0x00);
        asm volatile ("fence.i");
        
        // send result back to host for verification
        puthex(sum);
        putchar('\n');
    }    

    return 0;
}