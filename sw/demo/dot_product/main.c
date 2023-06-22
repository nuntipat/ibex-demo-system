#include "demo_system.h"

int main(void)
{
    uint8_t a[10];
    uint8_t b[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

    while (1) {
        uint32_t sum = 0;
    
        // get input
        int tmp;
        for (int i=0; i<10; i++) {
            while ((tmp = getchar()) == UART_EOF);
            a[i] = tmp;
        }

        // send input back to host for verification
        for (int i=0; i<10; i++) {
            uart_out(DEFAULT_UART, a[i]);
        }

        // perform calulation
        set_outputs(GPIO_OUT, 0x01);
        asm volatile ("nop");
        asm volatile ("nop");
        for (int i=0; i<10; i++) {
            sum += a[i] * b[i];
        }
        asm volatile ("nop");
        asm volatile ("nop");
        set_outputs(GPIO_OUT, 0x00);

        // send result back to host for verification
        puthex(sum);
        putchar('\n');
    }    

    return 0;
}