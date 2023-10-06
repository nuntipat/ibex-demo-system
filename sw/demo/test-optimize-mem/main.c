static int x[2] = {1, 2};

int main() {
    asm ("nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "nop\n\t"
         "sw t0, 0(%0)\n\t"
         "lb t0, 0(%0)\n\t"
         "lh t0, 1(%0)\n\t"
         "lw t0, 2(%0)\n\t"
         "sw t1, -2(%1)\n\t"
         "sw t2, 0(%1)\n\t"
         "sw t0, 4(%1)\n\t"
        : 
        : "r" (&x[0]), "r" (&x[1])
        : "t0", "t1", "t2");

    return 0;
}