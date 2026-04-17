; Simple test program
START:
    ADD R1, R2      ; R1 = R1 + R2
    SUB R3, 100     ; R3 = R3 - 100
    MUL R4, R5      ; R4 = R4 * R5
LOOP:
    LD R6, R7       ; Load R7 into R6
    BNE LOOP        ; Branch if not equal
    BEQ START       ; Branch to start
.END
