.START 0x1000

; ============================================================================
; TDC16.1v1 ASSEMBLER TEST PROGRAM
; Comprehensive test of all accepted instruction formats
; ============================================================================

; ============================================================================
; BRANCH INSTRUCTIONS - All condition codes
; ============================================================================

; Branch if Equal (Z=1)
LOOP:
    BEQ R5              ; Branch to address in R5
    BEQ 0x1000          ; Branch to absolute address
    BEQ LOOP            ; Branch to label
    BLEQ SUBROUTINE     ; Branch with link if equal

; Branch if Not Equal (Z=0)
    BNE R6              ; Branch if not equal
    BNE 0x2000          ; Branch to address
    BNE RETRY           ; Branch to label
    BLNE FUNCTION       ; Call function if not equal

; Branch if Carry Set (C=1)
    BCS R7
    BCS 0x3000
    BCS OVERFLOW_HANDLER
    BLCS ERROR_ROUTINE

; Branch if Carry Clear (C=0)
    BCC R8
    BCC 0x4000
    BCC NO_CARRY
    BLCC CONTINUE

; Branch if Higher or Same (unsigned >=)
    BHS R9
    BHS 0x5000
    BHS GREATER_EQUAL
    BLHS CHECK_UPPER

; Branch if Lower (unsigned <)
    BLO R10
    BLO 0x6000
    BLO LESS_THAN
    BLLO LOWER_ROUTINE

; Branch if Minus (N=1, negative)
    BMI R11
    BMI 0x7000
    BMI NEGATIVE
    BLMI NEG_HANDLER

; Branch if Plus (N=0, positive or zero)
    BPL R12
    BPL 0x8000
    BPL POSITIVE
    BLPL POS_HANDLER

; Branch if Overflow Set (V=1)
    BVS R13
    BVS 0x9000
    BVS OVERFLOW
    BLVS OVF_HANDLER

; Branch if Overflow Clear (V=0)
    BVC R14
    BVC 0xA000
    BVC NO_OVERFLOW
    BLVC NOOVF_HANDLER

; Branch if Higher (unsigned >)
    BHI R15
    BHI 0xB000
    BHI HIGHER
    BLHI HI_ROUTINE

; Branch if Lower or Same (unsigned <=)
    BLS R1
    BLS 0xC000
    BLS LOWER_SAME
    BLLS LS_ROUTINE

; Branch if Greater or Equal (signed >=)
    BGE R2
    BGE 0xD000
    BGE SIGNED_GE
    BLGE GE_ROUTINE

; Branch if Less Than (signed <)
    BLT R3
    BLT 0xE000
    BLT SIGNED_LT
    BLLT LT_ROUTINE

; Branch if Greater Than (signed >)
    BGT R4
    BGT 0xF000
    BGT SIGNED_GT
    BLGT GT_ROUTINE

; Branch if Less or Equal (signed <=)
    BLE R5
    BLE 0x1100
    BLE SIGNED_LE
    BLLE LE_ROUTINE

; Branch on Parity / Compare
    BPR R6              ; Branch on parity
    BPR 0x1200          ; Branch to address
    BPR PARITY_CHECK    ; Branch to label
    BPR R1, R2          ; Compare R1 and R2, set flags
    BPR R3, 100         ; Compare R3 with immediate

; Branch Always (unconditional jump)
    BA MAIN             ; Jump to label
    BA R7               ; Jump to address in R7
    BA 0x1300           ; Jump to absolute address
    BA (SP)+            ; Return from subroutine (RTS)

; Branch with Link Always (unconditional call)
    BLA FUNCTION        ; Call function
    BLA R8              ; Call address in R8
    BLA 0x1400          ; Call absolute address

; ============================================================================
; TEST INSTRUCTION
; ============================================================================

.ORG 0x1300

    TST R1, R2          ; Test R1 against R2 (compare, set flags)
    TST R3, 0xFF        ; Test R3 against immediate
    TST R4, 0b11110000  ; Test R4 with binary immediate

; ============================================================================
; LOAD INSTRUCTIONS - All addressing modes
; ============================================================================

    ; Register to register
    LD R1, R2           ; Copy R2 to R1

    ; Immediate to register
    LD R3, 0xFF         ; Load hex immediate
    LD R4, 255          ; Load decimal immediate
    LD R5, 0b11111111   ; Load binary immediate

    ; Stack operations
    LD -(SP), R6        ; Push R6 onto stack
    LD R7, (SP)+        ; Pop from stack into R7

    ; Load Multiple - Push multiple registers (only works with SP)
    LDM -(SP), {R1,R2,R6}       ; Push R1, R2, R6 onto stack
    LDM -(SP), {R3,R5,R7,R9}    ; Push R3, R5, R7, R9 onto stack
    LDM -(SP), {R0,R1,R2,R3}    ; Push R0-R3 onto stack

    ; Load Multiple - Pop multiple registers (only works with SP)
    LDM {R0,R1,R2,R3}, (SP)+    ; Pop R0-R3 from stack
    LDM {R3,R5,R7,R9}, (SP)+    ; Pop R3, R5, R7, R9 from stack
    LDM {R1,R2,R6}, (SP)+       ; Pop R1, R2, R6 from stack

    ; Indirect addressing
    LD R8, (R9)         ; Load from address in R9

    ; Indexed addressing with offset
    LD R10, 0x10(R11)   ; Load from R11 + 0x10
    LD R12, 8(SP)       ; Load from stack frame (SP + 8)
    LD R13, 100(R14)    ; Load from R14 + 100

    ; Label addressing
    LD R15, DATA_LABEL  ; Load from label address

    ; Label with register offset
    LD R1, ARRAY(R2)    ; Load from ARRAY base + R2
    LD R3, BUFFER(R4)   ; Load from BUFFER base + R4

; ============================================================================
; STORE INSTRUCTIONS - All addressing modes
; ============================================================================

    ; Indirect addressing
    ST (R5), R6         ; Store R6 to address in R5

    ; Indexed addressing with offset
    ST 0x20(R7), R8     ; Store R8 to R7 + 0x20
    ST 4(SP), R9        ; Store R9 to stack frame (SP + 4)
    ST 16(R10), R11     ; Store R11 to R10 + 16

    ; Label addressing
    ST DATA_LABEL, R12  ; Store R12 to label address

    ; Label with register offset
    ST ARRAY(R13), R14  ; Store R14 to ARRAY base + R13
    ST BUFFER(R15), R1  ; Store R1 to BUFFER base + R15

; ============================================================================
; ARITHMETIC INSTRUCTIONS - ADD
; ============================================================================

    ; 1 operand (increment)
    ADD R1              ; R1 = R1 + 1 (INC)

    ; 2 operands
    ADD R2, R3          ; R2 = R2 + R3
    ADD R4, 5           ; R4 = R4 + 5
    ADD R5, 0xFF        ; R5 = R5 + 0xFF

    ; 3 operands
    ADD R6, R7, 10      ; R6 = R7 + 10
    ADD R8, R9, 0x100   ; R8 = R9 + 0x100

; ============================================================================
; ARITHMETIC INSTRUCTIONS - ADC (Add with Carry)
; ============================================================================

    ; 2 operands
    ADC R1, R2          ; R1 = R1 + R2 + Carry
    ADC R3, 7           ; R3 = R3 + 7 + Carry

    ; 3 operands
    ADC R4, R5, 12      ; R4 = R5 + 12 + Carry
    ADC R6, R7, 0xFF    ; R6 = R7 + 0xFF + Carry

; ============================================================================
; ARITHMETIC INSTRUCTIONS - SUB (Subtraction)
; ============================================================================

    ; 1 operand (decrement)
    SUB R1              ; R1 = R1 - 1 (DEC)

    ; 2 operands
    SUB R2, R3          ; R2 = R2 - R3
    SUB R4, 5           ; R4 = R4 - 5
    SUB R5, 0x10        ; R5 = R5 - 0x10

    ; 3 operands
    SUB R6, R7, 20      ; R6 = R7 - 20
    SUB R8, R9, 0x200   ; R8 = R9 - 0x200

; ============================================================================
; ARITHMETIC INSTRUCTIONS - SBC (Subtract with Carry/Borrow)
; ============================================================================

    ; 1 operand
    SBC R1              ; R1 = R1 - 1 - Carry

    ; 2 operands
    SBC R2, R3          ; R2 = R2 - R3 - Carry
    SBC R4, 8           ; R4 = R4 - 8 - Carry

    ; 3 operands
    SBC R5, R6, 15      ; R5 = R6 - 15 - Carry
    SBC R7, R8, 0x50    ; R7 = R8 - 0x50 - Carry

; ============================================================================
; ARITHMETIC INSTRUCTIONS - MUL (Multiplication)
; ============================================================================

    ; 2 operands
    MUL R1, R2          ; R1 = R1 * R2 (lower 16 bits)
    MUL R3, 3           ; R3 = R3 * 3
    MUL R4, 0x10        ; R4 = R4 * 0x10

    ; 3 operands
    MUL R5, R6, 5       ; R5 = R6 * 5
    MUL R7, R8, 100     ; R7 = R8 * 100

; ============================================================================
; ARITHMETIC INSTRUCTIONS - MULX (Extended Multiplication, 32-bit result)
; ============================================================================

    ; 2 operands
    MULX R1, R2         ; R1:R2 = R1 * R2 (full 32-bit)

    ; 3 operands
    MULX R3, R4, 12     ; R3:R4 = R4 * 12 (full 32-bit)
    MULX R5, R6, 0xFF   ; R5:R6 = R6 * 0xFF

; ============================================================================
; ARITHMETIC INSTRUCTIONS - DIV (Division, quotient only)
; ============================================================================

    ; 2 operands
    DIV R1, R2          ; R1 = R1 / R2
    DIV R3, 4           ; R3 = R3 / 4
    DIV R4, 0x10        ; R4 = R4 / 0x10

    ; 3 operands
    DIV R5, R6, 8       ; R5 = R6 / 8
    DIV R7, R8, 100     ; R7 = R8 / 100

; ============================================================================
; ARITHMETIC INSTRUCTIONS - DIVX (Extended Division with remainder)
; ============================================================================

    ; 2 operands
    DIVX R1, R2         ; R1 = quotient, R2 = remainder

    ; 3 operands
    DIVX R3, R4, 7      ; R3 = R4 / 7, R4 = R4 % 7
    DIVX R5, R6, 100    ; R5 = R6 / 100, R6 = R6 % 100

; ============================================================================
; LOGICAL INSTRUCTIONS - AND
; ============================================================================

    ; 2 operands
    AND R1, R2          ; R1 = R1 & R2
    AND R3, 0xFF        ; R3 = R3 & 0xFF (mask lower byte)
    AND R4, 0b11110000  ; R4 = R4 & 0b11110000

    ; 3 operands
    AND R5, R6, 0x0F    ; R5 = R6 & 0x0F
    AND R7, R8, 0b00001111 ; R7 = R8 & 0b00001111

; ============================================================================
; LOGICAL INSTRUCTIONS - OR
; ============================================================================

    ; 2 operands
    OR R1, R2           ; R1 = R1 | R2
    OR R3, 0x80         ; R3 = R3 | 0x80 (set bit 7)
    OR R4, 0b10000000   ; R4 = R4 | 0b10000000

    ; 3 operands
    OR R5, R6, 0x01     ; R5 = R6 | 0x01
    OR R7, R8, 0xFF     ; R7 = R8 | 0xFF

; ============================================================================
; LOGICAL INSTRUCTIONS - XOR
; ============================================================================

    ; 2 operands
    XOR R1, R2          ; R1 = R1 ^ R2
    XOR R3, 0xFF        ; R3 = R3 ^ 0xFF (invert all bits)
    XOR R4, 0b11111111  ; R4 = R4 ^ 0b11111111

    ; 3 operands
    XOR R5, R6, 0xAA    ; R5 = R6 ^ 0xAA
    XOR R7, R8, 0x55    ; R7 = R8 ^ 0x55

; ============================================================================
; SHIFT AND ROTATE INSTRUCTIONS - ROL (Rotate Left)
; ============================================================================

    ; 2 operands
    ROL R1, R2          ; R1 = R1 rotated left by R2 positions
    ROL R3, 3           ; R3 = R3 rotated left by 3
    ROL R4, 1           ; R4 = R4 rotated left by 1

    ; 3 operands
    ROL R5, R6, 4       ; R5 = R6 rotated left by 4
    ROL R7, R8, 8       ; R7 = R8 rotated left by 8

; ============================================================================
; SHIFT AND ROTATE INSTRUCTIONS - ROR (Rotate Right)
; ============================================================================

    ; 2 operands
    ROR R1, R2          ; R1 = R1 rotated right by R2 positions
    ROR R3, 2           ; R3 = R3 rotated right by 2
    ROR R4, 1           ; R4 = R4 rotated right by 1

    ; 3 operands
    ROR R5, R6, 5       ; R5 = R6 rotated right by 5
    ROR R7, R8, 4       ; R7 = R8 rotated right by 4

; ============================================================================
; SHIFT AND ROTATE INSTRUCTIONS - LSL (Logical Shift Left)
; ============================================================================

    ; 2 operands
    LSL R1, R2          ; R1 = R1 << R2 (multiply by 2^R2)
    LSL R3, 4           ; R3 = R3 << 4 (multiply by 16)
    LSL R4, 1           ; R4 = R4 << 1 (multiply by 2)

    ; 3 operands
    LSL R5, R6, 3       ; R5 = R6 << 3
    LSL R7, R8, 8       ; R7 = R8 << 8

; ============================================================================
; SHIFT AND ROTATE INSTRUCTIONS - LSR (Logical Shift Right)
; ============================================================================

    ; 2 operands
    LSR R1, R2          ; R1 = R1 >> R2 (unsigned divide by 2^R2)
    LSR R3, 3           ; R3 = R3 >> 3 (unsigned divide by 8)
    LSR R4, 1           ; R4 = R4 >> 1 (unsigned divide by 2)

    ; 3 operands
    LSR R5, R6, 2       ; R5 = R6 >> 2
    LSR R7, R8, 4       ; R7 = R8 >> 4

; ============================================================================
; SHIFT AND ROTATE INSTRUCTIONS - ASR (Arithmetic Shift Right)
; ============================================================================

    ; 2 operands
    ASR R1, R2          ; R1 = R1 >> R2 (signed divide by 2^R2)
    ASR R3, 2           ; R3 = R3 >> 2 (signed divide by 4)
    ASR R4, 1           ; R4 = R4 >> 1 (signed divide by 2)

    ; 3 operands
    ASR R5, R6, 5       ; R5 = R6 >> 5 (preserves sign)
    ASR R7, R8, 3       ; R7 = R8 >> 3 (preserves sign)

; ============================================================================
; SUBROUTINES AND FUNCTIONS
; ============================================================================

SUBROUTINE:
    ADD R1, R2
    BA (SP)+            ; Return from subroutine

FUNCTION:
    MUL R3, 5
    BA (SP)+

ERROR_ROUTINE:
    LD R15, 0xFFFF
    BA (SP)+

OVERFLOW_HANDLER:
    SUB R1
    BA (SP)+

NO_CARRY:
CONTINUE:
CHECK_UPPER:
LOWER_ROUTINE:
NEG_HANDLER:
POS_HANDLER:
OVF_HANDLER:
NOOVF_HANDLER:
HI_ROUTINE:
LS_ROUTINE:
GE_ROUTINE:
LT_ROUTINE:
GT_ROUTINE:
LE_ROUTINE:
PARITY_CHECK:
MAIN:
RETRY:
GREATER_EQUAL:
LESS_THAN:
NEGATIVE:
POSITIVE:
OVERFLOW:
NO_OVERFLOW:
HIGHER:
LOWER_SAME:
SIGNED_GE:
SIGNED_LT:
SIGNED_GT:
SIGNED_LE:
    BA LOOP             ; Loop back

; ============================================================================
; DATA SECTION
; ============================================================================

.DATA

DATA_LABEL:
    .DB 0xFF            ; Single byte

ARRAY:
    .DB 0x01, 0x02, 0x03, 0x04, 0x05
    .DB 0x06, 0x07, 0x08, 0x09, 0x0A

BUFFER:
    .DW 0x1234          ; Word (16-bit)
    .DW 0x5678
    .DW 0xABCD

HELLO:
    .DB 0x0A, 0b1111, 0 ; Hex, binary, and decimal

TEST_DATA:
    .DB 255, 128, 64, 32, 16, 8, 4, 2, 1, 0

LONG_DATA:
    .DL 0xFFFEFFFF

WORLD:
    .ASCII "Hello world!"

.END
