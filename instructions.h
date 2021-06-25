#define MAX_REG 32
#define MAX_MEM 16 * 1024 * 1024 / sizeof(int)

#define sp 29
#define ra 31

#define add 0x20
#define addu 0x21
#define and 0x24
#define jr 0x8
#define nor 0x27
#define or 0x25
#define slt 0x2a
#define sltu 0x2b
#define sll 0x0
#define srl 0x2
#define sub 0x22
#define subu 0x23

#define addi 0x8
#define addiu 0x9
#define andi 0xc
#define beq 0x4
#define bne 0x5
#define j 0x2
#define jal 0x3
#define lui 0xf
#define lw 0x23
#define ori 0xd
#define slti 0xa
#define sltiu 0xb
#define sw 0x2b
