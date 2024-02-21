        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!
loop_starrt:
        # load a0(0x2000 to a0)
         lb x1,0(a0)
        # if the int of char equals 0, end the program 
         beq x1, zero, end_program

        # get the boundry of lowercase
         li x2, 97
         blt x1, x2, next_char

        #get the boundry of uppercase
         li x3, 122
         bgt x1, x3, next_char

        # convet the uppercase
         li x4, 32
         sub x1, x1, x4
         sb x1, 0(a0)

next_char:
        # move a0 to next char
         addi a0, a0, 1
         j loop_starrt
        
end_program:
        # jump here when you're done
        j end_program

