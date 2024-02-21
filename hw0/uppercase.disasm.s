
uppercase.bin:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <_start>:
   10074:	ffff2517          	auipc	a0,0xffff2
   10078:	f8c50513          	addi	a0,a0,-116 # 2000 <__DATA_BEGIN__>

0001007c <loop_starrt>:
   1007c:	00050083          	lb	ra,0(a0)
   10080:	02008463          	beqz	ra,100a8 <end_program>
   10084:	06100113          	li	sp,97
   10088:	0020cc63          	blt	ra,sp,100a0 <next_char>
   1008c:	07a00193          	li	gp,122
   10090:	0011c863          	blt	gp,ra,100a0 <next_char>
   10094:	02000213          	li	tp,32
   10098:	404080b3          	sub	ra,ra,tp
   1009c:	00150023          	sb	ra,0(a0)

000100a0 <next_char>:
   100a0:	00150513          	addi	a0,a0,1
   100a4:	fd9ff06f          	j	1007c <loop_starrt>

000100a8 <end_program>:
   100a8:	0000006f          	j	100a8 <end_program>
