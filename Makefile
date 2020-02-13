all: test npietest instr;
test: test.c
	$(CC) -O2 -fPIE test.c -o test
npietest: test.c
	$(CC) -O2 -no-pie test.c -o nopietest
instr: instr.c saver.o
	gcc -O0 -g -Wall -Wextra instr.c saver.o -lcapstone -lkeystone -o instr
saver.o: saver.s
	nasm -felf64 saver.s 
	objcopy -O binary --only-section=.text saver.o saver.bin
	ld -r -b binary saver.bin -o saver.o
