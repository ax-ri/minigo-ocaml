	.text
	.globl	main
main:
	xorq %rax, %rax
	ret

# TODO some auxiliary assembly functions, if needed
malloc_:
	pushq   %rbp
	movq    %rsp, %rbp
	andq    $-16, %rsp  # 16-byte stack alignment
	call    malloc
	movq    %rbp, %rsp
	popq    %rbp
	ret
calloc_:
	pushq   %rbp
	movq    %rsp, %rbp
	andq    $-16, %rsp  # 16-byte stack alignment
	call    calloc
	movq    %rbp, %rsp
	popq    %rbp
	ret
printf_:
	pushq   %rbp
	movq    %rsp, %rbp
	andq    $-16, %rsp  # 16-byte stack alignment
	call    printf
	movq    %rbp, %rsp
	popq    %rbp
	ret
	.data
