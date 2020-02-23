; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=i686-unknown-unknown -verify-machineinstrs | FileCheck %s --check-prefix X86 --check-prefix X86-NOSSE
; RUN: llc < %s -mtriple=i686-unknown-unknown -mattr=sse -verify-machineinstrs | FileCheck %s --check-prefix X86 --check-prefix X86-SSE --check-prefix X86-SSE1
; RUN: llc < %s -mtriple=i686-unknown-unknown -mattr=sse2 -verify-machineinstrs | FileCheck %s --check-prefix X86 --check-prefix X86-SSE --check-prefix X86-SSE2
; RUN: llc < %s -mtriple=i686-unknown-unknown -mattr=avx -verify-machineinstrs | FileCheck %s --check-prefix X86 --check-prefix X86-AVX --check-prefix X86-AVX1
; RUN: llc < %s -mtriple=i686-unknown-unknown -mattr=avx512f -verify-machineinstrs | FileCheck %s --check-prefix X86 --check-prefix X86-AVX --check-prefix X86-AVX512
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -verify-machineinstrs | FileCheck %s --check-prefix X64 --check-prefix X64-SSE
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=avx -verify-machineinstrs | FileCheck %s --check-prefix X64 --check-prefix X64-AVX --check-prefix X64-AVX1
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=avx512f -verify-machineinstrs | FileCheck %s --check-prefix X64 --check-prefix X64-AVX --check-prefix X64-AVX512

; ----- FADD -----

define void @fadd_32r(float* %loc, float %val) nounwind {
; X86-NOSSE-LABEL: fadd_32r:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    subl $8, %esp
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl (%eax), %ecx
; X86-NOSSE-NEXT:    movl %ecx, (%esp)
; X86-NOSSE-NEXT:    flds (%esp)
; X86-NOSSE-NEXT:    fadds {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fstps {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %ecx, (%eax)
; X86-NOSSE-NEXT:    addl $8, %esp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_32r:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    subl $8, %esp
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl (%eax), %ecx
; X86-SSE1-NEXT:    movl %ecx, (%esp)
; X86-SSE1-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE1-NEXT:    addss {{[0-9]+}}(%esp), %xmm0
; X86-SSE1-NEXT:    movss %xmm0, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-SSE1-NEXT:    movl %ecx, (%eax)
; X86-SSE1-NEXT:    addl $8, %esp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_32r:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE2-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE2-NEXT:    addss (%eax), %xmm0
; X86-SSE2-NEXT:    movss %xmm0, (%eax)
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_32r:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-AVX-NEXT:    vaddss (%eax), %xmm0, %xmm0
; X86-AVX-NEXT:    vmovss %xmm0, (%eax)
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_32r:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    addss (%rdi), %xmm0
; X64-SSE-NEXT:    movss %xmm0, (%rdi)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_32r:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    vaddss (%rdi), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovss %xmm0, (%rdi)
; X64-AVX-NEXT:    retq
  %floc = bitcast float* %loc to i32*
  %1 = load atomic i32, i32* %floc seq_cst, align 4
  %2 = bitcast i32 %1 to float
  %add = fadd float %2, %val
  %3 = bitcast float %add to i32
  store atomic i32 %3, i32* %floc release, align 4
  ret void
}

define void @fadd_64r(double* %loc, double %val) nounwind {
; X86-NOSSE-LABEL: fadd_64r:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    pushl %ebp
; X86-NOSSE-NEXT:    movl %esp, %ebp
; X86-NOSSE-NEXT:    andl $-8, %esp
; X86-NOSSE-NEXT:    subl $32, %esp
; X86-NOSSE-NEXT:    movl 8(%ebp), %eax
; X86-NOSSE-NEXT:    fildll (%eax)
; X86-NOSSE-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %edx
; X86-NOSSE-NEXT:    movl %edx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fldl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    faddl 12(%ebp)
; X86-NOSSE-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %edx
; X86-NOSSE-NEXT:    movl %ecx, (%esp)
; X86-NOSSE-NEXT:    movl %edx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fildll (%esp)
; X86-NOSSE-NEXT:    fistpll (%eax)
; X86-NOSSE-NEXT:    movl %ebp, %esp
; X86-NOSSE-NEXT:    popl %ebp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_64r:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    pushl %ebp
; X86-SSE1-NEXT:    movl %esp, %ebp
; X86-SSE1-NEXT:    andl $-8, %esp
; X86-SSE1-NEXT:    subl $24, %esp
; X86-SSE1-NEXT:    movl 8(%ebp), %eax
; X86-SSE1-NEXT:    fildll (%eax)
; X86-SSE1-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %edx
; X86-SSE1-NEXT:    movl %edx, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl %ecx, (%esp)
; X86-SSE1-NEXT:    fldl (%esp)
; X86-SSE1-NEXT:    faddl 12(%ebp)
; X86-SSE1-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    xorps %xmm0, %xmm0
; X86-SSE1-NEXT:    movlps {{.*#+}} xmm0 = mem[0,1],xmm0[2,3]
; X86-SSE1-NEXT:    movlps %xmm0, (%eax)
; X86-SSE1-NEXT:    movl %ebp, %esp
; X86-SSE1-NEXT:    popl %ebp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_64r:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    pushl %ebp
; X86-SSE2-NEXT:    movl %esp, %ebp
; X86-SSE2-NEXT:    andl $-8, %esp
; X86-SSE2-NEXT:    subl $8, %esp
; X86-SSE2-NEXT:    movl 8(%ebp), %eax
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    addsd 12(%ebp), %xmm0
; X86-SSE2-NEXT:    movsd %xmm0, (%esp)
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    movlps %xmm0, (%eax)
; X86-SSE2-NEXT:    movl %ebp, %esp
; X86-SSE2-NEXT:    popl %ebp
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_64r:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    pushl %ebp
; X86-AVX-NEXT:    movl %esp, %ebp
; X86-AVX-NEXT:    andl $-8, %esp
; X86-AVX-NEXT:    subl $8, %esp
; X86-AVX-NEXT:    movl 8(%ebp), %eax
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vaddsd 12(%ebp), %xmm0, %xmm0
; X86-AVX-NEXT:    vmovsd %xmm0, (%esp)
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vmovlps %xmm0, (%eax)
; X86-AVX-NEXT:    movl %ebp, %esp
; X86-AVX-NEXT:    popl %ebp
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_64r:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    addsd (%rdi), %xmm0
; X64-SSE-NEXT:    movsd %xmm0, (%rdi)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_64r:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    vaddsd (%rdi), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovsd %xmm0, (%rdi)
; X64-AVX-NEXT:    retq
  %floc = bitcast double* %loc to i64*
  %1 = load atomic i64, i64* %floc seq_cst, align 8
  %2 = bitcast i64 %1 to double
  %add = fadd double %2, %val
  %3 = bitcast double %add to i64
  store atomic i64 %3, i64* %floc release, align 8
  ret void
}

@glob32 = global float 0.000000e+00, align 4
@glob64 = global double 0.000000e+00, align 8

; Floating-point add to a global using an immediate.
define void @fadd_32g() nounwind {
; X86-NOSSE-LABEL: fadd_32g:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    subl $8, %esp
; X86-NOSSE-NEXT:    movl glob32, %eax
; X86-NOSSE-NEXT:    movl %eax, (%esp)
; X86-NOSSE-NEXT:    fld1
; X86-NOSSE-NEXT:    fadds (%esp)
; X86-NOSSE-NEXT:    fstps {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl %eax, glob32
; X86-NOSSE-NEXT:    addl $8, %esp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_32g:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    subl $8, %esp
; X86-SSE1-NEXT:    movl glob32, %eax
; X86-SSE1-NEXT:    movl %eax, (%esp)
; X86-SSE1-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE1-NEXT:    addss {{\.LCPI.*}}, %xmm0
; X86-SSE1-NEXT:    movss %xmm0, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl %eax, glob32
; X86-SSE1-NEXT:    addl $8, %esp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_32g:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE2-NEXT:    addss glob32, %xmm0
; X86-SSE2-NEXT:    movss %xmm0, glob32
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_32g:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-AVX-NEXT:    vaddss glob32, %xmm0, %xmm0
; X86-AVX-NEXT:    vmovss %xmm0, glob32
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_32g:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X64-SSE-NEXT:    addss {{.*}}(%rip), %xmm0
; X64-SSE-NEXT:    movss %xmm0, {{.*}}(%rip)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_32g:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X64-AVX-NEXT:    vaddss {{.*}}(%rip), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovss %xmm0, {{.*}}(%rip)
; X64-AVX-NEXT:    retq
  %i = load atomic i32, i32* bitcast (float* @glob32 to i32*) monotonic, align 4
  %f = bitcast i32 %i to float
  %add = fadd float %f, 1.000000e+00
  %s = bitcast float %add to i32
  store atomic i32 %s, i32* bitcast (float* @glob32 to i32*) monotonic, align 4
  ret void
}

define void @fadd_64g() nounwind {
; X86-NOSSE-LABEL: fadd_64g:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    pushl %ebp
; X86-NOSSE-NEXT:    movl %esp, %ebp
; X86-NOSSE-NEXT:    andl $-8, %esp
; X86-NOSSE-NEXT:    subl $32, %esp
; X86-NOSSE-NEXT:    fildll glob64
; X86-NOSSE-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl %eax, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fld1
; X86-NOSSE-NEXT:    faddl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %eax, (%esp)
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fildll (%esp)
; X86-NOSSE-NEXT:    fistpll glob64
; X86-NOSSE-NEXT:    movl %ebp, %esp
; X86-NOSSE-NEXT:    popl %ebp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_64g:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    pushl %ebp
; X86-SSE1-NEXT:    movl %esp, %ebp
; X86-SSE1-NEXT:    andl $-8, %esp
; X86-SSE1-NEXT:    subl $24, %esp
; X86-SSE1-NEXT:    fildll glob64
; X86-SSE1-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-SSE1-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl %eax, (%esp)
; X86-SSE1-NEXT:    fld1
; X86-SSE1-NEXT:    faddl (%esp)
; X86-SSE1-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    xorps %xmm0, %xmm0
; X86-SSE1-NEXT:    movlps {{.*#+}} xmm0 = mem[0,1],xmm0[2,3]
; X86-SSE1-NEXT:    movlps %xmm0, glob64
; X86-SSE1-NEXT:    movl %ebp, %esp
; X86-SSE1-NEXT:    popl %ebp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_64g:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    pushl %ebp
; X86-SSE2-NEXT:    movl %esp, %ebp
; X86-SSE2-NEXT:    andl $-8, %esp
; X86-SSE2-NEXT:    subl $8, %esp
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    addsd {{\.LCPI.*}}, %xmm0
; X86-SSE2-NEXT:    movsd %xmm0, (%esp)
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    movlps %xmm0, glob64
; X86-SSE2-NEXT:    movl %ebp, %esp
; X86-SSE2-NEXT:    popl %ebp
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_64g:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    pushl %ebp
; X86-AVX-NEXT:    movl %esp, %ebp
; X86-AVX-NEXT:    andl $-8, %esp
; X86-AVX-NEXT:    subl $8, %esp
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vaddsd {{\.LCPI.*}}, %xmm0, %xmm0
; X86-AVX-NEXT:    vmovsd %xmm0, (%esp)
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vmovlps %xmm0, glob64
; X86-AVX-NEXT:    movl %ebp, %esp
; X86-AVX-NEXT:    popl %ebp
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_64g:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X64-SSE-NEXT:    addsd {{.*}}(%rip), %xmm0
; X64-SSE-NEXT:    movsd %xmm0, {{.*}}(%rip)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_64g:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X64-AVX-NEXT:    vaddsd {{.*}}(%rip), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovsd %xmm0, {{.*}}(%rip)
; X64-AVX-NEXT:    retq
  %i = load atomic i64, i64* bitcast (double* @glob64 to i64*) monotonic, align 8
  %f = bitcast i64 %i to double
  %add = fadd double %f, 1.000000e+00
  %s = bitcast double %add to i64
  store atomic i64 %s, i64* bitcast (double* @glob64 to i64*) monotonic, align 8
  ret void
}

; Floating-point add to a hard-coded immediate location using an immediate.
define void @fadd_32imm() nounwind {
; X86-NOSSE-LABEL: fadd_32imm:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    subl $8, %esp
; X86-NOSSE-NEXT:    movl -559038737, %eax
; X86-NOSSE-NEXT:    movl %eax, (%esp)
; X86-NOSSE-NEXT:    fld1
; X86-NOSSE-NEXT:    fadds (%esp)
; X86-NOSSE-NEXT:    fstps {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl %eax, -559038737
; X86-NOSSE-NEXT:    addl $8, %esp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_32imm:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    subl $8, %esp
; X86-SSE1-NEXT:    movl -559038737, %eax
; X86-SSE1-NEXT:    movl %eax, (%esp)
; X86-SSE1-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE1-NEXT:    addss {{\.LCPI.*}}, %xmm0
; X86-SSE1-NEXT:    movss %xmm0, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl %eax, -559038737
; X86-SSE1-NEXT:    addl $8, %esp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_32imm:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE2-NEXT:    addss -559038737, %xmm0
; X86-SSE2-NEXT:    movss %xmm0, -559038737
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_32imm:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-AVX-NEXT:    vaddss -559038737, %xmm0, %xmm0
; X86-AVX-NEXT:    vmovss %xmm0, -559038737
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_32imm:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    movl $3735928559, %eax # imm = 0xDEADBEEF
; X64-SSE-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X64-SSE-NEXT:    addss (%rax), %xmm0
; X64-SSE-NEXT:    movss %xmm0, (%rax)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_32imm:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    movl $3735928559, %eax # imm = 0xDEADBEEF
; X64-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X64-AVX-NEXT:    vaddss (%rax), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovss %xmm0, (%rax)
; X64-AVX-NEXT:    retq
  %i = load atomic i32, i32* inttoptr (i32 3735928559 to i32*) monotonic, align 4
  %f = bitcast i32 %i to float
  %add = fadd float %f, 1.000000e+00
  %s = bitcast float %add to i32
  store atomic i32 %s, i32* inttoptr (i32 3735928559 to i32*) monotonic, align 4
  ret void
}

define void @fadd_64imm() nounwind {
; X86-NOSSE-LABEL: fadd_64imm:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    pushl %ebp
; X86-NOSSE-NEXT:    movl %esp, %ebp
; X86-NOSSE-NEXT:    andl $-8, %esp
; X86-NOSSE-NEXT:    subl $32, %esp
; X86-NOSSE-NEXT:    fildll -559038737
; X86-NOSSE-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl %eax, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fld1
; X86-NOSSE-NEXT:    faddl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %eax, (%esp)
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fildll (%esp)
; X86-NOSSE-NEXT:    fistpll -559038737
; X86-NOSSE-NEXT:    movl %ebp, %esp
; X86-NOSSE-NEXT:    popl %ebp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_64imm:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    pushl %ebp
; X86-SSE1-NEXT:    movl %esp, %ebp
; X86-SSE1-NEXT:    andl $-8, %esp
; X86-SSE1-NEXT:    subl $24, %esp
; X86-SSE1-NEXT:    fildll -559038737
; X86-SSE1-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-SSE1-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl %eax, (%esp)
; X86-SSE1-NEXT:    fld1
; X86-SSE1-NEXT:    faddl (%esp)
; X86-SSE1-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    xorps %xmm0, %xmm0
; X86-SSE1-NEXT:    movlps {{.*#+}} xmm0 = mem[0,1],xmm0[2,3]
; X86-SSE1-NEXT:    movlps %xmm0, -559038737
; X86-SSE1-NEXT:    movl %ebp, %esp
; X86-SSE1-NEXT:    popl %ebp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_64imm:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    pushl %ebp
; X86-SSE2-NEXT:    movl %esp, %ebp
; X86-SSE2-NEXT:    andl $-8, %esp
; X86-SSE2-NEXT:    subl $8, %esp
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    addsd {{\.LCPI.*}}, %xmm0
; X86-SSE2-NEXT:    movsd %xmm0, (%esp)
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    movlps %xmm0, -559038737
; X86-SSE2-NEXT:    movl %ebp, %esp
; X86-SSE2-NEXT:    popl %ebp
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_64imm:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    pushl %ebp
; X86-AVX-NEXT:    movl %esp, %ebp
; X86-AVX-NEXT:    andl $-8, %esp
; X86-AVX-NEXT:    subl $8, %esp
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vaddsd {{\.LCPI.*}}, %xmm0, %xmm0
; X86-AVX-NEXT:    vmovsd %xmm0, (%esp)
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vmovlps %xmm0, -559038737
; X86-AVX-NEXT:    movl %ebp, %esp
; X86-AVX-NEXT:    popl %ebp
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_64imm:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    movl $3735928559, %eax # imm = 0xDEADBEEF
; X64-SSE-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X64-SSE-NEXT:    addsd (%rax), %xmm0
; X64-SSE-NEXT:    movsd %xmm0, (%rax)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_64imm:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    movl $3735928559, %eax # imm = 0xDEADBEEF
; X64-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X64-AVX-NEXT:    vaddsd (%rax), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovsd %xmm0, (%rax)
; X64-AVX-NEXT:    retq
  %i = load atomic i64, i64* inttoptr (i64 3735928559 to i64*) monotonic, align 8
  %f = bitcast i64 %i to double
  %add = fadd double %f, 1.000000e+00
  %s = bitcast double %add to i64
  store atomic i64 %s, i64* inttoptr (i64 3735928559 to i64*) monotonic, align 8
  ret void
}

; Floating-point add to a stack location.
define void @fadd_32stack() nounwind {
; X86-NOSSE-LABEL: fadd_32stack:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    subl $12, %esp
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl %eax, (%esp)
; X86-NOSSE-NEXT:    fld1
; X86-NOSSE-NEXT:    fadds (%esp)
; X86-NOSSE-NEXT:    fstps {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl %eax, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    addl $12, %esp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_32stack:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    subl $12, %esp
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl %eax, (%esp)
; X86-SSE1-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE1-NEXT:    addss {{\.LCPI.*}}, %xmm0
; X86-SSE1-NEXT:    movss %xmm0, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl %eax, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    addl $12, %esp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_32stack:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    pushl %eax
; X86-SSE2-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-SSE2-NEXT:    addss (%esp), %xmm0
; X86-SSE2-NEXT:    movss %xmm0, (%esp)
; X86-SSE2-NEXT:    popl %eax
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_32stack:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    pushl %eax
; X86-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X86-AVX-NEXT:    vaddss (%esp), %xmm0, %xmm0
; X86-AVX-NEXT:    vmovss %xmm0, (%esp)
; X86-AVX-NEXT:    popl %eax
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_32stack:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    movss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X64-SSE-NEXT:    addss -{{[0-9]+}}(%rsp), %xmm0
; X64-SSE-NEXT:    movss %xmm0, -{{[0-9]+}}(%rsp)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_32stack:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    vmovss {{.*#+}} xmm0 = mem[0],zero,zero,zero
; X64-AVX-NEXT:    vaddss -{{[0-9]+}}(%rsp), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovss %xmm0, -{{[0-9]+}}(%rsp)
; X64-AVX-NEXT:    retq
  %ptr = alloca i32, align 4
  %bc3 = bitcast i32* %ptr to float*
  %load = load atomic i32, i32* %ptr acquire, align 4
  %bc0 = bitcast i32 %load to float
  %fadd = fadd float 1.000000e+00, %bc0
  %bc1 = bitcast float %fadd to i32
  store atomic i32 %bc1, i32* %ptr release, align 4
  ret void
}

define void @fadd_64stack() nounwind {
; X86-NOSSE-LABEL: fadd_64stack:
; X86-NOSSE:       # %bb.0:
; X86-NOSSE-NEXT:    pushl %ebp
; X86-NOSSE-NEXT:    movl %esp, %ebp
; X86-NOSSE-NEXT:    andl $-8, %esp
; X86-NOSSE-NEXT:    subl $40, %esp
; X86-NOSSE-NEXT:    fildll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl %eax, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fld1
; X86-NOSSE-NEXT:    faddl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-NOSSE-NEXT:    movl %eax, (%esp)
; X86-NOSSE-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fildll (%esp)
; X86-NOSSE-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl %ebp, %esp
; X86-NOSSE-NEXT:    popl %ebp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_64stack:
; X86-SSE1:       # %bb.0:
; X86-SSE1-NEXT:    pushl %ebp
; X86-SSE1-NEXT:    movl %esp, %ebp
; X86-SSE1-NEXT:    andl $-8, %esp
; X86-SSE1-NEXT:    subl $32, %esp
; X86-SSE1-NEXT:    fildll {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %eax
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %ecx
; X86-SSE1-NEXT:    movl %ecx, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl %eax, (%esp)
; X86-SSE1-NEXT:    fld1
; X86-SSE1-NEXT:    faddl (%esp)
; X86-SSE1-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    xorps %xmm0, %xmm0
; X86-SSE1-NEXT:    movlps {{.*#+}} xmm0 = mem[0,1],xmm0[2,3]
; X86-SSE1-NEXT:    movlps %xmm0, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl %ebp, %esp
; X86-SSE1-NEXT:    popl %ebp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_64stack:
; X86-SSE2:       # %bb.0:
; X86-SSE2-NEXT:    pushl %ebp
; X86-SSE2-NEXT:    movl %esp, %ebp
; X86-SSE2-NEXT:    andl $-8, %esp
; X86-SSE2-NEXT:    subl $16, %esp
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    addsd {{\.LCPI.*}}, %xmm0
; X86-SSE2-NEXT:    movsd %xmm0, (%esp)
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    movlps %xmm0, {{[0-9]+}}(%esp)
; X86-SSE2-NEXT:    movl %ebp, %esp
; X86-SSE2-NEXT:    popl %ebp
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_64stack:
; X86-AVX:       # %bb.0:
; X86-AVX-NEXT:    pushl %ebp
; X86-AVX-NEXT:    movl %esp, %ebp
; X86-AVX-NEXT:    andl $-8, %esp
; X86-AVX-NEXT:    subl $16, %esp
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vaddsd {{\.LCPI.*}}, %xmm0, %xmm0
; X86-AVX-NEXT:    vmovsd %xmm0, (%esp)
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vmovlps %xmm0, {{[0-9]+}}(%esp)
; X86-AVX-NEXT:    movl %ebp, %esp
; X86-AVX-NEXT:    popl %ebp
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_64stack:
; X64-SSE:       # %bb.0:
; X64-SSE-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X64-SSE-NEXT:    addsd -{{[0-9]+}}(%rsp), %xmm0
; X64-SSE-NEXT:    movsd %xmm0, -{{[0-9]+}}(%rsp)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_64stack:
; X64-AVX:       # %bb.0:
; X64-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X64-AVX-NEXT:    vaddsd -{{[0-9]+}}(%rsp), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovsd %xmm0, -{{[0-9]+}}(%rsp)
; X64-AVX-NEXT:    retq
  %ptr = alloca i64, align 8
  %bc3 = bitcast i64* %ptr to double*
  %load = load atomic i64, i64* %ptr acquire, align 8
  %bc0 = bitcast i64 %load to double
  %fadd = fadd double 1.000000e+00, %bc0
  %bc1 = bitcast double %fadd to i64
  store atomic i64 %bc1, i64* %ptr release, align 8
  ret void
}

define void @fadd_array(i64* %arg, double %arg1, i64 %arg2) nounwind {
; X86-NOSSE-LABEL: fadd_array:
; X86-NOSSE:       # %bb.0: # %bb
; X86-NOSSE-NEXT:    pushl %ebp
; X86-NOSSE-NEXT:    movl %esp, %ebp
; X86-NOSSE-NEXT:    pushl %esi
; X86-NOSSE-NEXT:    andl $-8, %esp
; X86-NOSSE-NEXT:    subl $40, %esp
; X86-NOSSE-NEXT:    movl 20(%ebp), %eax
; X86-NOSSE-NEXT:    movl 8(%ebp), %ecx
; X86-NOSSE-NEXT:    fildll (%ecx,%eax,8)
; X86-NOSSE-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %edx
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NOSSE-NEXT:    movl %esi, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl %edx, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fldl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    faddl 12(%ebp)
; X86-NOSSE-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %edx
; X86-NOSSE-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-NOSSE-NEXT:    movl %edx, (%esp)
; X86-NOSSE-NEXT:    movl %esi, {{[0-9]+}}(%esp)
; X86-NOSSE-NEXT:    fildll (%esp)
; X86-NOSSE-NEXT:    fistpll (%ecx,%eax,8)
; X86-NOSSE-NEXT:    leal -4(%ebp), %esp
; X86-NOSSE-NEXT:    popl %esi
; X86-NOSSE-NEXT:    popl %ebp
; X86-NOSSE-NEXT:    retl
;
; X86-SSE1-LABEL: fadd_array:
; X86-SSE1:       # %bb.0: # %bb
; X86-SSE1-NEXT:    pushl %ebp
; X86-SSE1-NEXT:    movl %esp, %ebp
; X86-SSE1-NEXT:    pushl %esi
; X86-SSE1-NEXT:    andl $-8, %esp
; X86-SSE1-NEXT:    subl $32, %esp
; X86-SSE1-NEXT:    movl 20(%ebp), %eax
; X86-SSE1-NEXT:    movl 8(%ebp), %ecx
; X86-SSE1-NEXT:    fildll (%ecx,%eax,8)
; X86-SSE1-NEXT:    fistpll {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %edx
; X86-SSE1-NEXT:    movl {{[0-9]+}}(%esp), %esi
; X86-SSE1-NEXT:    movl %esi, {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    movl %edx, (%esp)
; X86-SSE1-NEXT:    fldl (%esp)
; X86-SSE1-NEXT:    faddl 12(%ebp)
; X86-SSE1-NEXT:    fstpl {{[0-9]+}}(%esp)
; X86-SSE1-NEXT:    xorps %xmm0, %xmm0
; X86-SSE1-NEXT:    movlps {{.*#+}} xmm0 = mem[0,1],xmm0[2,3]
; X86-SSE1-NEXT:    movlps %xmm0, (%ecx,%eax,8)
; X86-SSE1-NEXT:    leal -4(%ebp), %esp
; X86-SSE1-NEXT:    popl %esi
; X86-SSE1-NEXT:    popl %ebp
; X86-SSE1-NEXT:    retl
;
; X86-SSE2-LABEL: fadd_array:
; X86-SSE2:       # %bb.0: # %bb
; X86-SSE2-NEXT:    pushl %ebp
; X86-SSE2-NEXT:    movl %esp, %ebp
; X86-SSE2-NEXT:    andl $-8, %esp
; X86-SSE2-NEXT:    subl $8, %esp
; X86-SSE2-NEXT:    movl 20(%ebp), %eax
; X86-SSE2-NEXT:    movl 8(%ebp), %ecx
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    addsd 12(%ebp), %xmm0
; X86-SSE2-NEXT:    movsd %xmm0, (%esp)
; X86-SSE2-NEXT:    movsd {{.*#+}} xmm0 = mem[0],zero
; X86-SSE2-NEXT:    movlps %xmm0, (%ecx,%eax,8)
; X86-SSE2-NEXT:    movl %ebp, %esp
; X86-SSE2-NEXT:    popl %ebp
; X86-SSE2-NEXT:    retl
;
; X86-AVX-LABEL: fadd_array:
; X86-AVX:       # %bb.0: # %bb
; X86-AVX-NEXT:    pushl %ebp
; X86-AVX-NEXT:    movl %esp, %ebp
; X86-AVX-NEXT:    andl $-8, %esp
; X86-AVX-NEXT:    subl $8, %esp
; X86-AVX-NEXT:    movl 20(%ebp), %eax
; X86-AVX-NEXT:    movl 8(%ebp), %ecx
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vaddsd 12(%ebp), %xmm0, %xmm0
; X86-AVX-NEXT:    vmovsd %xmm0, (%esp)
; X86-AVX-NEXT:    vmovsd {{.*#+}} xmm0 = mem[0],zero
; X86-AVX-NEXT:    vmovlps %xmm0, (%ecx,%eax,8)
; X86-AVX-NEXT:    movl %ebp, %esp
; X86-AVX-NEXT:    popl %ebp
; X86-AVX-NEXT:    retl
;
; X64-SSE-LABEL: fadd_array:
; X64-SSE:       # %bb.0: # %bb
; X64-SSE-NEXT:    addsd (%rdi,%rsi,8), %xmm0
; X64-SSE-NEXT:    movsd %xmm0, (%rdi,%rsi,8)
; X64-SSE-NEXT:    retq
;
; X64-AVX-LABEL: fadd_array:
; X64-AVX:       # %bb.0: # %bb
; X64-AVX-NEXT:    vaddsd (%rdi,%rsi,8), %xmm0, %xmm0
; X64-AVX-NEXT:    vmovsd %xmm0, (%rdi,%rsi,8)
; X64-AVX-NEXT:    retq
bb:
  %tmp4 = getelementptr inbounds i64, i64* %arg, i64 %arg2
  %tmp6 = load atomic i64, i64* %tmp4 monotonic, align 8
  %tmp7 = bitcast i64 %tmp6 to double
  %tmp8 = fadd double %tmp7, %arg1
  %tmp9 = bitcast double %tmp8 to i64
  store atomic i64 %tmp9, i64* %tmp4 monotonic, align 8
  ret void
}
