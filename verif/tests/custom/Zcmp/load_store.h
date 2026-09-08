#if __riscv_xlen == 32
# define lx lw
# define sx sw
# define xdata .word
RVTEST_RV32U
#elif __riscv_xlen == 64
# define lx ld
# define sx sd
# define xdata .dword
RVTEST_RV64U
#else
# error "Unsupported __riscv_xlen size"
#endif
#define xlen_bytes    (__riscv_xlen / 8)
#define align_16up(x) (((x) + 15) & ~15)
