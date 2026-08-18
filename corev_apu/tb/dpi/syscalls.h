#include <cstdint>
#include <cstdio>

extern "C" void emulate_syscall (long long tohost, long long fromhost);

class SyscallHandler {
    static uintptr_t _mem;

public:
    static void init(void* mem);
    static void emulate_syscall(long long tohost, long long fromhost);
};
