
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unistd.h>

#include "syscalls.h"

uintptr_t SyscallHandler::_mem;

constexpr uint64_t MEM_OFFSET=0x80000000;
constexpr uint64_t WORDLEN_BYTE=8;

void emulate_syscall (long long tohost, long long fromhost) {
    SyscallHandler::emulate_syscall(tohost, fromhost);
}

void SyscallHandler::init(void* mem) {
    _mem = (uintptr_t) mem - MEM_OFFSET;
}

void SyscallHandler::emulate_syscall(
        long long tohost, long long fromhost) {
    long long which, arg0, arg1, arg2;
    which = *(long long*) (_mem + tohost);
    arg0 = *(long long*) (_mem + tohost + WORDLEN_BYTE);
    arg1 = *(long long*) (_mem + tohost + 2*WORDLEN_BYTE);
    arg2 = *(long long*) (_mem + tohost + 3*WORDLEN_BYTE);
    switch (which) {
        case 64: {
            long ret = write((int) arg0, (void*)(_mem + arg1), (size_t) arg2);
            *((long*) (_mem + tohost)) = ret;
            break;
        }
        default: {
            fprintf(stderr, "[ERROR]: Unknown syscall %lld\n", which);
            break;
        }
    }
    *((uint64_t*) (_mem + fromhost)) = 1;
}
