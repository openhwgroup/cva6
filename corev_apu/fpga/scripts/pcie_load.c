/*
 * pcie_load — Load a binary file into FPGA DRAM via PCIe BAR0 (mmap).
 *
 * Usage: sudo ./pcie_load <resource0_path> <bar_offset> <file>
 *
 * <bar_offset> is the offset within the BAR, NOT the final AXI address.
 * The XDMA IP's pciebar2axibar_0 register adds a fixed base to produce
 * the AXI address:  AXI_addr = pciebar2axibar_0 + bar_offset.
 *
 * If pciebar2axibar_0 = 0x80000000 (DRAM base), use bar_offset = 0x0:
 *   sudo ./pcie_load /sys/bus/pci/devices/0000:02:00.0/resource0 0x0 boot.bin
 *
 * The BAR0 sysfs resource file is accessed via mmap (not read/write/seek).
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <errno.h>

int main(int argc, char *argv[])
{
    if (argc != 4) {
        fprintf(stderr, "Usage: %s <resource0> <bar_offset_hex> <payload_file>\n", argv[0]);
        fprintf(stderr, "  e.g. %s /sys/bus/pci/devices/0000:02:00.0/resource0 0x0 boot.bin\n", argv[0]);
        return 1;
    }

    const char *bar_path = argv[1];
    unsigned long bar_offset = strtoul(argv[2], NULL, 0);
    const char *payload_path = argv[3];

    /* Open payload file */
    int payload_fd = open(payload_path, O_RDONLY);
    if (payload_fd < 0) {
        perror("open payload");
        return 1;
    }

    struct stat st;
    if (fstat(payload_fd, &st) < 0) {
        perror("fstat payload");
        close(payload_fd);
        return 1;
    }
    size_t payload_size = st.st_size;

    /* Read payload into memory */
    uint8_t *payload = malloc(payload_size);
    if (!payload) {
        perror("malloc");
        close(payload_fd);
        return 1;
    }
    size_t total_read = 0;
    while (total_read < payload_size) {
        ssize_t n = read(payload_fd, payload + total_read, payload_size - total_read);
        if (n <= 0) {
            perror("read payload");
            free(payload);
            close(payload_fd);
            return 1;
        }
        total_read += n;
    }
    close(payload_fd);

    /* Open BAR0 resource. We mmap the file below; open flags don't carry
     * MMIO-ordering semantics on sysfs resource nodes, so plain O_RDWR is
     * sufficient. */
    int bar_fd = open(bar_path, O_RDWR);
    if (bar_fd < 0) {
        perror("open BAR0 resource");
        free(payload);
        return 1;
    }

    /* Get BAR size from file size */
    struct stat bar_st;
    if (fstat(bar_fd, &bar_st) < 0) {
        perror("fstat BAR0");
        close(bar_fd);
        free(payload);
        return 1;
    }
    size_t bar_size = bar_st.st_size;

    if (bar_offset + payload_size > bar_size) {
        fprintf(stderr, "Error: offset (0x%lx) + payload (%zu) exceeds BAR size (0x%zx)\n",
                bar_offset, payload_size, bar_size);
        close(bar_fd);
        free(payload);
        return 1;
    }

    /* mmap the entire BAR (or the needed portion).
     * We map from the start of the BAR to cover the offset. */
    size_t map_size = bar_offset + payload_size;
    /* Round up to page size */
    long page_size = sysconf(_SC_PAGESIZE);
    map_size = (map_size + page_size - 1) & ~(page_size - 1);

    void *bar_map = mmap(NULL, map_size, PROT_READ | PROT_WRITE, MAP_SHARED, bar_fd, 0);
    if (bar_map == MAP_FAILED) {
        perror("mmap BAR0");
        close(bar_fd);
        free(payload);
        return 1;
    }

    printf("BAR0 mapped at %p, size 0x%zx\n", bar_map, map_size);
    printf("Writing %zu bytes to BAR offset 0x%lx ...\n", payload_size, bar_offset);

    /* Stream the payload to DRAM via 64-bit MMIO writes. We deliberately
     * write dst[0] LAST, with __sync_synchronize() barriers around it.
     *
     * The bootrom (corev_apu/fpga/src/bootrom/src/main.c) polls the
     * first 8 bytes of DRAM for the XDMA_READY_MAGIC sentinel and jumps
     * to OpenSBI as soon as those 8 bytes change. So dst[0] is effectively
     * a release-store: when it changes, dst[1..N] must already be visible
     * on the FPGA side. The volatile dst pointer + the surrounding memory
     * barriers give us that ordering at the CPU level. PCIe's
     * posted-write ordering rules then carry it through to DDR4.
     *
     * If we wrote dst[0] in sequence with the rest of the payload, the
     * bootrom could observe the sentinel-replacement before later qwords
     * have landed in DRAM, and execute partially-loaded firmware. */
    volatile uint64_t *dst = (volatile uint64_t *)((uint8_t *)bar_map + bar_offset);
    const uint64_t *src = (const uint64_t *)payload;
    size_t qwords = payload_size / 8;
    size_t remainder = payload_size % 8;

    /* 1. Bulk: write qwords 1..N-1 in order */
    for (size_t i = 1; i < qwords; i++) {
        dst[i] = src[i];
    }

    /* 2. Trailing bytes (zero-padded into one extra qword) */
    if (remainder) {
        uint64_t last = 0;
        memcpy(&last, payload + qwords * 8, remainder);
        dst[qwords] = last;
    }

    /* 3. Release-store the first qword last (the sentinel-replacement). */
    __sync_synchronize();
    dst[0] = src[0];
    __sync_synchronize();

    /* Read back first 8 bytes as round-trip verification.
     * If this returns 0xFFFFFFFFFFFFFFFF, the PCIe link or BAR is broken.
     * If it returns a value different from what was written, the AXI
     * target may not be responding (DDR4 not calibrated, wrong address). */
    uint64_t readback = dst[0];
    uint64_t expected = src[0];
    printf("Done. Read back at BAR+0x%lx: 0x%016lx (expected 0x%016lx)\n",
           bar_offset, readback, expected);
    if (readback == UINT64_C(0xFFFFFFFFFFFFFFFF)) {
        fprintf(stderr, "WARNING: readback is all-ones — PCIe endpoint not responding!\n");
    } else if (readback != expected) {
        fprintf(stderr, "WARNING: readback mismatch — data may not have reached DRAM.\n");
        fprintf(stderr, "  Check that DDR4 calibration is complete and address translation is correct.\n");
    }

    munmap(bar_map, map_size);
    close(bar_fd);
    free(payload);
    return 0;
}
