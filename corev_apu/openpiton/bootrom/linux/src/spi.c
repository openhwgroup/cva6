#include "spi.h"

#include "uart.h"

void write_reg(uintptr_t addr, uint32_t value)
{
    volatile uint32_t *loc_addr = (volatile uint32_t *)addr;
    *loc_addr = value;
}

uint32_t read_reg(uintptr_t addr)
{
    return *(volatile uint32_t *)addr;
}

void spi_init()
{
    print_uart("init SPI\r\n");

    // reset the axi quadspi core
    write_reg(SPI_RESET_REG, 0x0a);

    for (int i = 0; i < 10; i++)
    {
        __asm__ volatile(
            "nop");
    }

    write_reg(SPI_CONTROL_REG, 0x104);

    uint32_t status = read_reg(SPI_STATUS_REG);
    print_uart("status: 0x");
    print_uart_addr(status);
    print_uart("\r\n");

    // clear all fifos
    write_reg(SPI_CONTROL_REG, 0x166);

    status = read_reg(SPI_STATUS_REG);
    print_uart("status: 0x");
    print_uart_addr(status);
    print_uart("\r\n");

    write_reg(SPI_CONTROL_REG, 0x06);

    print_uart("SPI initialized!\r\n");
}

uint8_t spi_txrx(uint8_t byte)
{
    // enable slave select
    write_reg(SPI_SLAVE_SELECT_REG, 0xfffffffe);

    write_reg(SPI_TRANSMIT_REG, byte);

    for (int i = 0; i < 100; i++)
    {
        __asm__ volatile(
            "nop");
    }

    // enable spi control master flag
    write_reg(SPI_CONTROL_REG, 0x106);

    while ((read_reg(SPI_STATUS_REG) & 0x1) == 0x1)
        ;

    uint32_t result = read_reg(SPI_RECEIVE_REG);

    if ((read_reg(SPI_STATUS_REG) & 0x1) != 0x1)
    {
        print_uart("rx fifo not empty?? ");
        print_uart_addr(read_reg(SPI_STATUS_REG));
        print_uart("\r\n");
    }

    // disable slave select
    write_reg(SPI_SLAVE_SELECT_REG, 0xffffffff);

    // disable spi control master flag
    write_reg(SPI_CONTROL_REG, 0x06);

    return result;
}

int spi_write_bytes(uint8_t *bytes, uint32_t len, uint8_t *ret)
{
    uint32_t status;

    if (len > 256) // FIFO maxdepth 256
        return -1;

    // enable slave select
    write_reg(SPI_SLAVE_SELECT_REG, 0xfffffffe);

    for (int i = 0; i < len; i++)
    {
        write_reg(SPI_TRANSMIT_REG, bytes[i] & 0xff);
    }

    for (int i = 0; i < 50; i++)
    {
        __asm__ volatile(
            "nop");
    }

    // enable spi control master flag
    write_reg(SPI_CONTROL_REG, 0x106);

    do
    {
        status = read_reg(SPI_STATUS_REG);
    } while ((status & 0x1) == 0x1);

    for (int i = 0; i < len;)
    {
        status = read_reg(SPI_STATUS_REG);
        if ((status & 0x1) != 0x1) // recieve fifo not empty
        {
            ret[i++] = read_reg(SPI_RECEIVE_REG);
        }
    }

    // disable slave select
    write_reg(SPI_SLAVE_SELECT_REG, 0xffffffff);

    // disable spi control master flag
    write_reg(SPI_CONTROL_REG, 0x06);

    return 0;
}