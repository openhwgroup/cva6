# First Stage Bootloader for Ariane

## How-To prepare SD card
The bootloader requires a GPT partition table so you first have to create one with gdisk.

```bash
$ sudo fdisk -l # search for the corresponding disk label (e.g. /dev/sdb)
$ sudo sgdisk --clear --new=1:2048:67583 --new=2 --typecode=1:3000 --typecode=2:8300 /dev/sdb # create a new gpt partition table and two partitions: 1st partition: 32mb (ONIE boot), second partition: rest (Linux root)
```

Now you have to make the linux kernel with the [ariane-sdk](https://github.com/pulp-platform/ariane-sdk):
```bash
$ cd /path/to/ariane-sdk
$ make bbl.bin # make the linux kernel with the ariane-sdk repository
```

Then the bbl+linux kernel image can get copied to the sd card with `dd`. __Careful:__  use the same disk label that you found before with `fdisk -l` but with a 1 in the end, e.g. `/dev/sdb` -> `/dev/sdb1`.
```bash
$ sudo dd if=bbl.bin of=/dev/sdb1 status=progress oflag=sync bs=1M
```

## Features

- uart
- spi
- sd card reading
- GPT partitions

## TODO

- file systems (fat16/fat32)
- elf loader
- zeroing of the `.bss` section of the second stage boot loader
