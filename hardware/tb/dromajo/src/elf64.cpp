/*
 * Elf64 utilities
 *
 * Copyright (C) 2018,2019, Esperanto Technologies Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "elf64.h"
#include <string.h>

bool elf64_is_riscv64(const uint8_t *image, size_t image_size)
{
    const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)image;

    if (image_size < sizeof *ehdr)
        return false;

    if (strncmp((char *)ehdr->e_ident, ELFMAG, SELFMAG) != 0)
        // header read, file corrupted?
        return false;

    if (ehdr->e_ident[EI_CLASS] != ELFCLASS64)
        // Only support 64-bit
        return false;

    if (ehdr->e_ident[EI_DATA] != ELFDATA2LSB)
        // Unsupported endian (big)
        return false;

    if (ehdr->e_machine != EM_RISCV)
        // Only handle RISC-V
        return false;

    /* We have an RV64 ELF file */

    if (ehdr->e_ehsize != sizeof *ehdr)
        // Unexpected e_ehsize field value
        return false;

    if (ehdr->e_phentsize != sizeof(Elf64_Phdr))
        // Unexpected e_phentsize field value
        return false;

    return true;
}

uint64_t elf64_get_entrypoint(const uint8_t *image)
{
    const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)image;

    return ehdr->e_entry;
}

bool elf64_find_global(const uint8_t *image, size_t image_size,
                       const char *key, uint64_t *value)
{
    const uint8_t *image_end   = image + image_size;
    Elf64_Ehdr *ehdr        = (Elf64_Ehdr *)image;

    if (ehdr->e_shoff + sizeof(Elf64_Shdr) - 1 > image_size)
        return false;

    Elf64_Shdr *shdr        = (Elf64_Shdr *)&image[ehdr->e_shoff];

    if ((const uint8_t *)&shdr[ehdr->e_shstrndx + 1] > image_end)
        return false;

    const Elf64_Sym  *symtab      = 0;
    int               symtab_len  = 0;
    const char       *strtab      = 0;

    if ((const uint8_t *)&shdr[ehdr->e_shnum] > image_end)
        return false;

    /* Look for symbol table */
    for (int i = 0; i < ehdr->e_shnum; ++i) {
        Elf64_Shdr *sh = &shdr[i];

        if (sh->sh_type == SHT_STRTAB && i != ehdr->e_shstrndx)
            strtab = (const char *)(image + sh->sh_offset);

        if (sh->sh_type == SHT_SYMTAB) {
            symtab = (Elf64_Sym *)&image[sh->sh_offset];
            symtab_len = sh->sh_size / sizeof(Elf64_Sym);
        }
    }

    if (symtab && strtab) {
        if ((const uint8_t *)&symtab[symtab_len] > image_end)
            return false;

        for (int i = 0; i < symtab_len; ++i) {
            const Elf64_Sym *sym = &symtab[i];

            if (strcmp(key, strtab + sym->st_name) == 0 &&
                ELF32_ST_BIND(sym->st_info) == STB_GLOBAL) {
                *value = sym->st_value;
                return true;
            }
        }
    }

    return false;
}
