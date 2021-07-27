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
#ifndef _ELF64_H
#define _ELF64_H 1

#if defined(__APPLE__)
#include <libelf/gelf.h>	/* brew install libelf */
#else
#include <elf.h>
#endif
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifndef EM_RISCV
#define EM_RISCV          0xF3 /* Little endian RISC-V, 32- and 64-bit */
#endif

bool elf64_is_riscv64(const uint8_t *image, size_t image_size);
bool elf64_find_global(const uint8_t *image, size_t image_size,
                       const char *key, uint64_t *value);

uint64_t elf64_get_entrypoint(const uint8_t *image);

#endif
