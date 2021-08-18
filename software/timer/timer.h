/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* 
 * Mantainer: Luca Valente (luca.valente2@unibo.it)
 */

#define TIMER_OFFSET 0xC1005000

static inline void enable_timer()
 {
   pulp_write32(TIMER_OFFSET+0x104,0xffff);
 }

static inline void config_counter(int timer_num, uint16_t prescaler, uint16_t mode, uint16_t insel, uint16_t updown, uint16_t clksel)
 {
   pulp_write32(TIMER_OFFSET+timer_num*0x40+0x4, ( (prescaler<<16) | (updown<<12) | (clksel<<11) | (mode<<8) | (insel) ) );
   return;
 }

static inline void set_counter_range(int timer_num, uint16_t low_th, uint16_t high_th)
 {
   pulp_write32(TIMER_OFFSET+timer_num*0x40+0x8,(high_th<<16) + low_th);
   return;
 }

static inline void set_threshold(int timer_num, int channel, int th, int mode)
 {
   pulp_write32(TIMER_OFFSET+timer_num*0x40+0xC+channel*0x4,(mode<<16) + th);
   return;
 }

static inline void start_timer()
 {
   pulp_write32(TIMER_OFFSET,1);
 }
