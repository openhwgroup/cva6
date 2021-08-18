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


#define ARCHI_UDMA_ADDR  0xC1000000 // = 3238002688
#define UDMA_HYPERBUS_OFFSET (3238002688 + 128*30)
#define HYPERBUS_DEVICE_NUM 29
#define CONFIG_REG_OFFSET 0x80

static inline void wait_cycles(const unsigned cycles)
{
  /**
   * Each iteration of the loop below will take four cycles on RI5CY (one for
   * `addi` and three for the taken `bnez`; if the instructions hit in the
   * I$).  Thus, we let `i` count the number of remaining loop iterations and
   * initialize it to a fourth of the number of clock cyles.  With this
   * initialization, we must not enter the loop if the number of clock cycles
   * is less than four, because this will cause an underflow on the first
   * subtraction.
   */
  register unsigned threshold;
  asm volatile("li %[threshold], 4" : [threshold] "=r" (threshold));
  asm volatile goto("ble %[cycles], %[threshold], %l2"
          : /* no output */
          : [cycles] "r" (cycles), [threshold] "r" (threshold)
          : /* no clobbers */
          : __wait_cycles_end);
  register unsigned i = cycles >> 2;
__wait_cycles_start:
  // Decrement `i` and loop if it is not yet zero.
  asm volatile("addi %0, %0, -1" : "+r" (i));
  asm volatile goto("bnez %0, %l1"
          : /* no output */
          : "r" (i)
          : /* no clobbers */
          : __wait_cycles_start);
__wait_cycles_end:
  return;
}

static inline void set_memsel_hyper(unsigned int mem_sel){
  pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x20, mem_sel); // hyperram 0, hyperflash 1, psram(x8) 2, psram(x16)3
}

static inline int check_memsel_hyper(){
  return pulp_read32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x20);
}

static inline void set_en_latency_add(unsigned int en){
  pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x08, en ); // REG_T_EN_LATENCY_ADD enable 1, deactivated 0
}

static inline void set_t_latency_access(unsigned int latency){
  pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x04, latency); 
}

static inline void set_t_cs_max(unsigned int period){
  pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x0C, period );
}

static inline void set_pagebound_hyper(unsigned int page_bound){

  switch(page_bound){
     case 128:
        pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x00, 0x00 ); // page boundary is set to every 128 bytes
        break;
     case 256:
        pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x00, 0x01 ); // page boundary is set to every 256 bytes
        break;
     case 512:
        pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x00, 0x02 ); // page boundary is set to every 128 bytes
        break;
     case 1024:
        pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x00, 0x03 ); // page boundary is set to every 256 bytes
        break;
     default:
        pulp_write32(UDMA_HYPERBUS_OFFSET + CONFIG_REG_OFFSET*8 + 0x00, 0x04 ); // page boundary is not considered
  }

}

static inline void set_twd_param_hyper(unsigned int twd_act_ext, unsigned int twd_count_ext,unsigned int twd_stride_ext, unsigned int twd_act_l2, unsigned int twd_count_l2, unsigned int twd_stride_l2, unsigned int tran_id){
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x28, twd_act_ext    ); // 2D TRAN is deactivated
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x2C, twd_count_ext  ); // 2D COUNT for ext mem
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x30, twd_stride_ext ); // 2D STRIDE for ext mem
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x34, twd_act_l2     ); // 2D TRAN is deactivated
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x38, twd_count_ext  ); // 2D COUNT for l2
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x3C, twd_stride_ext ); // 2D STRIDE for l2
}

static inline void set_tx_param_hyper(unsigned int len, unsigned int ext_addr, unsigned int l2_addr, unsigned int tran_id){
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x0C, l2_addr ); // Data address in L2
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x10, len );     // Data size to be sent
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x1C, ext_addr );// external memory address
}

static inline void set_rx_param_hyper(unsigned int len, unsigned int ext_addr, unsigned int l2_addr, unsigned int tran_id){
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x00, l2_addr ); // Data address in L2 
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x04, len );     // Data size 
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x1C, ext_addr );// external memory address
}

static inline void set_hyper_cfg(unsigned int data, unsigned int tran_id){
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x20, data); 
}

static inline void kick_reg_write_hyper(unsigned int tran_id){
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x18, 0x02); // Write is declared for the external mem
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x14, 0x14); // Write transaction is kicked
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x14, 0x00); // Write transaction information is reset
}

static inline void kick_mem_write_hyper(unsigned int tran_id){
  barrier();
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x18, 0x01); // Write is declared for the external mem
  barrier();
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x14, 0x14); // Write transaction is kicked
  barrier();
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x14, 0x00); // Write transaction information is reset
}

static inline void kick_flash_write_hyper(unsigned int tran_id){
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x18, 0x00); // Write is declared for the external mem
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x14, 0x14); // Write transaction is kicked
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x14, 0x00); // Write transaction information is reset
}

static inline void kick_read_hyper(unsigned int tran_id){
  barrier();
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x18, 0x05);     // Read is declared for the external mem
  barrier();
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x08, 0x14);     // Read transaction is kicked
  barrier();
  pulp_write32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x08, 0x00);     // Read transaction information is reset
}


static inline void udma_hyper_setup(){
  pulp_write32(ARCHI_UDMA_ADDR, 1 << HYPERBUS_DEVICE_NUM); // clock for the hyper bus module is activated
  set_en_latency_add(1);
  set_t_cs_max(0xffffffff);
  set_memsel_hyper(0);
  set_t_latency_access(6);
}


static inline void udma_spi8_setup(){
  pulp_write32(ARCHI_UDMA_ADDR, 1 << HYPERBUS_DEVICE_NUM); // clock for the hyper bus module is activated
  set_t_cs_max(0xffffffff);
  set_memsel_hyper(2);
  set_t_latency_access(6);

/* Setup for PSRAM side (MR0) */
  set_pagebound_hyper(0);
  set_tx_param_hyper(0,0,0,0); // MR address is set to 0
  set_hyper_cfg(0x2900,0); //PSRAM MR Data
  kick_reg_write_hyper(0); // PSRAM MR is set to 'h29
}

static inline void udma_spi16_setup(){
  pulp_write32(ARCHI_UDMA_ADDR, 1 << HYPERBUS_DEVICE_NUM); // clock for the hyper bus module is activated
  set_t_cs_max(0xffffffff);
  set_memsel_hyper(2);
  set_t_latency_access(5);

/* Setup for PSRAM side (MR0) */
  set_pagebound_hyper(0);
  set_tx_param_hyper(0,0,0,0); // MR address is set to 0
  set_hyper_cfg(0x2900,0);       // PSRAM MR Data
  kick_reg_write_hyper(0);     // PSRAM MR0 is set to 'h29

  set_tx_param_hyper(0,8,0,0); // MR address is set to 8
  set_hyper_cfg(0x4500,0);       // PSRAM MR Data
  kick_reg_write_hyper(0);     // PSRAM MR8 is set to 'h45
  set_memsel_hyper(3);
}


static inline void udma_hyper_flash_setup(){
   
  pulp_write32(ARCHI_UDMA_ADDR, 1 << HYPERBUS_DEVICE_NUM); // clock for the hyper bus module is activated
  while(pulp_read32(ARCHI_UDMA_ADDR)!= (1 << HYPERBUS_DEVICE_NUM));
  set_en_latency_add(0);
  set_t_cs_max(0xffffffff);
  set_memsel_hyper(1);
  set_t_latency_access(0x0f);
}

static inline void udma_hyper_sleep(){
  int a;
  a = pulp_read32(ARCHI_UDMA_ADDR);
  pulp_write32(ARCHI_UDMA_ADDR, (1 << HYPERBUS_DEVICE_NUM)^a ); // Clock gating is activated
}



// Burst write is conducted for the hyper flash. len <- burst length in bytes, ext_addr <- start address of the external memory, l2_addr <- start_address of the L2 memory, page_bound <- page boundary in the external memory
static inline void udma_hyper_dwrite(unsigned int len, unsigned int ext_addr, unsigned int l2_addr, unsigned int page_bound, unsigned int tran_id){

  int memsel;
  memsel = check_memsel_hyper();
  set_pagebound_hyper(page_bound);
  set_twd_param_hyper(0, 0, 0, 0, 0, 0, tran_id);

  if(memsel==2 | memsel==3) set_en_latency_add(0);
  else set_en_latency_add(1); 

  set_tx_param_hyper(len, ext_addr, l2_addr, tran_id);
  barrier();
  kick_mem_write_hyper(tran_id);
}


static inline void udma_hyper_twd_dwrite(unsigned int len, unsigned int ext_addr, unsigned int l2_addr, unsigned int page_bound, unsigned int twd_act_ext, unsigned int twd_count_ext,unsigned int twd_stride_ext, unsigned int twd_act_l2, unsigned int twd_count_l2, unsigned int twd_stride_l2, unsigned int tran_id){

  int memsel;
  memsel = check_memsel_hyper();
  set_pagebound_hyper(page_bound);
  set_twd_param_hyper( twd_act_ext, twd_count_ext, twd_stride_ext, twd_act_l2, twd_count_l2, twd_stride_l2, tran_id);

  if(memsel==2 | memsel==3) set_en_latency_add(0);
  else set_en_latency_add(1); 

  set_tx_param_hyper(len, ext_addr, l2_addr, tran_id);
  kick_mem_write_hyper(tran_id);
}


// Word write for Hyper flash
static inline void udma_hyperflash_wwrite(unsigned int ext_addr, short int data, unsigned int tran_id){

  set_pagebound_hyper(0);
  set_en_latency_add(0); 
  set_tx_param_hyper(0, ext_addr<<1, 0, tran_id);
  set_hyper_cfg(data,tran_id); 
  kick_flash_write_hyper(tran_id);
}

static inline void udma_hyperflash_wpwrite(unsigned int ext_addr, short int data, unsigned int tran_id){
    udma_hyperflash_wwrite(0x555, 0x00aa, tran_id);
    udma_hyperflash_wwrite(0x2aa, 0x0055, tran_id);
    udma_hyperflash_wwrite(0x555, 0x00a0, tran_id);
    udma_hyperflash_wwrite(ext_addr, data, tran_id);
    wait_cycles(125000);
}



static inline int udma_hyper_nb_tran(unsigned int tran_id){
  return pulp_read32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x24) >> 1;
}


// Burst write for Hyper flash. Page boundary consideration and byte addressing mode are NOT supported. nb_word <- burst length in words, hyper_waddr <- start address of the hyperflash (word addressing), l2_addr <- start_address for L2
static inline void udma_hyperflash_bwrite(unsigned int nb_word, unsigned int hyper_waddr, unsigned int l2_addr, unsigned int tran_id){

    udma_hyperflash_wwrite(0x555, 0x00aa, tran_id);
    udma_hyperflash_wwrite(0x2aa, 0x0055, tran_id);
    udma_hyperflash_wwrite(hyper_waddr, 0x0025, tran_id);
    udma_hyperflash_wwrite(hyper_waddr, nb_word-1, tran_id);
    for(int i=0; i< nb_word; i++ ){
       while(udma_hyper_nb_tran(tran_id)>7){}
       udma_hyperflash_wwrite(hyper_waddr+i, *((short int *) l2_addr+i), tran_id);
    }
    udma_hyperflash_wwrite(hyper_waddr, 0x0029, tran_id);
    wait_cycles(125000);
}

static inline void udma_hyperflash_erase(unsigned int sector_addr, unsigned int tran_id){
    udma_hyperflash_wwrite(0x555, 0x00aa, tran_id);
    udma_hyperflash_wwrite(0x2aa, 0x0055, tran_id);
    udma_hyperflash_wwrite(0x555, 0x0080, tran_id);
    udma_hyperflash_wwrite(0x555, 0x00aa, tran_id);
    udma_hyperflash_wwrite(0x2aa, 0x0055, tran_id);
    udma_hyperflash_wwrite(sector_addr, 0x0030, tran_id);
    wait_cycles(125000);
}

// Linear read is conducted. len <- burst length in bytes, ext_addr <- start address of the external memory, l2_addr <- start_address of the L2 memory, page_bound <- page boundary in the external memory
//

static inline void udma_hyper_dread(unsigned int len, unsigned int ext_addr, unsigned int l2_addr, unsigned int page_bound, unsigned int tran_id){

  int memsel;
  memsel = check_memsel_hyper();
  set_pagebound_hyper(page_bound);
  set_twd_param_hyper(0, 0, 0, 0, 0, 0, tran_id);

  if(memsel!=1) set_en_latency_add(1);
  else set_en_latency_add(0);

  set_rx_param_hyper(len, ext_addr, l2_addr, tran_id);
  kick_read_hyper(tran_id);
}

static inline void udma_hyper_twd_dread(unsigned int len, unsigned int ext_addr, unsigned int l2_addr, unsigned int page_bound, unsigned int twd_act_ext, unsigned int twd_count_ext,unsigned int twd_stride_ext, unsigned int twd_act_l2, unsigned int twd_count_l2, unsigned int twd_stride_l2, unsigned int tran_id){

  int memsel;
  memsel = check_memsel_hyper();
  set_pagebound_hyper(page_bound);
  set_twd_param_hyper( twd_act_ext, twd_count_ext, twd_stride_ext, twd_act_l2, twd_count_l2, twd_stride_l2, tran_id);

  if(memsel!=1) set_en_latency_add(1);
  else set_en_latency_add(0);

  set_rx_param_hyper(len, ext_addr, l2_addr, tran_id);
  kick_read_hyper(tran_id);
}

// If the hyperbus module is doing something.
static inline int udma_hyper_busy(unsigned int tran_id){
  return pulp_read32(UDMA_HYPERBUS_OFFSET + tran_id*CONFIG_REG_OFFSET + 0x24) & 0x00000001;
}

static inline void udma_hyper_wait(unsigned int tran_id){
   while(udma_hyper_busy(tran_id)){
   }
}

static inline int udma_hyper_id_alloc(){
  return pulp_read32(UDMA_HYPERBUS_OFFSET + 8*CONFIG_REG_OFFSET + 0x24);
}
