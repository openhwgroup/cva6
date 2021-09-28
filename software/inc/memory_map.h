/*
 * Copyright (C) 2018 ETH Zurich, University of Bologna
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


#ifndef __MEMORY_MAP_H__
#define __MEMORY_MAP_H__


/*
 * MEMORIES
 */

#define ARCHI_L2_PRIV0_ADDR  0x1c000000
#define ARCHI_L2_PRIV0_SIZE  0x00008000

#define ARCHI_L2_PRIV1_ADDR  0x1c008000
#define ARCHI_L2_PRIV1_SIZE  0x00008000

#define ARCHI_L2_SHARED_ADDR  0x1c010000
#define ARCHI_L2_SHARED_SIZE  0x00070000


/*
 * SOC PERIPHERALS
 */

#define ARCHI_SOC_PERIPHERALS_ADDR    0x1A100000

#define ARCHI_FC_TIMER_SIZE           0x00000800


#define ARCHI_FLL_OFFSET              0x00000000
#define ARCHI_GPIO_OFFSET             0x00001000
#define ARCHI_UDMA_OFFSET             0x00002000

#define ARCHI_HYAXICFG_OFFSET         0x00004000
#define ARCHI_ADVTIMER_OFFSET         0x00005000
#define ARCHI_PADFRAME_OFFSET         0x00006000

#define ARCHI_FC_ITC_OFFSET           0x00009800
#define ARCHI_FC_TIMER_OFFSET         0x0000B000
#define ARCHI_STDOUT_OFFSET           0x0000F000



#define ARCHI_GPIO_ADDR              ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_GPIO_OFFSET )
#define ARCHI_UDMA_ADDR              ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UDMA_OFFSET )

#define ARCHI_HYAXICFG_ADDR          ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_HYAXICFG_OFFSET )
#define ARCHI_ADVTIMER_ADDR          ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_ADVTIMER_OFFSET )
#define ARCHI_PADFRAME_ADDR          ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_PADFRAME_OFFSET )

#define ARCHI_FC_ITC_ADDR            ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_FC_ITC_OFFSET )
#define ARCHI_FC_TIMER_ADDR          ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_FC_TIMER_OFFSET )
#define ARCHI_STDOUT_ADDR            ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_STDOUT_OFFSET )

#define ARCHI_FLL_AREA_SIZE          0x00000010




/*
 * FC
 */

#define ARCHI_FC_ADDR                   0x00000000
#define ARCHI_FC_GLOBAL_ADDR            0x1B000000


/*
 * CLUSTER
 */

#define ARCHI_CLUSTER_ADDR              0x00000000
#define ARCHI_CLUSTER_SIZE              0x00400000
#define ARCHI_CLUSTER_GLOBAL_ADDR(cid)  (0x10000000 + (cid)*ARCHI_CLUSTER_SIZE)



/*
 * CLUSTER PERIPHERALS
 */

#define ARCHI_CLUSTER_PERIPHERALS_OFFSET 0x00200000

#define ARCHI_TIMER_SIZE                 0x00000800

#define ARCHI_CLUSTER_CTRL_OFFSET        0x00000000
#define ARCHI_TIMER_OFFSET               0x00000400
#define ARCHI_EU_OFFSET                  0x00000800
#define ARCHI_HWCE_OFFSET                0x00001000
#define ARCHI_ICACHE_CTRL_OFFSET         0x00001400
#define ARCHI_MCHAN_EXT_OFFSET           0x00001800

#define ARCHI_CLUSTER_PERIPHERALS_ADDR             ( ARCHI_CLUSTER_ADDR + ARCHI_CLUSTER_PERIPHERALS_OFFSET )
#define ARCHI_CLUSTER_PERIPHERALS_GLOBAL_ADDR(cid) ( ARCHI_CLUSTER_GLOBAL_ADDR(cid) + ARCHI_CLUSTER_PERIPHERALS_OFFSET )

#define ARCHI_CLUSTER_CTRL_ADDR                    ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_CLUSTER_CTRL_OFFSET )
#define ARCHI_ICACHE_CTRL_ADDR                     ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_ICACHE_CTRL_OFFSET )
#define ARCHI_EU_ADDR                              ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_EU_OFFSET )
#define ARCHI_HWCE_ADDR                            ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_HWCE_OFFSET )
#define ARCHI_MCHAN_EXT_ADDR                       ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_MCHAN_EXT_OFFSET )



/*
 * CLUSTER DEMUX PERIPHERALS
 */

#define ARCHI_DEMUX_PERIPHERALS_OFFSET        0x204000

#define ARCHI_EU_DEMUX_OFFSET                 ( 0x00000 )
#define ARCHI_MCHAN_DEMUX_OFFSET              ( 0x00400 )


#define ARCHI_DEMUX_PERIPHERALS_ADDR          ( ARCHI_CLUSTER_ADDR + ARCHI_DEMUX_PERIPHERALS_OFFSET )

#define ARCHI_EU_DEMUX_ADDR                   ( ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_EU_DEMUX_OFFSET )
#define ARCHI_MCHAN_DEMUX_ADDR                ( ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_MCHAN_DEMUX_OFFSET )

#endif
