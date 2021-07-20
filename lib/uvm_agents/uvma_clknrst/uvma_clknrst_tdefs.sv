// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 


`ifndef __UVMA_CLKNRST_TDEFS_SV__
`define __UVMA_CLKNRST_TDEFS_SV__


typedef enum {
   UVMA_CLKNRST_SEQ_ITEM_ACTION_START_CLK   ,
   UVMA_CLKNRST_SEQ_ITEM_ACTION_STOP_CLK    ,
   UVMA_CLKNRST_SEQ_ITEM_ACTION_ASSERT_RESET,
   UVMA_CLKNRST_SEQ_ITEM_ACTION_RESTART_CLK
} uvma_clknrst_seq_item_action_enum;

typedef enum {
   UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_0,
   UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_1,
   UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_X
} uvma_clknrst_seq_item_initial_value_enum;

typedef enum {
   UVMA_CLKNRST_MON_TRN_EVENT_CLK_STARTED     ,
   UVMA_CLKNRST_MON_TRN_EVENT_CLK_STOPPED     ,
   UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED  ,
   UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED
} uvma_clknrst_mon_trn_event_enum;


`endif // __UVMA_CLKNRST_TDEFS_SV__
