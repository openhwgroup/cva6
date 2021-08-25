/*
 * pulp_soc_defines.sv
 *
 * Copyright (C) 2013-2018 ETH Zurich, University of Bologna.
 *
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 */

/*
 * Collection of legacy pulp cluster defines.
 * 
 */

`define CLUSTER_ALIAS
`define PRIVATE_ICACHE
`define HIERARCHY_ICACHE_32BIT
`define SHARED_FPU_CLUSTER
`define FEATURE_ICACHE_STAT

`define FC_FPU 1
`define FC_FP_DIVSQRT 1
`define CLUST_FPU 1
`define CLUST_FP_DIVSQRT 1
// set to 2 when APU is connected
`define CLUST_SHARED_FP 2
// set to 2 to have divsqrt in one unit
`define CLUST_SHARED_FP_DIVSQRT 2

//PARAMETRES
`define NB_CLUSTERS   1
`define NB_CORES      8
`define NB_DMAS       4
`define NB_MPERIPHS   1
`define NB_SPERIPHS   10
