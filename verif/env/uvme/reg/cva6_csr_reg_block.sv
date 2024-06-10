//
// Copyright 2020 OpenHW Group
// Copyright 2023 Thales DIS
//
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

class cva6_csr_reg_block extends uvm_reg_block;
  `uvm_object_utils(cva6_csr_reg_block)
  
  //---------------------------------------
  // register instances 
  //---------------------------------------
  rand reg_mstatus  mstatus; 
  rand reg_misa  misa; 
  rand reg_mie  mie; 
  rand reg_mtvec  mtvec; 
  rand reg_mstatush  mstatush; 
  rand reg_mhpmevent3  mhpmevent3; 
  rand reg_mhpmevent4  mhpmevent4; 
  rand reg_mhpmevent5  mhpmevent5; 
  rand reg_mhpmevent6  mhpmevent6; 
  rand reg_mhpmevent7  mhpmevent7; 
  rand reg_mhpmevent8  mhpmevent8; 
  rand reg_mhpmevent9  mhpmevent9; 
  rand reg_mhpmevent10  mhpmevent10; 
  rand reg_mhpmevent11  mhpmevent11; 
  rand reg_mhpmevent12  mhpmevent12; 
  rand reg_mhpmevent13  mhpmevent13; 
  rand reg_mhpmevent14  mhpmevent14; 
  rand reg_mhpmevent15  mhpmevent15; 
  rand reg_mhpmevent16  mhpmevent16; 
  rand reg_mhpmevent17  mhpmevent17; 
  rand reg_mhpmevent18  mhpmevent18; 
  rand reg_mhpmevent19  mhpmevent19; 
  rand reg_mhpmevent20  mhpmevent20; 
  rand reg_mhpmevent21  mhpmevent21; 
  rand reg_mhpmevent22  mhpmevent22; 
  rand reg_mhpmevent23  mhpmevent23; 
  rand reg_mhpmevent24  mhpmevent24; 
  rand reg_mhpmevent25  mhpmevent25; 
  rand reg_mhpmevent26  mhpmevent26; 
  rand reg_mhpmevent27  mhpmevent27; 
  rand reg_mhpmevent28  mhpmevent28; 
  rand reg_mhpmevent29  mhpmevent29; 
  rand reg_mhpmevent30  mhpmevent30; 
  rand reg_mhpmevent31  mhpmevent31; 
  rand reg_mscratch  mscratch; 
  rand reg_mepc  mepc; 
  rand reg_mcause  mcause; 
  rand reg_mtval  mtval; 
  rand reg_mip  mip; 
  rand reg_pmpcfg0  pmpcfg0; 
  rand reg_pmpcfg1  pmpcfg1; 
  rand reg_pmpcfg2  pmpcfg2; 
  rand reg_pmpcfg3  pmpcfg3; 
  rand reg_pmpaddr0  pmpaddr0; 
  rand reg_pmpaddr1  pmpaddr1; 
  rand reg_pmpaddr2  pmpaddr2; 
  rand reg_pmpaddr3  pmpaddr3; 
  rand reg_pmpaddr4  pmpaddr4; 
  rand reg_pmpaddr5  pmpaddr5; 
  rand reg_pmpaddr6  pmpaddr6; 
  rand reg_pmpaddr7  pmpaddr7; 
  rand reg_pmpaddr8  pmpaddr8; 
  rand reg_pmpaddr9  pmpaddr9; 
  rand reg_pmpaddr10  pmpaddr10; 
  rand reg_pmpaddr11  pmpaddr11; 
  rand reg_pmpaddr12  pmpaddr12; 
  rand reg_pmpaddr13  pmpaddr13; 
  rand reg_pmpaddr14  pmpaddr14; 
  rand reg_pmpaddr15  pmpaddr15; 
  rand reg_icache  icache; 
  rand reg_mcycle  mcycle; 
  rand reg_minstret  minstret; 
  rand reg_mcycleh  mcycleh; 
  rand reg_minstreth  minstreth; 
  rand reg_mhpmcounter3  mhpmcounter3; 
  rand reg_mhpmcounter4  mhpmcounter4; 
  rand reg_mhpmcounter5  mhpmcounter5; 
  rand reg_mhpmcounter6  mhpmcounter6; 
  rand reg_mhpmcounter7  mhpmcounter7; 
  rand reg_mhpmcounter8  mhpmcounter8; 
  rand reg_mhpmcounter9  mhpmcounter9; 
  rand reg_mhpmcounter10  mhpmcounter10; 
  rand reg_mhpmcounter11  mhpmcounter11; 
  rand reg_mhpmcounter12  mhpmcounter12; 
  rand reg_mhpmcounter13  mhpmcounter13; 
  rand reg_mhpmcounter14  mhpmcounter14; 
  rand reg_mhpmcounter15  mhpmcounter15; 
  rand reg_mhpmcounter16  mhpmcounter16; 
  rand reg_mhpmcounter17  mhpmcounter17; 
  rand reg_mhpmcounter18  mhpmcounter18; 
  rand reg_mhpmcounter19  mhpmcounter19; 
  rand reg_mhpmcounter20  mhpmcounter20; 
  rand reg_mhpmcounter21  mhpmcounter21; 
  rand reg_mhpmcounter22  mhpmcounter22; 
  rand reg_mhpmcounter23  mhpmcounter23; 
  rand reg_mhpmcounter24  mhpmcounter24; 
  rand reg_mhpmcounter25  mhpmcounter25; 
  rand reg_mhpmcounter26  mhpmcounter26; 
  rand reg_mhpmcounter27  mhpmcounter27; 
  rand reg_mhpmcounter28  mhpmcounter28; 
  rand reg_mhpmcounter29  mhpmcounter29; 
  rand reg_mhpmcounter30  mhpmcounter30; 
  rand reg_mhpmcounter31  mhpmcounter31; 
  rand reg_mhpmcounterh3  mhpmcounterh3; 
  rand reg_mhpmcounterh4  mhpmcounterh4; 
  rand reg_mhpmcounterh5  mhpmcounterh5; 
  rand reg_mhpmcounterh6  mhpmcounterh6; 
  rand reg_mhpmcounterh7  mhpmcounterh7; 
  rand reg_mhpmcounterh8  mhpmcounterh8; 
  rand reg_mhpmcounterh9  mhpmcounterh9; 
  rand reg_mhpmcounterh10  mhpmcounterh10; 
  rand reg_mhpmcounterh11  mhpmcounterh11; 
  rand reg_mhpmcounterh12  mhpmcounterh12; 
  rand reg_mhpmcounterh13  mhpmcounterh13; 
  rand reg_mhpmcounterh14  mhpmcounterh14; 
  rand reg_mhpmcounterh15  mhpmcounterh15; 
  rand reg_mhpmcounterh16  mhpmcounterh16; 
  rand reg_mhpmcounterh17  mhpmcounterh17; 
  rand reg_mhpmcounterh18  mhpmcounterh18; 
  rand reg_mhpmcounterh19  mhpmcounterh19; 
  rand reg_mhpmcounterh20  mhpmcounterh20; 
  rand reg_mhpmcounterh21  mhpmcounterh21; 
  rand reg_mhpmcounterh22  mhpmcounterh22; 
  rand reg_mhpmcounterh23  mhpmcounterh23; 
  rand reg_mhpmcounterh24  mhpmcounterh24; 
  rand reg_mhpmcounterh25  mhpmcounterh25; 
  rand reg_mhpmcounterh26  mhpmcounterh26; 
  rand reg_mhpmcounterh27  mhpmcounterh27; 
  rand reg_mhpmcounterh28  mhpmcounterh28; 
  rand reg_mhpmcounterh29  mhpmcounterh29; 
  rand reg_mhpmcounterh30  mhpmcounterh30; 
  rand reg_mhpmcounterh31  mhpmcounterh31; 
  rand reg_mvendorid  mvendorid; 
  rand reg_marchid  marchid; 
  rand reg_mimpid  mimpid; 
  rand reg_mhartid  mhartid; 
  
  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "");
    super.new(name, .has_coverage(UVM_CVR_ALL));
  endfunction

  //---------------------------------------
  // Build Phase 
  //---------------------------------------
  virtual function build();
    
    //---------------------------------------
    //reg creation
    //---------------------------------------
    mstatus = reg_mstatus::type_id::create("mstatus", null, get_full_name());
    mstatus.configure(this, null, "mstatus");
    mstatus.build();

    misa = reg_misa::type_id::create("misa", null, get_full_name());
    misa.configure(this, null, "misa");
    misa.build();

    mie = reg_mie::type_id::create("mie", null, get_full_name());
    mie.configure(this, null, "mie");
    mie.build();

    mtvec = reg_mtvec::type_id::create("mtvec", null, get_full_name());
    mtvec.configure(this, null, "mtvec");
    mtvec.build();

    mstatush = reg_mstatush::type_id::create("mstatush", null, get_full_name());
    mstatush.configure(this, null, "mstatush");
    mstatush.build();

    mhpmevent3 = reg_mhpmevent3::type_id::create("mhpmevent3", null, get_full_name());
    mhpmevent3.configure(this, null, "mhpmevent3");
    mhpmevent3.build();

    mhpmevent4 = reg_mhpmevent4::type_id::create("mhpmevent4", null, get_full_name());
    mhpmevent4.configure(this, null, "mhpmevent4");
    mhpmevent4.build();

    mhpmevent5 = reg_mhpmevent5::type_id::create("mhpmevent5", null, get_full_name());
    mhpmevent5.configure(this, null, "mhpmevent5");
    mhpmevent5.build();

    mhpmevent6 = reg_mhpmevent6::type_id::create("mhpmevent6", null, get_full_name());
    mhpmevent6.configure(this, null, "mhpmevent6");
    mhpmevent6.build();

    mhpmevent7 = reg_mhpmevent7::type_id::create("mhpmevent7", null, get_full_name());
    mhpmevent7.configure(this, null, "mhpmevent7");
    mhpmevent7.build();

    mhpmevent8 = reg_mhpmevent8::type_id::create("mhpmevent8", null, get_full_name());
    mhpmevent8.configure(this, null, "mhpmevent8");
    mhpmevent8.build();

    mhpmevent9 = reg_mhpmevent9::type_id::create("mhpmevent9", null, get_full_name());
    mhpmevent9.configure(this, null, "mhpmevent9");
    mhpmevent9.build();

    mhpmevent10 = reg_mhpmevent10::type_id::create("mhpmevent10", null, get_full_name());
    mhpmevent10.configure(this, null, "mhpmevent10");
    mhpmevent10.build();

    mhpmevent11 = reg_mhpmevent11::type_id::create("mhpmevent11", null, get_full_name());
    mhpmevent11.configure(this, null, "mhpmevent11");
    mhpmevent11.build();

    mhpmevent12 = reg_mhpmevent12::type_id::create("mhpmevent12", null, get_full_name());
    mhpmevent12.configure(this, null, "mhpmevent12");
    mhpmevent12.build();

    mhpmevent13 = reg_mhpmevent13::type_id::create("mhpmevent13", null, get_full_name());
    mhpmevent13.configure(this, null, "mhpmevent13");
    mhpmevent13.build();

    mhpmevent14 = reg_mhpmevent14::type_id::create("mhpmevent14", null, get_full_name());
    mhpmevent14.configure(this, null, "mhpmevent14");
    mhpmevent14.build();

    mhpmevent15 = reg_mhpmevent15::type_id::create("mhpmevent15", null, get_full_name());
    mhpmevent15.configure(this, null, "mhpmevent15");
    mhpmevent15.build();

    mhpmevent16 = reg_mhpmevent16::type_id::create("mhpmevent16", null, get_full_name());
    mhpmevent16.configure(this, null, "mhpmevent16");
    mhpmevent16.build();

    mhpmevent17 = reg_mhpmevent17::type_id::create("mhpmevent17", null, get_full_name());
    mhpmevent17.configure(this, null, "mhpmevent17");
    mhpmevent17.build();

    mhpmevent18 = reg_mhpmevent18::type_id::create("mhpmevent18", null, get_full_name());
    mhpmevent18.configure(this, null, "mhpmevent18");
    mhpmevent18.build();

    mhpmevent19 = reg_mhpmevent19::type_id::create("mhpmevent19", null, get_full_name());
    mhpmevent19.configure(this, null, "mhpmevent19");
    mhpmevent19.build();

    mhpmevent20 = reg_mhpmevent20::type_id::create("mhpmevent20", null, get_full_name());
    mhpmevent20.configure(this, null, "mhpmevent20");
    mhpmevent20.build();

    mhpmevent21 = reg_mhpmevent21::type_id::create("mhpmevent21", null, get_full_name());
    mhpmevent21.configure(this, null, "mhpmevent21");
    mhpmevent21.build();

    mhpmevent22 = reg_mhpmevent22::type_id::create("mhpmevent22", null, get_full_name());
    mhpmevent22.configure(this, null, "mhpmevent22");
    mhpmevent22.build();

    mhpmevent23 = reg_mhpmevent23::type_id::create("mhpmevent23", null, get_full_name());
    mhpmevent23.configure(this, null, "mhpmevent23");
    mhpmevent23.build();

    mhpmevent24 = reg_mhpmevent24::type_id::create("mhpmevent24", null, get_full_name());
    mhpmevent24.configure(this, null, "mhpmevent24");
    mhpmevent24.build();

    mhpmevent25 = reg_mhpmevent25::type_id::create("mhpmevent25", null, get_full_name());
    mhpmevent25.configure(this, null, "mhpmevent25");
    mhpmevent25.build();

    mhpmevent26 = reg_mhpmevent26::type_id::create("mhpmevent26", null, get_full_name());
    mhpmevent26.configure(this, null, "mhpmevent26");
    mhpmevent26.build();

    mhpmevent27 = reg_mhpmevent27::type_id::create("mhpmevent27", null, get_full_name());
    mhpmevent27.configure(this, null, "mhpmevent27");
    mhpmevent27.build();

    mhpmevent28 = reg_mhpmevent28::type_id::create("mhpmevent28", null, get_full_name());
    mhpmevent28.configure(this, null, "mhpmevent28");
    mhpmevent28.build();

    mhpmevent29 = reg_mhpmevent29::type_id::create("mhpmevent29", null, get_full_name());
    mhpmevent29.configure(this, null, "mhpmevent29");
    mhpmevent29.build();

    mhpmevent30 = reg_mhpmevent30::type_id::create("mhpmevent30", null, get_full_name());
    mhpmevent30.configure(this, null, "mhpmevent30");
    mhpmevent30.build();

    mhpmevent31 = reg_mhpmevent31::type_id::create("mhpmevent31", null, get_full_name());
    mhpmevent31.configure(this, null, "mhpmevent31");
    mhpmevent31.build();

    mscratch = reg_mscratch::type_id::create("mscratch", null, get_full_name());
    mscratch.configure(this, null, "mscratch");
    mscratch.build();

    mepc = reg_mepc::type_id::create("mepc", null, get_full_name());
    mepc.configure(this, null, "mepc");
    mepc.build();

    mcause = reg_mcause::type_id::create("mcause", null, get_full_name());
    mcause.configure(this, null, "mcause");
    mcause.build();

    mtval = reg_mtval::type_id::create("mtval", null, get_full_name());
    mtval.configure(this, null, "mtval");
    mtval.build();

    mip = reg_mip::type_id::create("mip", null, get_full_name());
    mip.configure(this, null, "mip");
    mip.build();

    pmpcfg0 = reg_pmpcfg0::type_id::create("pmpcfg0", null, get_full_name());
    pmpcfg0.configure(this, null, "pmpcfg0");
    pmpcfg0.build();

    pmpcfg1 = reg_pmpcfg1::type_id::create("pmpcfg1", null, get_full_name());
    pmpcfg1.configure(this, null, "pmpcfg1");
    pmpcfg1.build();

    pmpcfg2 = reg_pmpcfg2::type_id::create("pmpcfg2", null, get_full_name());
    pmpcfg2.configure(this, null, "pmpcfg2");
    pmpcfg2.build();

    pmpcfg3 = reg_pmpcfg3::type_id::create("pmpcfg3", null, get_full_name());
    pmpcfg3.configure(this, null, "pmpcfg3");
    pmpcfg3.build();

    pmpaddr0 = reg_pmpaddr0::type_id::create("pmpaddr0", null, get_full_name());
    pmpaddr0.configure(this, null, "pmpaddr0");
    pmpaddr0.build();

    pmpaddr1 = reg_pmpaddr1::type_id::create("pmpaddr1", null, get_full_name());
    pmpaddr1.configure(this, null, "pmpaddr1");
    pmpaddr1.build();

    pmpaddr2 = reg_pmpaddr2::type_id::create("pmpaddr2", null, get_full_name());
    pmpaddr2.configure(this, null, "pmpaddr2");
    pmpaddr2.build();

    pmpaddr3 = reg_pmpaddr3::type_id::create("pmpaddr3", null, get_full_name());
    pmpaddr3.configure(this, null, "pmpaddr3");
    pmpaddr3.build();

    pmpaddr4 = reg_pmpaddr4::type_id::create("pmpaddr4", null, get_full_name());
    pmpaddr4.configure(this, null, "pmpaddr4");
    pmpaddr4.build();

    pmpaddr5 = reg_pmpaddr5::type_id::create("pmpaddr5", null, get_full_name());
    pmpaddr5.configure(this, null, "pmpaddr5");
    pmpaddr5.build();

    pmpaddr6 = reg_pmpaddr6::type_id::create("pmpaddr6", null, get_full_name());
    pmpaddr6.configure(this, null, "pmpaddr6");
    pmpaddr6.build();

    pmpaddr7 = reg_pmpaddr7::type_id::create("pmpaddr7", null, get_full_name());
    pmpaddr7.configure(this, null, "pmpaddr7");
    pmpaddr7.build();

    pmpaddr8 = reg_pmpaddr8::type_id::create("pmpaddr8", null, get_full_name());
    pmpaddr8.configure(this, null, "pmpaddr8");
    pmpaddr8.build();

    pmpaddr9 = reg_pmpaddr9::type_id::create("pmpaddr9", null, get_full_name());
    pmpaddr9.configure(this, null, "pmpaddr9");
    pmpaddr9.build();

    pmpaddr10 = reg_pmpaddr10::type_id::create("pmpaddr10", null, get_full_name());
    pmpaddr10.configure(this, null, "pmpaddr10");
    pmpaddr10.build();

    pmpaddr11 = reg_pmpaddr11::type_id::create("pmpaddr11", null, get_full_name());
    pmpaddr11.configure(this, null, "pmpaddr11");
    pmpaddr11.build();

    pmpaddr12 = reg_pmpaddr12::type_id::create("pmpaddr12", null, get_full_name());
    pmpaddr12.configure(this, null, "pmpaddr12");
    pmpaddr12.build();

    pmpaddr13 = reg_pmpaddr13::type_id::create("pmpaddr13", null, get_full_name());
    pmpaddr13.configure(this, null, "pmpaddr13");
    pmpaddr13.build();

    pmpaddr14 = reg_pmpaddr14::type_id::create("pmpaddr14", null, get_full_name());
    pmpaddr14.configure(this, null, "pmpaddr14");
    pmpaddr14.build();

    pmpaddr15 = reg_pmpaddr15::type_id::create("pmpaddr15", null, get_full_name());
    pmpaddr15.configure(this, null, "pmpaddr15");
    pmpaddr15.build();

    icache = reg_icache::type_id::create("icache", null, get_full_name());
    icache.configure(this, null, "icache");
    icache.build();

    mcycle = reg_mcycle::type_id::create("mcycle", null, get_full_name());
    mcycle.configure(this, null, "mcycle");
    mcycle.build();

    minstret = reg_minstret::type_id::create("minstret", null, get_full_name());
    minstret.configure(this, null, "minstret");
    minstret.build();

    mcycleh = reg_mcycleh::type_id::create("mcycleh", null, get_full_name());
    mcycleh.configure(this, null, "mcycleh");
    mcycleh.build();

    minstreth = reg_minstreth::type_id::create("minstreth", null, get_full_name());
    minstreth.configure(this, null, "minstreth");
    minstreth.build();

    mhpmcounter3 = reg_mhpmcounter3::type_id::create("mhpmcounter3", null, get_full_name());
    mhpmcounter3.configure(this, null, "mhpmcounter3");
    mhpmcounter3.build();

    mhpmcounter4 = reg_mhpmcounter4::type_id::create("mhpmcounter4", null, get_full_name());
    mhpmcounter4.configure(this, null, "mhpmcounter4");
    mhpmcounter4.build();

    mhpmcounter5 = reg_mhpmcounter5::type_id::create("mhpmcounter5", null, get_full_name());
    mhpmcounter5.configure(this, null, "mhpmcounter5");
    mhpmcounter5.build();

    mhpmcounter6 = reg_mhpmcounter6::type_id::create("mhpmcounter6", null, get_full_name());
    mhpmcounter6.configure(this, null, "mhpmcounter6");
    mhpmcounter6.build();

    mhpmcounter7 = reg_mhpmcounter7::type_id::create("mhpmcounter7", null, get_full_name());
    mhpmcounter7.configure(this, null, "mhpmcounter7");
    mhpmcounter7.build();

    mhpmcounter8 = reg_mhpmcounter8::type_id::create("mhpmcounter8", null, get_full_name());
    mhpmcounter8.configure(this, null, "mhpmcounter8");
    mhpmcounter8.build();

    mhpmcounter9 = reg_mhpmcounter9::type_id::create("mhpmcounter9", null, get_full_name());
    mhpmcounter9.configure(this, null, "mhpmcounter9");
    mhpmcounter9.build();

    mhpmcounter10 = reg_mhpmcounter10::type_id::create("mhpmcounter10", null, get_full_name());
    mhpmcounter10.configure(this, null, "mhpmcounter10");
    mhpmcounter10.build();

    mhpmcounter11 = reg_mhpmcounter11::type_id::create("mhpmcounter11", null, get_full_name());
    mhpmcounter11.configure(this, null, "mhpmcounter11");
    mhpmcounter11.build();

    mhpmcounter12 = reg_mhpmcounter12::type_id::create("mhpmcounter12", null, get_full_name());
    mhpmcounter12.configure(this, null, "mhpmcounter12");
    mhpmcounter12.build();

    mhpmcounter13 = reg_mhpmcounter13::type_id::create("mhpmcounter13", null, get_full_name());
    mhpmcounter13.configure(this, null, "mhpmcounter13");
    mhpmcounter13.build();

    mhpmcounter14 = reg_mhpmcounter14::type_id::create("mhpmcounter14", null, get_full_name());
    mhpmcounter14.configure(this, null, "mhpmcounter14");
    mhpmcounter14.build();

    mhpmcounter15 = reg_mhpmcounter15::type_id::create("mhpmcounter15", null, get_full_name());
    mhpmcounter15.configure(this, null, "mhpmcounter15");
    mhpmcounter15.build();

    mhpmcounter16 = reg_mhpmcounter16::type_id::create("mhpmcounter16", null, get_full_name());
    mhpmcounter16.configure(this, null, "mhpmcounter16");
    mhpmcounter16.build();

    mhpmcounter17 = reg_mhpmcounter17::type_id::create("mhpmcounter17", null, get_full_name());
    mhpmcounter17.configure(this, null, "mhpmcounter17");
    mhpmcounter17.build();

    mhpmcounter18 = reg_mhpmcounter18::type_id::create("mhpmcounter18", null, get_full_name());
    mhpmcounter18.configure(this, null, "mhpmcounter18");
    mhpmcounter18.build();

    mhpmcounter19 = reg_mhpmcounter19::type_id::create("mhpmcounter19", null, get_full_name());
    mhpmcounter19.configure(this, null, "mhpmcounter19");
    mhpmcounter19.build();

    mhpmcounter20 = reg_mhpmcounter20::type_id::create("mhpmcounter20", null, get_full_name());
    mhpmcounter20.configure(this, null, "mhpmcounter20");
    mhpmcounter20.build();

    mhpmcounter21 = reg_mhpmcounter21::type_id::create("mhpmcounter21", null, get_full_name());
    mhpmcounter21.configure(this, null, "mhpmcounter21");
    mhpmcounter21.build();

    mhpmcounter22 = reg_mhpmcounter22::type_id::create("mhpmcounter22", null, get_full_name());
    mhpmcounter22.configure(this, null, "mhpmcounter22");
    mhpmcounter22.build();

    mhpmcounter23 = reg_mhpmcounter23::type_id::create("mhpmcounter23", null, get_full_name());
    mhpmcounter23.configure(this, null, "mhpmcounter23");
    mhpmcounter23.build();

    mhpmcounter24 = reg_mhpmcounter24::type_id::create("mhpmcounter24", null, get_full_name());
    mhpmcounter24.configure(this, null, "mhpmcounter24");
    mhpmcounter24.build();

    mhpmcounter25 = reg_mhpmcounter25::type_id::create("mhpmcounter25", null, get_full_name());
    mhpmcounter25.configure(this, null, "mhpmcounter25");
    mhpmcounter25.build();

    mhpmcounter26 = reg_mhpmcounter26::type_id::create("mhpmcounter26", null, get_full_name());
    mhpmcounter26.configure(this, null, "mhpmcounter26");
    mhpmcounter26.build();

    mhpmcounter27 = reg_mhpmcounter27::type_id::create("mhpmcounter27", null, get_full_name());
    mhpmcounter27.configure(this, null, "mhpmcounter27");
    mhpmcounter27.build();

    mhpmcounter28 = reg_mhpmcounter28::type_id::create("mhpmcounter28", null, get_full_name());
    mhpmcounter28.configure(this, null, "mhpmcounter28");
    mhpmcounter28.build();

    mhpmcounter29 = reg_mhpmcounter29::type_id::create("mhpmcounter29", null, get_full_name());
    mhpmcounter29.configure(this, null, "mhpmcounter29");
    mhpmcounter29.build();

    mhpmcounter30 = reg_mhpmcounter30::type_id::create("mhpmcounter30", null, get_full_name());
    mhpmcounter30.configure(this, null, "mhpmcounter30");
    mhpmcounter30.build();

    mhpmcounter31 = reg_mhpmcounter31::type_id::create("mhpmcounter31", null, get_full_name());
    mhpmcounter31.configure(this, null, "mhpmcounter31");
    mhpmcounter31.build();

    mhpmcounterh3 = reg_mhpmcounterh3::type_id::create("mhpmcounterh3", null, get_full_name());
    mhpmcounterh3.configure(this, null, "mhpmcounterh3");
    mhpmcounterh3.build();

    mhpmcounterh4 = reg_mhpmcounterh4::type_id::create("mhpmcounterh4", null, get_full_name());
    mhpmcounterh4.configure(this, null, "mhpmcounterh4");
    mhpmcounterh4.build();

    mhpmcounterh5 = reg_mhpmcounterh5::type_id::create("mhpmcounterh5", null, get_full_name());
    mhpmcounterh5.configure(this, null, "mhpmcounterh5");
    mhpmcounterh5.build();

    mhpmcounterh6 = reg_mhpmcounterh6::type_id::create("mhpmcounterh6", null, get_full_name());
    mhpmcounterh6.configure(this, null, "mhpmcounterh6");
    mhpmcounterh6.build();

    mhpmcounterh7 = reg_mhpmcounterh7::type_id::create("mhpmcounterh7", null, get_full_name());
    mhpmcounterh7.configure(this, null, "mhpmcounterh7");
    mhpmcounterh7.build();

    mhpmcounterh8 = reg_mhpmcounterh8::type_id::create("mhpmcounterh8", null, get_full_name());
    mhpmcounterh8.configure(this, null, "mhpmcounterh8");
    mhpmcounterh8.build();

    mhpmcounterh9 = reg_mhpmcounterh9::type_id::create("mhpmcounterh9", null, get_full_name());
    mhpmcounterh9.configure(this, null, "mhpmcounterh9");
    mhpmcounterh9.build();

    mhpmcounterh10 = reg_mhpmcounterh10::type_id::create("mhpmcounterh10", null, get_full_name());
    mhpmcounterh10.configure(this, null, "mhpmcounterh10");
    mhpmcounterh10.build();

    mhpmcounterh11 = reg_mhpmcounterh11::type_id::create("mhpmcounterh11", null, get_full_name());
    mhpmcounterh11.configure(this, null, "mhpmcounterh11");
    mhpmcounterh11.build();

    mhpmcounterh12 = reg_mhpmcounterh12::type_id::create("mhpmcounterh12", null, get_full_name());
    mhpmcounterh12.configure(this, null, "mhpmcounterh12");
    mhpmcounterh12.build();

    mhpmcounterh13 = reg_mhpmcounterh13::type_id::create("mhpmcounterh13", null, get_full_name());
    mhpmcounterh13.configure(this, null, "mhpmcounterh13");
    mhpmcounterh13.build();

    mhpmcounterh14 = reg_mhpmcounterh14::type_id::create("mhpmcounterh14", null, get_full_name());
    mhpmcounterh14.configure(this, null, "mhpmcounterh14");
    mhpmcounterh14.build();

    mhpmcounterh15 = reg_mhpmcounterh15::type_id::create("mhpmcounterh15", null, get_full_name());
    mhpmcounterh15.configure(this, null, "mhpmcounterh15");
    mhpmcounterh15.build();

    mhpmcounterh16 = reg_mhpmcounterh16::type_id::create("mhpmcounterh16", null, get_full_name());
    mhpmcounterh16.configure(this, null, "mhpmcounterh16");
    mhpmcounterh16.build();

    mhpmcounterh17 = reg_mhpmcounterh17::type_id::create("mhpmcounterh17", null, get_full_name());
    mhpmcounterh17.configure(this, null, "mhpmcounterh17");
    mhpmcounterh17.build();

    mhpmcounterh18 = reg_mhpmcounterh18::type_id::create("mhpmcounterh18", null, get_full_name());
    mhpmcounterh18.configure(this, null, "mhpmcounterh18");
    mhpmcounterh18.build();

    mhpmcounterh19 = reg_mhpmcounterh19::type_id::create("mhpmcounterh19", null, get_full_name());
    mhpmcounterh19.configure(this, null, "mhpmcounterh19");
    mhpmcounterh19.build();

    mhpmcounterh20 = reg_mhpmcounterh20::type_id::create("mhpmcounterh20", null, get_full_name());
    mhpmcounterh20.configure(this, null, "mhpmcounterh20");
    mhpmcounterh20.build();

    mhpmcounterh21 = reg_mhpmcounterh21::type_id::create("mhpmcounterh21", null, get_full_name());
    mhpmcounterh21.configure(this, null, "mhpmcounterh21");
    mhpmcounterh21.build();

    mhpmcounterh22 = reg_mhpmcounterh22::type_id::create("mhpmcounterh22", null, get_full_name());
    mhpmcounterh22.configure(this, null, "mhpmcounterh22");
    mhpmcounterh22.build();

    mhpmcounterh23 = reg_mhpmcounterh23::type_id::create("mhpmcounterh23", null, get_full_name());
    mhpmcounterh23.configure(this, null, "mhpmcounterh23");
    mhpmcounterh23.build();

    mhpmcounterh24 = reg_mhpmcounterh24::type_id::create("mhpmcounterh24", null, get_full_name());
    mhpmcounterh24.configure(this, null, "mhpmcounterh24");
    mhpmcounterh24.build();

    mhpmcounterh25 = reg_mhpmcounterh25::type_id::create("mhpmcounterh25", null, get_full_name());
    mhpmcounterh25.configure(this, null, "mhpmcounterh25");
    mhpmcounterh25.build();

    mhpmcounterh26 = reg_mhpmcounterh26::type_id::create("mhpmcounterh26", null, get_full_name());
    mhpmcounterh26.configure(this, null, "mhpmcounterh26");
    mhpmcounterh26.build();

    mhpmcounterh27 = reg_mhpmcounterh27::type_id::create("mhpmcounterh27", null, get_full_name());
    mhpmcounterh27.configure(this, null, "mhpmcounterh27");
    mhpmcounterh27.build();

    mhpmcounterh28 = reg_mhpmcounterh28::type_id::create("mhpmcounterh28", null, get_full_name());
    mhpmcounterh28.configure(this, null, "mhpmcounterh28");
    mhpmcounterh28.build();

    mhpmcounterh29 = reg_mhpmcounterh29::type_id::create("mhpmcounterh29", null, get_full_name());
    mhpmcounterh29.configure(this, null, "mhpmcounterh29");
    mhpmcounterh29.build();

    mhpmcounterh30 = reg_mhpmcounterh30::type_id::create("mhpmcounterh30", null, get_full_name());
    mhpmcounterh30.configure(this, null, "mhpmcounterh30");
    mhpmcounterh30.build();

    mhpmcounterh31 = reg_mhpmcounterh31::type_id::create("mhpmcounterh31", null, get_full_name());
    mhpmcounterh31.configure(this, null, "mhpmcounterh31");
    mhpmcounterh31.build();

    mvendorid = reg_mvendorid::type_id::create("mvendorid", null, get_full_name());
    mvendorid.configure(this, null, "mvendorid");
    mvendorid.build();

    marchid = reg_marchid::type_id::create("marchid", null, get_full_name());
    marchid.configure(this, null, "marchid");
    marchid.build();

    mimpid = reg_mimpid::type_id::create("mimpid", null, get_full_name());
    mimpid.configure(this, null, "mimpid");
    mimpid.build();

    mhartid = reg_mhartid::type_id::create("mhartid", null, get_full_name());
    mhartid.configure(this, null, "mhartid");
    mhartid.build();

 
    
    //---------------------------------------
    //Memory map creation and reg map to it
    //---------------------------------------
    default_map = create_map(.name("default_map"), .base_addr(0), .n_bytes(4) , .endian(UVM_LITTLE_ENDIAN));
    default_map.add_reg(mstatus, 'h300, "RW");  
    default_map.add_reg(misa, 'h301, "RW");  
    default_map.add_reg(mie, 'h304, "RW");  
    default_map.add_reg(mtvec, 'h305, "RW");  
    default_map.add_reg(mstatush, 'h310, "RW");  
    default_map.add_reg(mhpmevent3, 'h323, "RW");  
    default_map.add_reg(mhpmevent4, 'h324, "RW");  
    default_map.add_reg(mhpmevent5, 'h325, "RW");  
    default_map.add_reg(mhpmevent6, 'h326, "RW");  
    default_map.add_reg(mhpmevent7, 'h327, "RW");  
    default_map.add_reg(mhpmevent8, 'h328, "RW");  
    default_map.add_reg(mhpmevent9, 'h329, "RW");  
    default_map.add_reg(mhpmevent10, 'h32a, "RW");  
    default_map.add_reg(mhpmevent11, 'h32b, "RW");  
    default_map.add_reg(mhpmevent12, 'h32c, "RW");  
    default_map.add_reg(mhpmevent13, 'h32d, "RW");  
    default_map.add_reg(mhpmevent14, 'h32e, "RW");  
    default_map.add_reg(mhpmevent15, 'h32f, "RW");  
    default_map.add_reg(mhpmevent16, 'h330, "RW");  
    default_map.add_reg(mhpmevent17, 'h331, "RW");  
    default_map.add_reg(mhpmevent18, 'h332, "RW");  
    default_map.add_reg(mhpmevent19, 'h333, "RW");  
    default_map.add_reg(mhpmevent20, 'h334, "RW");  
    default_map.add_reg(mhpmevent21, 'h335, "RW");  
    default_map.add_reg(mhpmevent22, 'h336, "RW");  
    default_map.add_reg(mhpmevent23, 'h337, "RW");  
    default_map.add_reg(mhpmevent24, 'h338, "RW");  
    default_map.add_reg(mhpmevent25, 'h339, "RW");  
    default_map.add_reg(mhpmevent26, 'h33a, "RW");  
    default_map.add_reg(mhpmevent27, 'h33b, "RW");  
    default_map.add_reg(mhpmevent28, 'h33c, "RW");  
    default_map.add_reg(mhpmevent29, 'h33d, "RW");  
    default_map.add_reg(mhpmevent30, 'h33e, "RW");  
    default_map.add_reg(mhpmevent31, 'h33f, "RW");  
    default_map.add_reg(mscratch, 'h340, "RW");  
    default_map.add_reg(mepc, 'h341, "RW");  
    default_map.add_reg(mcause, 'h342, "RW");  
    default_map.add_reg(mtval, 'h343, "RW");  
    default_map.add_reg(mip, 'h344, "RW");  
    default_map.add_reg(pmpcfg0, 'h3a0, "RW");  
    default_map.add_reg(pmpcfg1, 'h3a1, "RW");  
    default_map.add_reg(pmpcfg2, 'h3a2, "RW");  
    default_map.add_reg(pmpcfg3, 'h3a3, "RW");  
    default_map.add_reg(pmpaddr0, 'h3b0, "RW");  
    default_map.add_reg(pmpaddr1, 'h3b1, "RW");  
    default_map.add_reg(pmpaddr2, 'h3b2, "RW");  
    default_map.add_reg(pmpaddr3, 'h3b3, "RW");  
    default_map.add_reg(pmpaddr4, 'h3b4, "RW");  
    default_map.add_reg(pmpaddr5, 'h3b5, "RW");  
    default_map.add_reg(pmpaddr6, 'h3b6, "RW");  
    default_map.add_reg(pmpaddr7, 'h3b7, "RW");  
    default_map.add_reg(pmpaddr8, 'h3b8, "RW");  
    default_map.add_reg(pmpaddr9, 'h3b9, "RW");  
    default_map.add_reg(pmpaddr10, 'h3ba, "RW");  
    default_map.add_reg(pmpaddr11, 'h3bb, "RW");  
    default_map.add_reg(pmpaddr12, 'h3bc, "RW");  
    default_map.add_reg(pmpaddr13, 'h3bd, "RW");  
    default_map.add_reg(pmpaddr14, 'h3be, "RW");  
    default_map.add_reg(pmpaddr15, 'h3bf, "RW");  
    default_map.add_reg(icache, 'h7C0, "RW");  
    default_map.add_reg(mcycle, 'hB00, "RW");  
    default_map.add_reg(minstret, 'hB02, "RW");  
    default_map.add_reg(mcycleh, 'hB80, "RW");  
    default_map.add_reg(minstreth, 'hB82, "RW");  
    default_map.add_reg(mhpmcounter3, 'hb03, "RW");  
    default_map.add_reg(mhpmcounter4, 'hb04, "RW");  
    default_map.add_reg(mhpmcounter5, 'hb05, "RW");  
    default_map.add_reg(mhpmcounter6, 'hb06, "RW");  
    default_map.add_reg(mhpmcounter7, 'hb07, "RW");  
    default_map.add_reg(mhpmcounter8, 'hb08, "RW");  
    default_map.add_reg(mhpmcounter9, 'hb09, "RW");  
    default_map.add_reg(mhpmcounter10, 'hb0a, "RW");  
    default_map.add_reg(mhpmcounter11, 'hb0b, "RW");  
    default_map.add_reg(mhpmcounter12, 'hb0c, "RW");  
    default_map.add_reg(mhpmcounter13, 'hb0d, "RW");  
    default_map.add_reg(mhpmcounter14, 'hb0e, "RW");  
    default_map.add_reg(mhpmcounter15, 'hb0f, "RW");  
    default_map.add_reg(mhpmcounter16, 'hb10, "RW");  
    default_map.add_reg(mhpmcounter17, 'hb11, "RW");  
    default_map.add_reg(mhpmcounter18, 'hb12, "RW");  
    default_map.add_reg(mhpmcounter19, 'hb13, "RW");  
    default_map.add_reg(mhpmcounter20, 'hb14, "RW");  
    default_map.add_reg(mhpmcounter21, 'hb15, "RW");  
    default_map.add_reg(mhpmcounter22, 'hb16, "RW");  
    default_map.add_reg(mhpmcounter23, 'hb17, "RW");  
    default_map.add_reg(mhpmcounter24, 'hb18, "RW");  
    default_map.add_reg(mhpmcounter25, 'hb19, "RW");  
    default_map.add_reg(mhpmcounter26, 'hb1a, "RW");  
    default_map.add_reg(mhpmcounter27, 'hb1b, "RW");  
    default_map.add_reg(mhpmcounter28, 'hb1c, "RW");  
    default_map.add_reg(mhpmcounter29, 'hb1d, "RW");  
    default_map.add_reg(mhpmcounter30, 'hb1e, "RW");  
    default_map.add_reg(mhpmcounter31, 'hb1f, "RW");  
    default_map.add_reg(mhpmcounterh3, 'hb83, "RW");  
    default_map.add_reg(mhpmcounterh4, 'hb84, "RW");  
    default_map.add_reg(mhpmcounterh5, 'hb85, "RW");  
    default_map.add_reg(mhpmcounterh6, 'hb86, "RW");  
    default_map.add_reg(mhpmcounterh7, 'hb87, "RW");  
    default_map.add_reg(mhpmcounterh8, 'hb88, "RW");  
    default_map.add_reg(mhpmcounterh9, 'hb89, "RW");  
    default_map.add_reg(mhpmcounterh10, 'hb8a, "RW");  
    default_map.add_reg(mhpmcounterh11, 'hb8b, "RW");  
    default_map.add_reg(mhpmcounterh12, 'hb8c, "RW");  
    default_map.add_reg(mhpmcounterh13, 'hb8d, "RW");  
    default_map.add_reg(mhpmcounterh14, 'hb8e, "RW");  
    default_map.add_reg(mhpmcounterh15, 'hb8f, "RW");  
    default_map.add_reg(mhpmcounterh16, 'hb90, "RW");  
    default_map.add_reg(mhpmcounterh17, 'hb91, "RW");  
    default_map.add_reg(mhpmcounterh18, 'hb92, "RW");  
    default_map.add_reg(mhpmcounterh19, 'hb93, "RW");  
    default_map.add_reg(mhpmcounterh20, 'hb94, "RW");  
    default_map.add_reg(mhpmcounterh21, 'hb95, "RW");  
    default_map.add_reg(mhpmcounterh22, 'hb96, "RW");  
    default_map.add_reg(mhpmcounterh23, 'hb97, "RW");  
    default_map.add_reg(mhpmcounterh24, 'hb98, "RW");  
    default_map.add_reg(mhpmcounterh25, 'hb99, "RW");  
    default_map.add_reg(mhpmcounterh26, 'hb9a, "RW");  
    default_map.add_reg(mhpmcounterh27, 'hb9b, "RW");  
    default_map.add_reg(mhpmcounterh28, 'hb9c, "RW");  
    default_map.add_reg(mhpmcounterh29, 'hb9d, "RW");  
    default_map.add_reg(mhpmcounterh30, 'hb9e, "RW");  
    default_map.add_reg(mhpmcounterh31, 'hb9f, "RW");   
    default_map.add_reg(mvendorid, 'hF11, "RO");  
    default_map.add_reg(marchid, 'hF12, "RO");  
    default_map.add_reg(mimpid, 'hF13, "RO");  
    default_map.add_reg(mhartid, 'hF14, "RO");  
    //default_map.set_check_on_read(1);
    this.set_coverage(UVM_CVR_ALL);
    this.lock_model();
    reset();
  endfunction
endclass
