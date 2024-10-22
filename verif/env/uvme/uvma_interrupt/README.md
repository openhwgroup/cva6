#Interrupt Agent documentation

<!---
Copyright 2024 Thales DIS SAS

Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
You may obtain a copy of the License at https://solderpad.org/licenses/

Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

-->

## Contents

[1- Introduction](#introduction)

[2- Interrupt Agent architecture](#interrupt-agent-architecture)

[3- Supported features](#supported-features)

[4- Agent configuration Fields](#_Configuration_Fields)

[5- TestBench Integration](#testbench-integration)

[6- Sequences](#sequence)

[7- Checks](#checks)

[9- Packages dependencies](#packages-dependencies)

## Introduction

This document describes the interrupt agent that plays as a interrupt controler
for the CV32A65X, the agent is based on the following protocol:
<https://github.com/openhwgroup/cva6/blob/master/verif/docs/Protocols/interrupt-verification.adoc>

## Interrupt Agent architecture

![](image.png)

*Fig-1: Interrupt agent architecture*

The Interrupt agent provides following components:

-   uvma_interrupt_agent_c: UVM Agent

-   uvma_interrupt_mon_c: Agent monitor, collects and broadcast transactions to
    the coverage model each time the interrupt interface changes.

-   uvma_interrupt_base_seq_c: Base sequence, instantiate agent configuration & context,
    and connect it whit the sequencer configue & context.

-   uvma_interrupt_seq_c: Generates interrupt requests & clear them 
    based on the clear protocol decribe in link above.

-   uvma_interrupt_seq_item_c: Have main items of an interrupt transaction,
    `interuupt_vector, `interrupt_channel_mask and interrupt delays.

-   uvma_interrupt_sqr_c: Sequencer, receives requests from
    the sequence and send it to the driver.

-   uvma_interrupt_drv_c: drive the vif with the requests received from
    sequencer.

-   uvma_interrupt_cntxt_c: Agent context, instantiate VIF uma_interrupt_intf and
    memory uvml_mem. VIF and Memory are accessible in all components
    through context.

-   uvma_interrupt_cfg_c: Agent configuration, all available configuration
    fields are described in Configuration Fields.

## Supported features

features are:

-   **Asynchronous request::** the agent support Asynchronously interrupts requests.

-   **No channel Depandecy:** there's no dependecy between the interrupt channels,
    every one is managed independently.

-   **Channel delay:** provide delay after setting the interrupt request,
    also after clear it.

-   **Randomize channel:** full randomization of setting interrupt request.

-   **Timeout:** the agent is triggering a `UVM_FATAL after a number of
    clock cycle if it failed to clear the interrupt request.

## Agent configuration Fields

-   **is_active**: Switch the agent mode to active. The agent support
    only UVM_ACTIVE mode (can't be in passive mode).

-   **trn_log_enabled**: Enabling interrupt transaction logger when 1.

-   **enable_interrupt:** Enabling sending interrupt request when 1.

-   **interrupt_plusarg_valid:** Enabling interrupts from commande line request when 1.

-   **num_irq_supported**: Represent the number of interrupt channels supported.

-   **irq_addr**: Represent the memory address used by the interrupt
    clear mechanism.

-   **enable_clear_irq**: Enabling the interrupt clear mechanism when 1.

-   **irq_timeout**: Represent the number of clock cyle before the agent
    trigger a `UVM_FATAL timeout.

## TestBench Integration

In the sv testbench instantiate the VIF and connect it to the DUT
interface:

   `uvma_interrupt_if            interrupt_vif(
                                         .clk(clknrst_if.clk),
                                         .reset_n(clknrst_if.reset_n)
                                );`

//DUT connection

    `.irq_i                ( {1'b0, irq_i[0]}             )`
    `.ipi_i                ( 1'b0                         )`
    `.time_irq_i           ( irq_i[1]                     )`

Then set the VIF to agent instantiation in env:

     `uvm_config_db#(virtual uvma_interrupt_if)::set(.cntxt(null), .inst_name("*"), .field_name("interrupt_vif"),  .value(interrupt_vif));`

In env instantiate and create the Interrupt agent:

   `uvma_interrupt_agent_c       interrupt_agent;
`
   `interrupt_agent     = uvma_interrupt_agent_c::type_id::create("interrupt_agent",this);`

Instantiate, create and set the config to the agent:

   `uvma_interrupt_cfg_c        interrupt_cfg;`
   
   `interrupt_cfg      = uvma_interrupt_cfg_c::type_id::create("interrupt_cfg");`

   `uvm_config_db#(uvma_interrupt_cfg_c)::set(this, "*interrupt_agent", "cfg",cfg.interrupt_cfg);`

## Sequences

This agent provides only one sequence:

1.  Set/Clear sequence: this sequence set interrupt request also clear it
    based on a protocol.

## Checks

No checks for now.

## Packages dependencies

This agent is dependent on the following UVM packages:

-   uvm_pkg

-   uvml_trn_pkg

-   uvml_logs_pkg

-   uvml_mem_pkg
