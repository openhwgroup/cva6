/*
* Copyright 2019 ETH Zürich and University of Bologna
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

.section .vectors, "ax"
.option norvc
.global vector_table

vector_table:
	j u_sw_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_software_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_timer_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_external_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_fast0_irq_handler
	j m_fast1_irq_handler
	j m_fast2_irq_handler
	j m_fast3_irq_handler
	j m_fast4_irq_handler
	j m_fast5_irq_handler
	j m_fast6_irq_handler
	j m_fast7_irq_handler
	j m_fast8_irq_handler
	j m_fast9_irq_handler
	j m_fast10_irq_handler
	j m_fast11_irq_handler
	j m_fast12_irq_handler
	j m_fast13_irq_handler
	j m_fast14_irq_handler
	j m_fast15_irq_handler

