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
	j sw_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j software_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j timer_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j external_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j fast0_irq_handler
	j fast1_irq_handler
	j fast2_irq_handler
	j fast3_irq_handler
	j fast4_irq_handler
	j fast5_irq_handler
	j fast6_irq_handler
	j fast7_irq_handler
	j fast8_irq_handler
	j fast9_irq_handler
	j fast10_irq_handler
	j fast11_irq_handler
	j fast12_irq_handler
	j fast13_irq_handler
	j fast14_irq_handler
	j fast15_irq_handler

