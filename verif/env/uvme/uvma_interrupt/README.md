Description of the interrupt agent.  

- The interrupt agent supports mainly 3 modes:  
  1 - The agent sends one interrupt request, then we deassert it.   
  2 - The agent sends several interrupt requests at the same time, with the same size, then we deassert the interrupt requests.   
  3 - The agent sends randomized interrupt requests.   

- The interrupt agent has 2 type of delays in `uvma_interrupt_seq_item.sv`:  
  1 - `irq_delay` is related to the delay between two interrupt request.  
  2 - `irq_time` is related to the time the interrupt request could take.  

- The interrupt agent sends requests asynchronously.

- To enable interrupt requests you should add the option `"+enable_interrupt"`.

- There is no mechanism to clear the interrupt requests (on going).
