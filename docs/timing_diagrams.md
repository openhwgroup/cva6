# Timing Diagrams

## Memory Interface

Basic Memory Request:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P..........'},
  {name: 'data_addr',   wave: 'x..2..x....', data: ['address']},
  {name: 'data_wdata',  wave: 'x..2..x....', data: ['wdata']},
  {name: 'data_req',    wave: '0..1..0....'},
  {name: 'data_gnt',    wave: '0....10....'},
  {name: 'data_rvalid', wave: '0.....1.0..'},
  {name: 'data_rdata',  wave: 'x.....2.x..', data: ['rdata']},
  {name: 'data_we',     wave: 'x..2..x....', data: ['we']},
  {name: 'data_be',     wave: 'x..2..x....', data: ['be']}
]}
</script>

Slow memory response:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P....|.........'},
  {name: 'data_addr',   wave: 'x..2.|....x....', data: ['address']},
  {name: 'data_wdata',  wave: 'x..2.|....x....', data: ['wdata']},
  {name: 'data_req',    wave: '0..1.|....0....'},
  {name: 'data_gnt',    wave: '0....|...10....'},
  {name: 'data_rvalid', wave: '0....|......1.0'},
  {name: 'data_rdata',  wave: 'x....|......2.x', data: ['rdata']},
  {name: 'data_we',     wave: 'x..2.|....x....', data: ['we']},
  {name: 'data_be',     wave: 'x..2.|....x....', data: ['be']}
]}
</script>
Fast back to back memory response:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P........'},
  {name: 'data_addr',   wave: 'x..2345x.', data: ['a1', 'a2', 'a3', 'a4']},
  {name: 'data_wdata',  wave: 'x..2345x.', data: ['w1', 'w2', 'w3', 'w4']},
  {name: 'data_req',    wave: '0..1...0.'},
  {name: 'data_gnt',    wave: '0..1...0.'},
  {name: 'data_rvalid', wave: '0...1...0'},
  {name: 'data_rdata',  wave: 'x...2345x', data: ['r1', 'r2', 'r3', 'r4']},
  {name: 'data_we',     wave: 'x..2345x.', data: ['we1', 'we2', 'we3', 'we4']},
  {name: 'data_be',     wave: 'x..2345x.', data: ['be1', 'be2', 'be3', 'be4']}
]}
</script>

