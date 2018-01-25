# Timing Diagrams

## D$ Interface

Basic D$ Memory Request:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P..........'},
  {name: 'data_index',  wave: 'x..2..x....', data: ['index']},
  {name: 'data_tag',    wave: 'x.....2x...', data: ['tag']},
  {name: 'data_wdata',  wave: 'x..2..x....', data: ['wdata']},
  {name: 'data_req',    wave: '0..1..0....'},
  {name: 'data_gnt',    wave: '0....10....'},
  {name: 'tag_valid',   wave: '0.....10...'},
  {name: 'kill_req',    wave: '0..........'},
  {name: 'data_rvalid', wave: '0.....10...'},
  {name: 'data_rdata',  wave: 'x.....2x...', data: ['rdata']},
  {name: 'data_we',     wave: 'x..2..x....', data: ['we']},
  {name: 'data_be',     wave: 'x..2..x....', data: ['be']}
]}
</script>

D$ Miss followed by another request (a hit in that case):
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P.....|.........'},
  {name: 'data_index',  wave: 'x.234.|....x....', data: ['index', 'index', 'index']},
  {name: 'data_tag',    wave: 'x..23x|....4x...', data: ['tag', 'tag', 'tag']},
  {name: 'data_wdata',  wave: 'x.234.|....x....', data: ['data', 'data', 'data']},
  {name: 'data_req',    wave: '0.1...|....0....'},
  {name: 'data_gnt',    wave: '0.1.0.|...10....'},
  {name: 'tag_valid',   wave: '0..1.0|0...10...'},
  {name: 'kill_req',    wave: '0.....|.........'},
  {name: 'data_rvalid', wave: '0.....|..1..0...'},
  {name: 'data_rdata',  wave: 'x.....|..234x...', data: ['rdata', 'rdata', 'rdata']},
  {name: 'data_we',     wave: 'x.234.|....x....', data: ['we', 'we', 'we']},
  {name: 'data_be',     wave: 'x.234.|....x....', data: ['be', 'be', 'be']}
]}
</script>

Slow D$ response:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P....|.........'},
  {name: 'data_index',  wave: 'x..2.|....x....', data: ['index']},
  {name: 'data_tag',    wave: 'x....|....2x...', data: ['tag']},
  {name: 'data_wdata',  wave: 'x..2.|....x....', data: ['wdata']},
  {name: 'data_req',    wave: '0..1.|....0....'},
  {name: 'data_gnt',    wave: '0....|...10....'},
  {name: 'tag_valid',   wave: '0....|....10...'},
  {name: 'kill_req',    wave: '0....|.........'},
  {name: 'data_rvalid', wave: '0....|......10.'},
  {name: 'data_rdata',  wave: 'x....|......2x.', data: ['rdata']},
  {name: 'data_we',     wave: 'x..2.|....x....', data: ['we']},
  {name: 'data_be',     wave: 'x..2.|....x....', data: ['be']}
]}
</script>

Fast back to back D$ response:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P........'},
  {name: 'data_index',  wave: 'x..2345x.', data: ['a1', 'a2', 'a3', 'a4']},
  {name: 'data_tag',    wave: 'x...2345x', data: ['a1', 'a2', 'a3', 'a4']},
  {name: 'data_wdata',  wave: 'x..2345x.', data: ['w1', 'w2', 'w3', 'w4']},
  {name: 'data_req',    wave: '0..1...0.'},
  {name: 'data_gnt',    wave: '0..1...0.'},
  {name: 'tag_valid',   wave: '0...1...0'},
  {name: 'kill_req',    wave: '0........'},
  {name: 'data_rvalid', wave: '0...1...0'},
  {name: 'data_rdata',  wave: 'x...2345x', data: ['r1', 'r2', 'r3', 'r4']},
  {name: 'data_we',     wave: 'x..2345x.', data: ['we1', 'we2', 'we3', 'we4']},
  {name: 'data_be',     wave: 'x..2345x.', data: ['be1', 'be2', 'be3', 'be4']}
]}
</script>

Aborted D$ request (with a new back to back request):
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P..........'},
  {name: 'data_index',  wave: 'x..2..3x...', data: ['index', 'index']},
  {name: 'data_tag',    wave: 'x......3x..', data: ['tag']},
  {name: 'data_wdata',  wave: 'x..2..x....', data: ['wdata']},
  {name: 'data_req',    wave: '0..1...0...'},
  {name: 'data_gnt',    wave: '0....1.0...'},
  {name: 'tag_valid',   wave: '0.....1.0..'},
  {name: 'kill_req',    wave: '0.....10...'},
  {name: 'data_rvalid', wave: '0.....1.0..'},
  {name: 'data_rdata',  wave: 'x......3x..', data: ['rdata']},
  {name: 'data_we',     wave: 'x..2..3x...', data: ['we', 'we']},
  {name: 'data_be',     wave: 'x..2..3x...', data: ['be', 'be']}
]}
</script>

## Functional Unit
<script type="WaveDrom">
{signal: [
  {name: 'clk',                 wave: 'P..........'},
  {name: 'operator_i',          wave: 'x.2x34x.5x.', data: ['op1', 'op2', 'op3', 'op4']},
  {name: 'operand_a_i',         wave: 'x.2x34x.5x.', data: ['a1', 'a2', 'a3', 'a4']},
  {name: 'operand_b_i',         wave: 'x.2x34x.5x.', data: ['b1', 'b2', 'b3', 'b4']},
  {name: 'trans_id_i',          wave: 'x.2x34x.5x.', data: ['t1', 't2', 't3', 't4']},
  {name: 'fu_ready_o',          wave: '0..1..0.1..'},
  {name: 'fu_valid_i',          wave: '0.101.0.10.'},
  {name: 'fu_valid_o',          wave: '0..1.0.1.0.', data: ['pa1', 'pa3', 'pa3', 'pa4']},
  {name: 'fu_trans_id_o',       wave: 'x..23x.45x.', data: ['t1', 't2', 't3', 't4']},
  {name: 'fu_result_o',         wave: 'x..23x.45x.', data: ['r1', 'r2', 'r3', 'r4']},
]}
</script>
# Pipeline Diagram

## LSU

![Ariane Block Diagram](fig/ld_pipeline_diagram.svg)
