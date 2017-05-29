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

Slow D$ response:
<script type="WaveDrom">
{signal: [
  {name: 'clk',         wave: 'P....|.........'},
  {name: 'data_index',  wave: 'x..2.|....x....', data: ['index']},
  {name: 'data_tag',    wave: 'x....|....2..x.', data: ['tag']},
  {name: 'data_wdata',  wave: 'x..2.|....x....', data: ['wdata']},
  {name: 'data_req',    wave: '0..1.|....0....'},
  {name: 'data_gnt',    wave: '0....|...10....'},
  {name: 'tag_valid',   wave: '0....|....1..0.'},
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

<!-- ## LSU

- **Multicycle D$ access**: Making the path to the cache a multicycle path. This will give enough headroom for the memories to propagate their output.

<script type="WaveDrom">
{signal: [
  {name: 'clk',                 wave: 'P.................'},
  {name: 'lsu_clk',             wave: 'HlHlHlHlHlHlHlHlHl'},
  {name: 'operator',            wave: 'x.2.3.4.x.5.x.....', data: ['ST', 'LD', 'ST', 'LD']},
  {name: 'vaddr',               wave: 'x.2.3.4.x.5.x.....', data: ['vaddr1', 'vaddr2', 'vaddr3', 'vaddr4']},
  {name: 'valid',               wave: '0.1.....0.1.0.....'},
  {name: 'ready',               wave: '1.....0...1.0...1.'},
  {name: 'paddr',               wave: 'x.2.3.x.4.x.5.x...', data: ['paddr1', 'paddr3', 'paddr3', 'paddr4']},
  {name: 'translation_valid',   wave: '0.1...0.1.0.1.0...'},
  {name: 'data_addr',           wave: 'x.2.3.x.4...5.x...', data: ['paddr1', 'paddr3', 'paddr3', 'paddr4']},
  {name: 'data_wdata',          wave: 'x.2.x...4...x.....', data: ['wdata1', 'wdata2', 'wdata3']},
  {name: 'data_req',            wave: '0.1...0.1.....0...'},
  {name: 'data_gnt',            wave: '0.1...0...1...0...'},
  {name: 'data_rvalid',         wave: '0...1...0...1.0.1.'},
  {name: 'data_rdata',          wave: 'x.....3.x.......5.', data: ['rdata2', 'rdata4']},
  {name: 'data_we',             wave: '0.1.0...1...0.....'},
  {name: 'data_be',             wave: 'x.2.3.x.4...5.x...', data: ['be1', 'be2', 'be3', 'be4']}
]}
</script>
- **Extra MMU stage**: Splitting the path after address generation. With the headroom gained we could deskew the ld/st path again.
<script type="WaveDrom">
{signal: [
  {name: 'clk',                 wave: 'P.............'},
  {name: 'operator',            wave: 'x.234x.5x.....', data: ['ST', 'LD', 'ST', 'LD']},
  {name: 'vaddr',               wave: 'x.234x.5x.....', data: ['va1', 'va2', 'va3', 'va4']},
  {name: 'valid',               wave: '0.1..0.10.....'},
  {name: 'ready',               wave: '1....0.10.1...'},
  {name: 'paddr',               wave: 'x..23x.4x.5x..', data: ['pa1', 'pa3', 'pa3', 'pa4']},
  {name: 'translation_valid',   wave: '0..1.0.10.10..'},
  {name: 'data_addr',           wave: 'x..23x.4x.5x..', data: ['pa1', 'pa3', 'pa3', 'pa4']},
  {name: 'data_wdata',          wave: 'x..2x..4x.....', data: ['wd1', 'wd2', 'wd3']},
  {name: 'data_req',            wave: '0..1.0.10.....'},
  {name: 'data_gnt',            wave: '0..1.0.10.10..'},
  {name: 'data_rvalid',         wave: '0...1.0.10..10'},
  {name: 'data_rdata',          wave: 'x....3x.....5x', data: ['rd2', 'rd4']},
  {name: 'data_we',             wave: '0..10..10.....'},
  {name: 'data_be',             wave: 'x..23x.4x.5x..', data: ['be1', 'be2', 'be3', 'be4']}
]}
</script>
- Making the D$ **virtually indexed and physically tagged**. This will hide the latency of address translation.
<script type="WaveDrom">
{signal: [
  {name: 'clk',                 wave: 'P.............'},
  {name: 'operator',            wave: 'x.234x.5x.....', data: ['ST', 'LD', 'ST', 'LD']},
  {name: 'vaddr',               wave: 'x.234x.5x.....', data: ['va1', 'va2', 'va3', 'va4']},
  {name: 'valid',               wave: '0.1..0.10.....'},
  {name: 'ready',               wave: '1....0.10.1...'},
  {name: 'paddr',               wave: 'x..23x.4x.5x..', data: ['pa1', 'pa3', 'pa3', 'pa4']},
  {name: 'translation_valid',   wave: '0..1.0.10.10..'},
  {name: 'data_addr',           wave: 'x..23x.4x.5x..', data: ['pa1', 'pa3', 'pa3', 'pa4']},
  {name: 'data_wdata',          wave: 'x..2x..4x.....', data: ['wd1', 'wd2', 'wd3']},
  {name: 'data_req',            wave: '0.1.0..10.....'},
  {name: 'data_gnt',            wave: '0.1.0..10.10..'},
  {name: 'data_rvalid',         wave: '0..1.0..10.10.'},
  {name: 'data_rdata',          wave: 'x...3x.....5x.', data: ['rd2', 'rd4']},
  {name: 'data_we',             wave: '0..10..10.....'},
  {name: 'data_be',             wave: 'x..23x.4x.5x..', data: ['be1', 'be2', 'be3', 'be4']}
]}
</script> -->

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