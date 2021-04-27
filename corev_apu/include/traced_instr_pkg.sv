// See LICENSE.Berkeley for license details.

// Author: Abraham Gonzalez, UC Berkeley
// Date: 24.02.2020
// Description: Traced Instruction and Port (using in Rocket Chip based systems)

package traced_instr_pkg;

  typedef struct packed {
      logic clock;
      logic reset;
      logic valid;
      logic [63:0] iaddr;
      logic [31:0] insn;
      logic [1:0] priv;
      logic exception;
      logic interrupt;
      logic [63:0] cause;
      logic [63:0] tval;
  } traced_instr_t;

  typedef traced_instr_t [ariane_pkg::NR_COMMIT_PORTS-1:0] trace_port_t;

endpackage
