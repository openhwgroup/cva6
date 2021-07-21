
import "DPI-C" initialize_simulator = function void handcar_initialize_simulator(input string options);
import "DPI-C" step_simulator = function int handcar_step_simulator(input int target_id, input int num_steps, input int stx_failed);

module uvmt_cv32e40x_rvvi_handcar();

  RVVI_control control_if();
  RVVI_state   state_if();

  initial handcar_initialize_simulator("-p1 -hartids=0");

endmodule : uvmt_cv32e40x_rvvi_handcar
