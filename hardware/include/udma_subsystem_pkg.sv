package udma_subsystem_pkg;

  localparam N_SPI          = 12; 
  localparam N_UART         = 8;
  localparam N_SDIO         = 2;
  localparam N_CAM          = 2;
  localparam N_I2C          = 5;
  localparam N_HYPER        = 1;

  typedef struct packed {
 		logic tx_o;
 	} uart_to_pad_t;
 	typedef struct packed {
 		logic rx_i;
 	} pad_to_uart_t;

	typedef struct packed {
		logic sd0_o;
		logic sd0_oen_o;
		logic sd1_o;
		logic sd1_oen_o;
		logic sd2_o;
		logic sd2_oen_o;
		logic sd3_o;
		logic sd3_oen_o;
		logic csn0_o;
		logic csn1_o;
		logic csn2_o;
		logic csn3_o;
		logic clk_o;
	} qspi_to_pad_t;
	typedef struct packed {
		logic sd0_i;
		logic sd1_i;
		logic sd2_i;
		logic sd3_i;
	} pad_to_qspi_t;

	typedef struct packed {
	   logic sda_o;
	   logic sda_oe_o;
	   logic scl_o;
	   logic scl_oe_o;
	  } i2c_to_pad_t;
	typedef struct packed {
	   logic sda_i;
	   logic scl_i;
	 } pad_to_i2c_t;

  typedef struct packed {
    logic clk_i;
    logic hsync_i;
    logic vsync_i;
		logic data0_i;
		logic data1_i;
		logic data2_i;
		logic data3_i;
		logic data4_i;
		logic data5_i;
		logic data6_i;
		logic data7_i;
  } pad_to_cam_t;

  typedef struct packed {
    logic clk_o;
    logic cmd_o;
    logic cmd_oen_o;
		logic data0_o;
		logic data1_o;
		logic data2_o;
		logic data3_o;
		logic data0_oen_o;
		logic data1_oen_o;
		logic data2_oen_o;
		logic data3_oen_o;
  } sdio_to_pad_t;

  typedef struct packed {
    logic cmd_i;
		logic data0_i;
		logic data1_i;
		logic data2_i;
		logic data3_i;
  } pad_to_sdio_t;

	typedef struct packed {
		logic cs0n_o;
		logic cs1n_o;
		logic ck_o;
		logic ckn_o;
		logic rwds_o;
		logic rwds_oe_o;
		logic resetn_o;
		logic dq0_o;
		logic dq1_o;
		logic dq2_o;
		logic dq3_o;
		logic dq4_o;
		logic dq5_o;
		logic dq6_o;
		logic dq7_o;
		logic dq_oe_o;
	} hyper_to_pad_t;

	typedef struct packed {
		logic rwds_i;
		logic dq0_i;
		logic dq1_i;
		logic dq2_i;
		logic dq3_i;
		logic dq4_i;
		logic dq5_i;
		logic dq6_i;
		logic dq7_i;
	} pad_to_hyper_t;

 	typedef struct packed {
		logic pwm0_o;
		logic pwm1_o;
		logic pwm2_o;
		logic pwm3_o;
		logic pwm4_o;
		logic pwm5_o;
		logic pwm6_o;
		logic pwm7_o;
	} pwm_to_pad_t;

endpackage
   
