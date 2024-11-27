	component cva6_intel_jtag_uart_0 is
		port (
			clk            : in  std_logic                     := 'X';             -- clk
			rst_n          : in  std_logic                     := 'X';             -- reset_n
			av_chipselect  : in  std_logic                     := 'X';             -- chipselect
			av_address     : in  std_logic                     := 'X';             -- address
			av_read_n      : in  std_logic                     := 'X';             -- read_n
			av_readdata    : out std_logic_vector(31 downto 0);                    -- readdata
			av_write_n     : in  std_logic                     := 'X';             -- write_n
			av_writedata   : in  std_logic_vector(31 downto 0) := (others => 'X'); -- writedata
			av_waitrequest : out std_logic;                                        -- waitrequest
			av_irq         : out std_logic                                         -- irq
		);
	end component cva6_intel_jtag_uart_0;

	u0 : component cva6_intel_jtag_uart_0
		port map (
			clk            => CONNECTED_TO_clk,            --               clk.clk
			rst_n          => CONNECTED_TO_rst_n,          --             reset.reset_n
			av_chipselect  => CONNECTED_TO_av_chipselect,  -- avalon_jtag_slave.chipselect
			av_address     => CONNECTED_TO_av_address,     --                  .address
			av_read_n      => CONNECTED_TO_av_read_n,      --                  .read_n
			av_readdata    => CONNECTED_TO_av_readdata,    --                  .readdata
			av_write_n     => CONNECTED_TO_av_write_n,     --                  .write_n
			av_writedata   => CONNECTED_TO_av_writedata,   --                  .writedata
			av_waitrequest => CONNECTED_TO_av_waitrequest, --                  .waitrequest
			av_irq         => CONNECTED_TO_av_irq          --               irq.irq
		);

