	component iobuf is
		port (
			dout   : out   std_logic_vector(0 downto 0);                    -- export
			din    : in    std_logic_vector(0 downto 0) := (others => 'X'); -- export
			oe     : in    std_logic_vector(0 downto 0) := (others => 'X'); -- export
			pad_io : inout std_logic_vector(0 downto 0) := (others => 'X')  -- export
		);
	end component iobuf;

	u0 : component iobuf
		port map (
			dout   => CONNECTED_TO_dout,   --   dout.export
			din    => CONNECTED_TO_din,    --    din.export
			oe     => CONNECTED_TO_oe,     --     oe.export
			pad_io => CONNECTED_TO_pad_io  -- pad_io.export
		);

