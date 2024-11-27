	component oddr_intel is
		port (
			ck      : in  std_logic                    := 'X';             -- export
			din     : in  std_logic_vector(1 downto 0) := (others => 'X'); -- export
			pad_out : out std_logic_vector(0 downto 0)                     -- export
		);
	end component oddr_intel;

	u0 : component oddr_intel
		port map (
			ck      => CONNECTED_TO_ck,      --      ck.export
			din     => CONNECTED_TO_din,     --     din.export
			pad_out => CONNECTED_TO_pad_out  -- pad_out.export
		);

