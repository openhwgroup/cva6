	component cva6_intel_axi_bridge_0 is
		generic (
			USE_PIPELINE              : integer := 1;
			USE_M0_AWID               : integer := 1;
			USE_M0_AWREGION           : integer := 0;
			USE_M0_AWLEN              : integer := 1;
			USE_M0_AWSIZE             : integer := 1;
			USE_M0_AWBURST            : integer := 1;
			USE_M0_AWLOCK             : integer := 1;
			USE_M0_AWCACHE            : integer := 1;
			USE_M0_AWQOS              : integer := 0;
			USE_S0_AWREGION           : integer := 0;
			USE_S0_AWLOCK             : integer := 1;
			USE_S0_AWCACHE            : integer := 1;
			USE_S0_AWQOS              : integer := 0;
			USE_S0_AWPROT             : integer := 1;
			USE_M0_WSTRB              : integer := 1;
			USE_S0_WLAST              : integer := 1;
			USE_M0_BID                : integer := 1;
			USE_M0_BRESP              : integer := 1;
			USE_S0_BRESP              : integer := 1;
			USE_M0_ARID               : integer := 1;
			USE_M0_ARREGION           : integer := 0;
			USE_M0_ARLEN              : integer := 1;
			USE_M0_ARSIZE             : integer := 1;
			USE_M0_ARBURST            : integer := 1;
			USE_M0_ARLOCK             : integer := 1;
			USE_M0_ARCACHE            : integer := 1;
			USE_M0_ARQOS              : integer := 0;
			USE_S0_ARREGION           : integer := 0;
			USE_S0_ARLOCK             : integer := 1;
			USE_S0_ARCACHE            : integer := 1;
			USE_S0_ARQOS              : integer := 0;
			USE_S0_ARPROT             : integer := 1;
			USE_M0_RID                : integer := 1;
			USE_M0_RRESP              : integer := 1;
			USE_M0_RLAST              : integer := 1;
			USE_S0_RRESP              : integer := 1;
			M0_ID_WIDTH               : integer := 8;
			S0_ID_WIDTH               : integer := 8;
			DATA_WIDTH                : integer := 64;
			WRITE_ADDR_USER_WIDTH     : integer := 32;
			READ_ADDR_USER_WIDTH      : integer := 32;
			WRITE_DATA_USER_WIDTH     : integer := 32;
			WRITE_RESP_USER_WIDTH     : integer := 32;
			READ_DATA_USER_WIDTH      : integer := 32;
			ADDR_WIDTH                : integer := 64;
			USE_S0_AWUSER             : integer := 0;
			USE_S0_ARUSER             : integer := 0;
			USE_S0_WUSER              : integer := 0;
			USE_S0_RUSER              : integer := 0;
			USE_S0_BUSER              : integer := 0;
			USE_M0_AWUSER             : integer := 0;
			USE_M0_ARUSER             : integer := 0;
			USE_M0_WUSER              : integer := 0;
			USE_M0_RUSER              : integer := 0;
			USE_M0_BUSER              : integer := 0;
			AXI_VERSION               : string  := "AXI4";
			ACE_LITE_SUPPORT          : integer := 0;
			SYNC_RESET                : integer := 0;
			BACKPRESSURE_DURING_RESET : integer := 0
		);
		port (
			aclk       : in  std_logic                     := 'X';             -- clk
			aresetn    : in  std_logic                     := 'X';             -- reset_n
			s0_awid    : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- awid
			s0_awaddr  : in  std_logic_vector(63 downto 0) := (others => 'X'); -- awaddr
			s0_awlen   : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- awlen
			s0_awsize  : in  std_logic_vector(2 downto 0)  := (others => 'X'); -- awsize
			s0_awburst : in  std_logic_vector(1 downto 0)  := (others => 'X'); -- awburst
			s0_awlock  : in  std_logic_vector(0 downto 0)  := (others => 'X'); -- awlock
			s0_awcache : in  std_logic_vector(3 downto 0)  := (others => 'X'); -- awcache
			s0_awprot  : in  std_logic_vector(2 downto 0)  := (others => 'X'); -- awprot
			s0_awvalid : in  std_logic                     := 'X';             -- awvalid
			s0_awready : out std_logic;                                        -- awready
			s0_wdata   : in  std_logic_vector(63 downto 0) := (others => 'X'); -- wdata
			s0_wstrb   : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- wstrb
			s0_wlast   : in  std_logic                     := 'X';             -- wlast
			s0_wvalid  : in  std_logic                     := 'X';             -- wvalid
			s0_wready  : out std_logic;                                        -- wready
			s0_bid     : out std_logic_vector(7 downto 0);                     -- bid
			s0_bresp   : out std_logic_vector(1 downto 0);                     -- bresp
			s0_bvalid  : out std_logic;                                        -- bvalid
			s0_bready  : in  std_logic                     := 'X';             -- bready
			s0_arid    : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- arid
			s0_araddr  : in  std_logic_vector(63 downto 0) := (others => 'X'); -- araddr
			s0_arlen   : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- arlen
			s0_arsize  : in  std_logic_vector(2 downto 0)  := (others => 'X'); -- arsize
			s0_arburst : in  std_logic_vector(1 downto 0)  := (others => 'X'); -- arburst
			s0_arlock  : in  std_logic_vector(0 downto 0)  := (others => 'X'); -- arlock
			s0_arcache : in  std_logic_vector(3 downto 0)  := (others => 'X'); -- arcache
			s0_arprot  : in  std_logic_vector(2 downto 0)  := (others => 'X'); -- arprot
			s0_arvalid : in  std_logic                     := 'X';             -- arvalid
			s0_arready : out std_logic;                                        -- arready
			s0_rid     : out std_logic_vector(7 downto 0);                     -- rid
			s0_rdata   : out std_logic_vector(63 downto 0);                    -- rdata
			s0_rresp   : out std_logic_vector(1 downto 0);                     -- rresp
			s0_rlast   : out std_logic;                                        -- rlast
			s0_rvalid  : out std_logic;                                        -- rvalid
			s0_rready  : in  std_logic                     := 'X';             -- rready
			m0_awid    : out std_logic_vector(7 downto 0);                     -- awid
			m0_awaddr  : out std_logic_vector(63 downto 0);                    -- awaddr
			m0_awlen   : out std_logic_vector(7 downto 0);                     -- awlen
			m0_awsize  : out std_logic_vector(2 downto 0);                     -- awsize
			m0_awburst : out std_logic_vector(1 downto 0);                     -- awburst
			m0_awlock  : out std_logic_vector(0 downto 0);                     -- awlock
			m0_awcache : out std_logic_vector(3 downto 0);                     -- awcache
			m0_awprot  : out std_logic_vector(2 downto 0);                     -- awprot
			m0_awvalid : out std_logic;                                        -- awvalid
			m0_awready : in  std_logic                     := 'X';             -- awready
			m0_wdata   : out std_logic_vector(63 downto 0);                    -- wdata
			m0_wstrb   : out std_logic_vector(7 downto 0);                     -- wstrb
			m0_wlast   : out std_logic;                                        -- wlast
			m0_wvalid  : out std_logic;                                        -- wvalid
			m0_wready  : in  std_logic                     := 'X';             -- wready
			m0_bid     : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- bid
			m0_bresp   : in  std_logic_vector(1 downto 0)  := (others => 'X'); -- bresp
			m0_bvalid  : in  std_logic                     := 'X';             -- bvalid
			m0_bready  : out std_logic;                                        -- bready
			m0_arid    : out std_logic_vector(7 downto 0);                     -- arid
			m0_araddr  : out std_logic_vector(63 downto 0);                    -- araddr
			m0_arlen   : out std_logic_vector(7 downto 0);                     -- arlen
			m0_arsize  : out std_logic_vector(2 downto 0);                     -- arsize
			m0_arburst : out std_logic_vector(1 downto 0);                     -- arburst
			m0_arlock  : out std_logic_vector(0 downto 0);                     -- arlock
			m0_arcache : out std_logic_vector(3 downto 0);                     -- arcache
			m0_arprot  : out std_logic_vector(2 downto 0);                     -- arprot
			m0_arvalid : out std_logic;                                        -- arvalid
			m0_arready : in  std_logic                     := 'X';             -- arready
			m0_rid     : in  std_logic_vector(7 downto 0)  := (others => 'X'); -- rid
			m0_rdata   : in  std_logic_vector(63 downto 0) := (others => 'X'); -- rdata
			m0_rresp   : in  std_logic_vector(1 downto 0)  := (others => 'X'); -- rresp
			m0_rlast   : in  std_logic                     := 'X';             -- rlast
			m0_rvalid  : in  std_logic                     := 'X';             -- rvalid
			m0_rready  : out std_logic                                         -- rready
		);
	end component cva6_intel_axi_bridge_0;

	u0 : component cva6_intel_axi_bridge_0
		generic map (
			USE_PIPELINE              => INTEGER_VALUE_FOR_USE_PIPELINE,
			USE_M0_AWID               => INTEGER_VALUE_FOR_USE_M0_AWID,
			USE_M0_AWREGION           => INTEGER_VALUE_FOR_USE_M0_AWREGION,
			USE_M0_AWLEN              => INTEGER_VALUE_FOR_USE_M0_AWLEN,
			USE_M0_AWSIZE             => INTEGER_VALUE_FOR_USE_M0_AWSIZE,
			USE_M0_AWBURST            => INTEGER_VALUE_FOR_USE_M0_AWBURST,
			USE_M0_AWLOCK             => INTEGER_VALUE_FOR_USE_M0_AWLOCK,
			USE_M0_AWCACHE            => INTEGER_VALUE_FOR_USE_M0_AWCACHE,
			USE_M0_AWQOS              => INTEGER_VALUE_FOR_USE_M0_AWQOS,
			USE_S0_AWREGION           => INTEGER_VALUE_FOR_USE_S0_AWREGION,
			USE_S0_AWLOCK             => INTEGER_VALUE_FOR_USE_S0_AWLOCK,
			USE_S0_AWCACHE            => INTEGER_VALUE_FOR_USE_S0_AWCACHE,
			USE_S0_AWQOS              => INTEGER_VALUE_FOR_USE_S0_AWQOS,
			USE_S0_AWPROT             => INTEGER_VALUE_FOR_USE_S0_AWPROT,
			USE_M0_WSTRB              => INTEGER_VALUE_FOR_USE_M0_WSTRB,
			USE_S0_WLAST              => INTEGER_VALUE_FOR_USE_S0_WLAST,
			USE_M0_BID                => INTEGER_VALUE_FOR_USE_M0_BID,
			USE_M0_BRESP              => INTEGER_VALUE_FOR_USE_M0_BRESP,
			USE_S0_BRESP              => INTEGER_VALUE_FOR_USE_S0_BRESP,
			USE_M0_ARID               => INTEGER_VALUE_FOR_USE_M0_ARID,
			USE_M0_ARREGION           => INTEGER_VALUE_FOR_USE_M0_ARREGION,
			USE_M0_ARLEN              => INTEGER_VALUE_FOR_USE_M0_ARLEN,
			USE_M0_ARSIZE             => INTEGER_VALUE_FOR_USE_M0_ARSIZE,
			USE_M0_ARBURST            => INTEGER_VALUE_FOR_USE_M0_ARBURST,
			USE_M0_ARLOCK             => INTEGER_VALUE_FOR_USE_M0_ARLOCK,
			USE_M0_ARCACHE            => INTEGER_VALUE_FOR_USE_M0_ARCACHE,
			USE_M0_ARQOS              => INTEGER_VALUE_FOR_USE_M0_ARQOS,
			USE_S0_ARREGION           => INTEGER_VALUE_FOR_USE_S0_ARREGION,
			USE_S0_ARLOCK             => INTEGER_VALUE_FOR_USE_S0_ARLOCK,
			USE_S0_ARCACHE            => INTEGER_VALUE_FOR_USE_S0_ARCACHE,
			USE_S0_ARQOS              => INTEGER_VALUE_FOR_USE_S0_ARQOS,
			USE_S0_ARPROT             => INTEGER_VALUE_FOR_USE_S0_ARPROT,
			USE_M0_RID                => INTEGER_VALUE_FOR_USE_M0_RID,
			USE_M0_RRESP              => INTEGER_VALUE_FOR_USE_M0_RRESP,
			USE_M0_RLAST              => INTEGER_VALUE_FOR_USE_M0_RLAST,
			USE_S0_RRESP              => INTEGER_VALUE_FOR_USE_S0_RRESP,
			M0_ID_WIDTH               => INTEGER_VALUE_FOR_M0_ID_WIDTH,
			S0_ID_WIDTH               => INTEGER_VALUE_FOR_S0_ID_WIDTH,
			DATA_WIDTH                => INTEGER_VALUE_FOR_DATA_WIDTH,
			WRITE_ADDR_USER_WIDTH     => INTEGER_VALUE_FOR_WRITE_ADDR_USER_WIDTH,
			READ_ADDR_USER_WIDTH      => INTEGER_VALUE_FOR_READ_ADDR_USER_WIDTH,
			WRITE_DATA_USER_WIDTH     => INTEGER_VALUE_FOR_WRITE_DATA_USER_WIDTH,
			WRITE_RESP_USER_WIDTH     => INTEGER_VALUE_FOR_WRITE_RESP_USER_WIDTH,
			READ_DATA_USER_WIDTH      => INTEGER_VALUE_FOR_READ_DATA_USER_WIDTH,
			ADDR_WIDTH                => INTEGER_VALUE_FOR_ADDR_WIDTH,
			USE_S0_AWUSER             => INTEGER_VALUE_FOR_USE_S0_AWUSER,
			USE_S0_ARUSER             => INTEGER_VALUE_FOR_USE_S0_ARUSER,
			USE_S0_WUSER              => INTEGER_VALUE_FOR_USE_S0_WUSER,
			USE_S0_RUSER              => INTEGER_VALUE_FOR_USE_S0_RUSER,
			USE_S0_BUSER              => INTEGER_VALUE_FOR_USE_S0_BUSER,
			USE_M0_AWUSER             => INTEGER_VALUE_FOR_USE_M0_AWUSER,
			USE_M0_ARUSER             => INTEGER_VALUE_FOR_USE_M0_ARUSER,
			USE_M0_WUSER              => INTEGER_VALUE_FOR_USE_M0_WUSER,
			USE_M0_RUSER              => INTEGER_VALUE_FOR_USE_M0_RUSER,
			USE_M0_BUSER              => INTEGER_VALUE_FOR_USE_M0_BUSER,
			AXI_VERSION               => STRING_VALUE_FOR_AXI_VERSION,
			ACE_LITE_SUPPORT          => INTEGER_VALUE_FOR_ACE_LITE_SUPPORT,
			SYNC_RESET                => INTEGER_VALUE_FOR_SYNC_RESET,
			BACKPRESSURE_DURING_RESET => INTEGER_VALUE_FOR_BACKPRESSURE_DURING_RESET
		)
		port map (
			aclk       => CONNECTED_TO_aclk,       --       clk.clk
			aresetn    => CONNECTED_TO_aresetn,    -- clk_reset.reset_n
			s0_awid    => CONNECTED_TO_s0_awid,    --        s0.awid
			s0_awaddr  => CONNECTED_TO_s0_awaddr,  --          .awaddr
			s0_awlen   => CONNECTED_TO_s0_awlen,   --          .awlen
			s0_awsize  => CONNECTED_TO_s0_awsize,  --          .awsize
			s0_awburst => CONNECTED_TO_s0_awburst, --          .awburst
			s0_awlock  => CONNECTED_TO_s0_awlock,  --          .awlock
			s0_awcache => CONNECTED_TO_s0_awcache, --          .awcache
			s0_awprot  => CONNECTED_TO_s0_awprot,  --          .awprot
			s0_awvalid => CONNECTED_TO_s0_awvalid, --          .awvalid
			s0_awready => CONNECTED_TO_s0_awready, --          .awready
			s0_wdata   => CONNECTED_TO_s0_wdata,   --          .wdata
			s0_wstrb   => CONNECTED_TO_s0_wstrb,   --          .wstrb
			s0_wlast   => CONNECTED_TO_s0_wlast,   --          .wlast
			s0_wvalid  => CONNECTED_TO_s0_wvalid,  --          .wvalid
			s0_wready  => CONNECTED_TO_s0_wready,  --          .wready
			s0_bid     => CONNECTED_TO_s0_bid,     --          .bid
			s0_bresp   => CONNECTED_TO_s0_bresp,   --          .bresp
			s0_bvalid  => CONNECTED_TO_s0_bvalid,  --          .bvalid
			s0_bready  => CONNECTED_TO_s0_bready,  --          .bready
			s0_arid    => CONNECTED_TO_s0_arid,    --          .arid
			s0_araddr  => CONNECTED_TO_s0_araddr,  --          .araddr
			s0_arlen   => CONNECTED_TO_s0_arlen,   --          .arlen
			s0_arsize  => CONNECTED_TO_s0_arsize,  --          .arsize
			s0_arburst => CONNECTED_TO_s0_arburst, --          .arburst
			s0_arlock  => CONNECTED_TO_s0_arlock,  --          .arlock
			s0_arcache => CONNECTED_TO_s0_arcache, --          .arcache
			s0_arprot  => CONNECTED_TO_s0_arprot,  --          .arprot
			s0_arvalid => CONNECTED_TO_s0_arvalid, --          .arvalid
			s0_arready => CONNECTED_TO_s0_arready, --          .arready
			s0_rid     => CONNECTED_TO_s0_rid,     --          .rid
			s0_rdata   => CONNECTED_TO_s0_rdata,   --          .rdata
			s0_rresp   => CONNECTED_TO_s0_rresp,   --          .rresp
			s0_rlast   => CONNECTED_TO_s0_rlast,   --          .rlast
			s0_rvalid  => CONNECTED_TO_s0_rvalid,  --          .rvalid
			s0_rready  => CONNECTED_TO_s0_rready,  --          .rready
			m0_awid    => CONNECTED_TO_m0_awid,    --        m0.awid
			m0_awaddr  => CONNECTED_TO_m0_awaddr,  --          .awaddr
			m0_awlen   => CONNECTED_TO_m0_awlen,   --          .awlen
			m0_awsize  => CONNECTED_TO_m0_awsize,  --          .awsize
			m0_awburst => CONNECTED_TO_m0_awburst, --          .awburst
			m0_awlock  => CONNECTED_TO_m0_awlock,  --          .awlock
			m0_awcache => CONNECTED_TO_m0_awcache, --          .awcache
			m0_awprot  => CONNECTED_TO_m0_awprot,  --          .awprot
			m0_awvalid => CONNECTED_TO_m0_awvalid, --          .awvalid
			m0_awready => CONNECTED_TO_m0_awready, --          .awready
			m0_wdata   => CONNECTED_TO_m0_wdata,   --          .wdata
			m0_wstrb   => CONNECTED_TO_m0_wstrb,   --          .wstrb
			m0_wlast   => CONNECTED_TO_m0_wlast,   --          .wlast
			m0_wvalid  => CONNECTED_TO_m0_wvalid,  --          .wvalid
			m0_wready  => CONNECTED_TO_m0_wready,  --          .wready
			m0_bid     => CONNECTED_TO_m0_bid,     --          .bid
			m0_bresp   => CONNECTED_TO_m0_bresp,   --          .bresp
			m0_bvalid  => CONNECTED_TO_m0_bvalid,  --          .bvalid
			m0_bready  => CONNECTED_TO_m0_bready,  --          .bready
			m0_arid    => CONNECTED_TO_m0_arid,    --          .arid
			m0_araddr  => CONNECTED_TO_m0_araddr,  --          .araddr
			m0_arlen   => CONNECTED_TO_m0_arlen,   --          .arlen
			m0_arsize  => CONNECTED_TO_m0_arsize,  --          .arsize
			m0_arburst => CONNECTED_TO_m0_arburst, --          .arburst
			m0_arlock  => CONNECTED_TO_m0_arlock,  --          .arlock
			m0_arcache => CONNECTED_TO_m0_arcache, --          .arcache
			m0_arprot  => CONNECTED_TO_m0_arprot,  --          .arprot
			m0_arvalid => CONNECTED_TO_m0_arvalid, --          .arvalid
			m0_arready => CONNECTED_TO_m0_arready, --          .arready
			m0_rid     => CONNECTED_TO_m0_rid,     --          .rid
			m0_rdata   => CONNECTED_TO_m0_rdata,   --          .rdata
			m0_rresp   => CONNECTED_TO_m0_rresp,   --          .rresp
			m0_rlast   => CONNECTED_TO_m0_rlast,   --          .rlast
			m0_rvalid  => CONNECTED_TO_m0_rvalid,  --          .rvalid
			m0_rready  => CONNECTED_TO_m0_rready   --          .rready
		);

