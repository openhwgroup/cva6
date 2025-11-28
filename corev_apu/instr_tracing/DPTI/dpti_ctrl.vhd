----------------------------------------------------------------------------------
-- Company: Digilent Inc.
-- Engineer: 
-- 
-- Create Date:    16:16:24 10/26/2011 
-- Design Name: 
-- Module Name:    dpti_ctrl - Behavioral 
-- Project Name: 
-- Target Devices: 
-- Tool versions: 
-- Description: This module implements a synchronous DPTI interface. It includes 
--     two local FIFOs that allow the data to be moved from the DPTI clock domain
--     to another clock domain in the FPGA.
--
-- Dependencies: 
--
-- Revision: 
-- Revision 0.01 - File Created
-- Additional Comments: 
--	5/30/2016(sjb) -- Prepared for public release
----------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

-- Uncomment the following library declaration if using
-- arithmetic functions with Signed or Unsigned values
--use IEEE.NUMERIC_STD.ALL;

-- Uncomment the following library declaration if instantiating
-- any Xilinx primitives in this code.
library UNISIM;
use UNISIM.VComponents.all;

Library UNIMACRO;
use UNIMACRO.vcomponents.all;

entity dpti_ctrl is
    Port ( 
    --User Write FIFO signals
           wr_clk    : in std_logic;
           wr_en     : in std_logic;
           wr_full   : out std_logic;
           wr_afull  : out std_logic;
           wr_err    : out std_logic;
           wr_count  : out std_logic_vector(11 downto 0);
           wr_di     : in std_logic_vector(7 downto 0);
    
    --User Read FIFO signals
          rd_clk    : in std_logic;
          rd_en     : in std_logic;
          rd_empty  : out std_logic;
          rd_aempty : out std_logic;
          rd_err    : out std_logic;
          rd_count  : out std_logic_vector(11 downto 0);
          rd_do     : out std_logic_vector(7 downto 0);
          
    --misc. signals
          rst   : in std_logic;  --Asynchronously resets the entire component. Must be held high for at least 100ns, or 6 clock cycles of the slowest fifo clock if that is longer
          
    --DPTI Port signals
           prog_clko    : in  STD_LOGIC;
           prog_rxen      : in  STD_LOGIC;
           prog_txen      : in  STD_LOGIC;
           prog_spien   : in  STD_LOGIC; --called jtagen on some platforms
           prog_rdn       : out  STD_LOGIC;
           prog_wrn       : out  STD_LOGIC;
           prog_oen       : out  STD_LOGIC;
           prog_siwun     : out STD_LOGIC;
           prog_d      : inout  STD_LOGIC_VECTOR (7 downto 0));
end dpti_ctrl;

architecture Behavioral of dpti_ctrl is





-------------------------------------------------------------------------------
-- Component Declarations
-------------------------------------------------------------------------------

component xlnx_dpti_clk is
port
 (
  CLK_IN1           : in     std_logic;
  CLK_OUT1          : out    std_logic;
  CLK_OUT2          : out    std_logic;
  LOCKED            : out    std_logic
 );
end component;

-------------------------------------------------------------------------------
-- Local Type Declarations
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Constant Declarations
-------------------------------------------------------------------------------

-- The following constants define state codes for the Synchronous PTI port
-- state machine. The high order bits of the state number provide a unique
-- state identifier for each state. The low order bits are the state machine
-- outputs for that state. This type of state machine implementation uses no
-- combinational logic to generate the outputs, which should result in glitch
-- free outputs. 


constant    stPtiRdy    : std_logic_vector(6 downto 0):= "0" & "00" & "1111";
constant    stPtiInOut0 : std_logic_vector(6 downto 0):= "1" & "00" & "1111";
constant    stPtiInOut1 : std_logic_vector(6 downto 0):= "1" & "00" & "1011";
constant    stPtiInOut2 : std_logic_vector(6 downto 0):= "1" & "01" & "1010";
constant    stPtiInOut3 : std_logic_vector(6 downto 0):= "1" & "10" & "0101";

-------------------------------------------------------------------------------
-- Signal Declarations
-------------------------------------------------------------------------------

signal  stPtiCur    : std_logic_vector(6 downto 0) := stPtiRdy;
signal  stPtiNext   : std_logic_vector(6 downto 0);

signal  clkPti  : std_logic;
signal  clkIOB : std_logic;
signal  locked : std_logic;

--user fifo signals
signal  usrWrClk  : std_logic;
signal  usrWrEn  : std_logic;
signal  usrFull  : std_logic;
signal  usrAFull  : std_logic;
signal  usrWrErr  : std_logic;
signal  usrRdClk  : std_logic;
signal  usrRdEn  : std_logic;
signal  usrEmpty  : std_logic;
signal  usrAEmpty  : std_logic;
signal  usrRdErr  : std_logic;
signal  usrRdCnt  : std_logic_vector(11 downto 0);
signal  usrDO  : std_logic_vector(7 downto 0);
signal  usrWrCnt  : std_logic_vector(11 downto 0);
signal  usrDI  : std_logic_vector(7 downto 0);

-- Internal control signals
signal ctlRd    : std_logic;
signal ctlWr    : std_logic;
signal ctlOe    : std_logic;
signal ctlDir   : std_logic;

signal ctlRxf   : std_logic;
signal ctlTxe   : std_logic;
signal ctlRst   : std_logic;

signal ctlFull  : std_logic;
signal ctlAFull : std_logic;
signal ctlEmpty : std_logic;
signal ctlFwr   : std_logic;
signal ctlFrd   : std_logic;

signal  dummyWrCnt  : std_logic_vector(11 downto 0);
signal  dummyRdCnt  : std_logic_vector(11 downto 0);

signal busPtiTris   : std_logic;
signal busPtiOut    : std_logic_vector(7 downto 0);

signal busPtiIn     : std_logic_vector(7 downto 0);
signal busPtiInReg  : std_logic_vector(7 downto 0);
signal busFifoOut   : std_logic_vector(7 downto 0);

-------------------------------------------------------------------------------
-- Module Implementation
-------------------------------------------------------------------------------

begin

--This clocking wizard is used to sychronize the clock used throughout this design
--with the prog_clko input. It reduces delays introduced by the global clocking
--network (~4ns in post-route simulation on Artix 200t). It is also used to generate
--a phase shifted clock for latching input data/flags 
clkwiz_inst : xlnx_dpti_clk
  port map
   (
    CLK_IN1 => prog_clko,
    CLK_OUT1 => clkIOB,
    CLK_OUT2 => clkPti,
    LOCKED => locked);

--This process latches the inputs from the FTDI part at IOB flip-flops. They are latched 
--using a phaseshifted clock about ~11ns after the rising edge of the input clock. This
--makes meeting the input delay timing constraints possible. Additional contstraints for
--traveling from the clkIOB domain to clkPti are automatically inferred by the tools 
--because they have a known phase relationship (signals will need to settle in <~5ns).
--If the design fails interclock timing analysis with clkIOB, first ensure that IOB flip
--flops are being instantiated for the registers in this process. Then you can try reducing
--the phase shift by a few degrees (too much will cause the inputdelay constraints to fail). Last
--resort is to modify the design so that these flags are all immediately latched to the clkPti 
--domain.
--@sjb: I recently came across this code and began questioning if it is necessary. At first thought, it seems 
--      that latching the input signals would add to needed setup times vs. just letting them thru 
--      asynchronously. It took me awhile, but I believe I understand why this is needed, so I have decided 
--      to document my reasoning further for the next time someone comes across this.  
--      I believe I inserted these because the FTDI part only holds the data on the bus valid for 1 ns
--      after a prog_clk edge, and I was concerned that the databus/ctrl signals might
--      beat the clock due to delays introduced by the clocking infrastructure. The IOBs treat this situation 
--      by ensuring the data/ctrl gets latched internally the moment it is guarenteed to be valid. This seems like 
--      the most architecture independent way to treat the problem, because it only requires three things, all of which 
--      are very likely to be present in future FPGA architectures/devices:
--           1) Ability to generate a clock with minimum input delay (~<3ns)
--           2) IOB flip-flops with minimum setup requirement (~<3ns)
--           3) Ability to generate a clock with a 230 degree phase shift relative to the generated clock with minimum input delay.
--      Last note, I think the input_delay constraints with the -min option in timing.xdc describe this requirement
--      to the tools. I'm pretty sure removing these flip-flops will cause the design to fail meeting those constraints.

process(ctlRst, clkIOB)
begin
  if (ctlRst = '1') then
    busPtiInReg <= (others =>'0');
    ctlRxf <= '0';
    ctlTxe <= '0';
  elsif (rising_edge(clkIOB)) then
    busPtiInReg <= busPtiIn;
    ctlRxf <= prog_rxen;
    ctlTxe <= prog_txen;
  end if;
end process;

-------------------------------------------------------------------------------
-- Map basic status and control signals
-------------------------------------------------------------------------------

--Asynchronous reset signal
ctlRst <= (prog_spien or rst) or not(locked);


--Top level output mapping
prog_siwun <= '1';
prog_wrn <= ctlWr;
prog_rdn <= ctlRd;
prog_oen <= ctlOe;

-- Data bus direction and control.
IOBUF_gen : for index in 0 to 7 generate
  IOBUF_inst : IOBUF
  generic map (
  DRIVE => 16,
  SLEW => "FAST")
  port map (
  O => busPtiIn(index), -- Buffer output
  IO => prog_d(index), -- Buffer inout port (connect directly to top-level port)
  I => busPtiOut(index), -- Buffer input
  T => busPtiTris -- 3-state enable input, high=input, low=output
  );
end generate;

busPtiTris <= ctlDir or ctlRst;

-------------------------------------------------------------------------------
-- PTI State Machine
-------------------------------------------------------------------------------

-- Map glitch-less control signals from the current state
ctlRd   <= stPtiCur(0); --keep in mind: active low
ctlWr   <= stPtiCur(1) or ctlEmpty; --keep in mind: active low
ctlOe   <= stPtiCur(2);
ctlDir  <= stPtiCur(3);

--Map additional control signals from the current state
ctlFwr  <= stPtiCur(4) and not ctlRxf;
ctlFrd  <= stPtiCur(5) and ((not ctlTxe) and (not ctlEmpty));

-- This process moves the state machine to the next state on each clock.
process (clkPti, ctlRst)
begin
    if ctlRst = '1' then
        stPtiCur <= stPtiRdy;
    elsif clkPti = '1' and clkPti'Event then
        stPtiCur <= stPtiNext;
    end if;
end process;

-- This process determines the next state based on the current state and the
-- state machine inputs.
-- TODO: It appears the bandwidth is very limited when the FTDI->FPGA FPGA side FIFO
--       gets almost filled (4080 out of 4096). Almost full seems to take a very long time
--       to deassert, regardless of how fast the user is reading data. This causes the state machine
--       to continuosly receive a single byte at a time (1/3 bandwidth) until the FIFO is full, or until
--       the FIFO has been read by the user past the almost fill point and no data has been available on 
--       the DPTI bus for a long time (~50 us). Need to fix this because it will lower bandwidth of designs that involve
--       continuously sending large amounts of data to the FPGA.  
process (stPtiCur, stPtiNext, ctlRxf, ctlTxe, ctlFull, ctlAFull, ctlEmpty)
begin
    case stPtiCur is
        when stPtiRdy =>
            stPtiNext <= stPtiInOut0;
        
        when stPtiInOut0 => --Start any pending transactions
            if ctlRxf = '0' and ctlFull = '0' then  --Receive data from FTDI (gets priority)
                stPtiNext <= stPtiInOut1;
            elsif ctlTxe = '0' and ctlEmpty = '0' then --send data to FTDI
                stPtiNext <= stPtiInOut3;
            else --no transaction yet
                stPtiNext <= stPtiInOut0;
            end if;
            
        when stPtiInOut1 => --Initiate read transaction (FTDI->FPGA)
            stPtiNext <= stPtiInOut2;
            
        when stPtiInOut2 => --Continue Read transaction
            if ctlRxf = '0' and ctlAFull = '0' then 
                stPtiNext <= stPtiInOut2;
            else --if no data available, or FPGA-side FIFO is almost full, stop transaction
                stPtiNext <= stPtiInOut0;
            end if;
            
        when stPtiInOut3 => --Start/Continue write transaction (FPGA->FTDI)
            if ctlTxe = '0' and ctlEmpty = '0' then --note almost empty is used because the FIFO is first-word fall thru
                stPtiNext <= stPtiInOut3;
            else --if FTDI FIFO is full, or we are on the last byte being sent, stop transaction
                stPtiNext <= stPtiInOut0;
            end if;
        
        when others =>
            stPtiNext <= stPtiRdy;
    end case;
end process;

-------------------------------------------------------------------------------
-- Input/Output Fifos for data
-------------------------------------------------------------------------------

--Output Fifo
usr2dpti_fifo : FIFO_DUALCLOCK_MACRO
generic map (
    DEVICE => "7SERIES",            -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES" 
    ALMOST_FULL_OFFSET => X"0FF0",  -- Sets almost full threshold
    ALMOST_EMPTY_OFFSET => X"000F", -- Sets the almost empty threshold
    DATA_WIDTH => 8,   -- Valid values are 1-72 (37-72 only valid when FIFO_SIZE="36Kb")
    FIFO_SIZE => "36Kb",            -- Target BRAM, "18Kb" or "36Kb" 
    FIRST_WORD_FALL_THROUGH => TRUE) -- Sets the FIFO FWFT to TRUE or FALSE
port map (
    ALMOSTEMPTY => open,   -- 1-bit output almost empty
    ALMOSTFULL => usrAFull,     -- 1-bit output almost full
    DO => busPtiOut,                     -- Output data, width defined by DATA_WIDTH parameter
    EMPTY => ctlEmpty,               -- 1-bit output empty
    FULL => usrFull,                 -- 1-bit output full
    RDCOUNT => dummyRdCnt,           -- Output read count, width determined by FIFO depth
    RDERR => open,               -- 1-bit output read error
    WRCOUNT => usrWrCnt,           -- Output write count, width determined by FIFO depth
    WRERR => usrWrErr,               -- 1-bit output write error
    DI => usrDI,                     -- Input data, width defined by DATA_WIDTH parameter
    RDCLK => clkPti,               -- 1-bit input read clock
    RDEN => ctlFrd,                 -- 1-bit input read enable
    RST => ctlRst,                   -- 1-bit input reset
    WRCLK => usrWrClk,               -- 1-bit input write clock
    WREN => usrWrEn                  -- 1-bit input write enable
);
  
usrWrClk <= wr_clk;
usrWrEn <= wr_en;
wr_full <= usrFull;
wr_afull <= usrAFull;
wr_err <= usrWrErr;
wr_count <= usrWrCnt;
usrDI <= wr_di;
   
--Input Fifo
dpti2usr_fifo : FIFO_DUALCLOCK_MACRO
generic map (
    DEVICE => "7SERIES",            -- Target Device: "VIRTEX5", "VIRTEX6", "7SERIES" 
    ALMOST_FULL_OFFSET => X"0FF0",  -- Sets almost full threshold
    ALMOST_EMPTY_OFFSET => X"000F", -- Sets the almost empty threshold
    DATA_WIDTH => 8,   -- Valid values are 1-72 (37-72 only valid when FIFO_SIZE="36Kb")
    FIFO_SIZE => "36Kb",            -- Target BRAM, "18Kb" or "36Kb" 
    FIRST_WORD_FALL_THROUGH => TRUE) -- Sets the FIFO FWFT to TRUE or FALSE
port map (
    ALMOSTEMPTY => usrAEmpty,   -- 1-bit output almost empty
    ALMOSTFULL => ctlAFull,     -- 1-bit output almost full
    DO => usrDO,                     -- Output data, width defined by DATA_WIDTH parameter
    EMPTY => usrEmpty,               -- 1-bit output empty
    FULL => ctlFull,                 -- 1-bit output full
    RDCOUNT => usrRdCnt,           -- Output read count, width determined by FIFO depth
    RDERR => usrRdErr,               -- 1-bit output read error
    WRCOUNT => dummyWrCnt,           -- Output write count, width determined by FIFO depth
    WRERR => open,               -- 1-bit output write error
    DI => busPtiInReg,                     -- Input data, width defined by DATA_WIDTH parameter
    RDCLK => usrRdClk,               -- 1-bit input read clock
    RDEN => usrRdEn,                 -- 1-bit input read enable
    RST => ctlRst,                   -- 1-bit input reset
    WRCLK => clkPti,               -- 1-bit input write clock
    WREN => ctlFwr                  -- 1-bit input write enable
);
  
usrRdClk <= rd_clk;
usrRdEn <= rd_en;
rd_empty <= usrEmpty;
rd_aempty <= usrAEmpty;
rd_err <= usrRdErr;
rd_count <= usrRdCnt;
rd_do <= usrDO;

end Behavioral;

