--
-- UART receiver
--
-- Author:   Sebastian Witt
-- Date:     27.01.2008
-- Version:  1.2
--
-- This code is free software; you can redistribute it and/or
-- modify it under the terms of the GNU Lesser General Public
-- License as published by the Free Software Foundation; either
-- version 2.1 of the License, or (at your option) any later version.
--
-- This code is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
-- Lesser General Public License for more details.
--
-- You should have received a copy of the GNU Lesser General Public
-- License along with this library; if not, write to the
-- Free Software  Foundation, Inc., 59 Temple Place, Suite 330,
-- Boston, MA  02111-1307  USA
--

LIBRARY IEEE;
USE IEEE.std_logic_1164.all;
USE IEEE.numeric_std.all;

-- Serial UART receiver
entity uart_receiver is
    port (
        CLK         : in std_logic;                                 -- Clock
        RST         : in std_logic;                                 -- Reset
        RXCLK       : in std_logic;                                 -- Receiver clock (16x baudrate)
        RXCLEAR     : in std_logic;                                 -- Reset receiver state
        WLS         : in std_logic_vector(1 downto 0);              -- Word length select
        STB         : in std_logic;                                 -- Number of stop bits
        PEN         : in std_logic;                                 -- Parity enable
        EPS         : in std_logic;                                 -- Even parity select
        SP          : in std_logic;                                 -- Stick parity
        SIN         : in std_logic;                                 -- Receiver input
        PE          : out std_logic;                                -- Parity error
        FE          : out std_logic;                                -- Framing error
        BI          : out std_logic;                                -- Break interrupt
        DOUT        : out std_logic_vector(7 downto 0);             -- Output data
        RXFINISHED  : out std_logic                                 -- Receiver operation finished
    );
end uart_receiver;

architecture rtl of uart_receiver is
    -- Majority voting logic
    component slib_mv_filter is
        generic (
            WIDTH       : natural := 4;
            THRESHOLD   : natural := 10
        );
        port (
            CLK         : in std_logic;                             -- Clock
            RST         : in std_logic;                             -- Reset
            SAMPLE      : in std_logic;                             -- Clock enable for sample process
            CLEAR       : in std_logic;                             -- Reset process
            D           : in std_logic;                             -- Signal input
            Q           : out std_logic                             -- Signal D was at least THRESHOLD samples high
        );
    end component;
    component slib_input_filter is
        generic (
            SIZE        : natural := 4      -- Filter counter size
        );
        port (
            CLK         : in std_logic;     -- Clock
            RST         : in std_logic;     -- Reset
            CE          : in std_logic;     -- Clock enable
            D           : in std_logic;     -- Signal input
            Q           : out std_logic     -- Signal output
        );
    end component;

    -- Counter
    component slib_counter is
        generic (
            WIDTH       : natural := 4       -- Counter width
        );
        port (
            CLK         : in std_logic;      -- Clock
            RST         : in std_logic;      -- Reset
            CLEAR       : in std_logic;      -- Clear counter register
            LOAD        : in std_logic;      -- Load counter register
            ENABLE      : in std_logic;      -- Enable count operation
            DOWN        : in std_logic;      -- Count direction down
            D           : in std_logic_vector(WIDTH-1 downto 0);    -- Load counter register input
            Q           : out std_logic_vector(WIDTH-1 downto 0);   -- Shift register output
            OVERFLOW    : out std_logic      -- Counter overflow
        );
    end component;

    -- FSM
    type state_type is (IDLE, START, DATA, PAR, STOP, MWAIT);
    signal CState, NState : state_type;

    -- Signals
    signal iBaudCount          : std_logic_vector(3 downto 0);      -- Baud counter output
    signal iBaudCountClear     : std_logic;                         -- Baud counter clear
    signal iBaudStep           : std_logic;                         -- Next symbol pulse
    signal iBaudStepD          : std_logic;                         -- Next symbol pulse delayed by one clock
    signal iFilterClear        : std_logic;                         -- Reset input filter
    signal iFSIN               : std_logic;                         -- Filtered SIN
    signal iFStopBit           : std_logic;                         -- Filtered SIN for stop bit detection
    signal iParity             : std_logic;                         -- Data parity
    signal iParityReceived     : std_logic;                         -- Parity received
    signal iDataCount          : integer range 0 to 8;              -- Data bit counter
    signal iDataCountInit      : std_logic;                         -- Initialize data bit counter to word length
    signal iDataCountFinish    : std_logic;                         -- Data bit counter finished
    signal iRXFinished         : std_logic;                         -- Word received, output data valid
    signal iFE                 : std_logic;                         -- Internal frame error
    signal iBI                 : std_logic;                         -- Internal break interrupt
    signal iNoStopReceived     : std_logic;                         -- No valid stop bit received
    signal iDOUT               : std_logic_vector(7 downto 0);      -- Data output

begin

    -- Baudrate counter: RXCLK/16
    RX_BRC: slib_counter generic map (
                                WIDTH       => 4
                         ) port map (
                                CLK         => CLK,
                                RST         => RST,
                                CLEAR       => iBaudCountClear,
                                LOAD        => '0',
                                ENABLE      => RXCLK,
                                DOWN        => '0',
                                D           => x"0",
                                Q           => iBaudCount,
                                OVERFLOW    => iBaudStep
                         );

    -- Input filter
    RX_MVF: slib_mv_filter generic map (
                                WIDTH       => 4,
                                THRESHOLD   => 10
                           ) port map (
                                CLK         => CLK,
                                RST         => RST,
                                SAMPLE      => RXCLK,
                                CLEAR       => iFilterClear,
                                D           => SIN,
                                Q           => iFSIN
                            );

    -- Input filter for the stop bit
    RX_IFSB: slib_input_filter generic map (
                                SIZE        => 4
                           ) port map (
                                CLK         => CLK,
                                RST         => RST,
                                CE          => RXCLK,
                                D           => SIN,
                                Q           => iFStopBit
                            );

    -- iBaudStepD
    RX_IFC: process (CLK, RST)
    begin
        if (RST = '1') then
            iBaudStepD <= '0';
        elsif (CLK'event and CLK = '1') then
            iBaudStepD <= iBaudStep;
        end if;
    end process;

    iFilterClear <= iBaudStepD or iBaudCountClear;

    -- Parity generation
    RX_PAR: process (iDOUT, EPS)
    begin
        iParity <= iDOUT(7) xor iDOUT(6) xor iDOUT(5) xor iDOUT(4) xor iDOUT(3) xor iDOUT(2) xor iDOUT(1) xor iDOUT(0) xor not EPS;
    end process;

    -- Data bit capture
    RX_DATACOUNT: process (CLK, RST)
    begin
        if (RST = '1') then
            iDataCount <= 0;
            iDOUT <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (iDataCountInit = '1') then
                iDataCount <= 0;
                iDOUT <= (others => '0');
            else
                if (iBaudStep = '1' and iDataCountFinish = '0') then
                    iDOUT(iDataCount) <= iFSIN;
                    iDataCount <= iDataCount + 1;
                end if;
            end if;
        end if;
    end process;

    iDataCountFinish <= '1' when (WLS = "00" and iDataCount = 5) or
                                 (WLS = "01" and iDataCount = 6) or
                                 (WLS = "10" and iDataCount = 7) or
                                 (WLS = "11" and iDataCount = 8) else '0';

    -- FSM update process
    RX_FSMUPDATE: process (CLK, RST)
    begin
        if (RST = '1') then
            CState <= IDLE;
        elsif (CLK'event and CLK = '1') then
            CState <= NState;
        end if;
    end process;

    -- RX FSM
    RX_FSM: process (CState, SIN, iFSIN, iFStopBit, iBaudStep, iBaudCount, iDataCountFinish, PEN, WLS, STB)
    begin
        -- Defaults
        NState          <= IDLE;
        iBaudCountClear <= '0';
        iDataCountInit  <= '0';
        iRXFinished     <= '0';

        case CState is
            when IDLE   =>  if (SIN = '0') then                 -- Start detected
                                NState <= START;
                            end if;
                            iBaudCountClear <= '1';
                            iDataCountInit  <= '1';
            when START  =>  iDataCountInit  <= '1';
                            if (iBaudStep = '1') then           -- Wait for start bit end
                                if (iFSIN = '0') then
                                    NState <= DATA;
                                end if;
                            else
                                NState <= START;
                            end if;
            when DATA   =>  if (iDataCountFinish = '1') then    -- Received all data bits
                                if (PEN = '1') then
                                    NState <= PAR;              -- Parity enabled
                                else
                                    NState <= STOP;             -- No parity
                                end if;
                            else
                                NState <= DATA;
                            end if;
            when PAR    =>  if (iBaudStep = '1') then           -- Wait for parity bit
                                NState <= STOP;
                            else
                                NState <= PAR;
                            end if;
            when STOP   =>  if (iBaudCount(3) = '1') then       -- Wait for stop bit
                                if (iFStopBit = '0') then       -- No stop bit received
                                    iRXFinished <= '1';
                                    NState <= MWAIT;
                                else
                                    iRXFinished <= '1';
                                    NState <= IDLE;             -- Stop bit end
                                end if;
                            else
                                NState <= STOP;
                            end if;
            when MWAIT  =>  if (SIN = '0') then                 -- Wait for mark
                                NState <= MWAIT;
                            end if;
            when others =>  null;
        end case;
    end process;

    -- Check parity
    RX_PARCHECK: process (CLK, RST)
    begin
        if (RST = '1') then
            PE <= '0';
            iParityReceived <= '0';
        elsif (CLK'event and CLK = '1') then
            if (CState = PAR and iBaudStep = '1') then
                iParityReceived <= iFSIN;                       -- Received parity bit
            end if;

            -- Check parity
            if (PEN = '1') then                                 -- Parity enabled
                PE <= '0';
                if (SP = '1') then                              -- Sticky parity
                    if ((EPS xor iParityReceived) = '0') then
                        PE <= '1';                              -- Parity error
                    end if;
                else
                    if (iParity /= iParityReceived) then
                        PE <= '1';                              -- Parity error
                    end if;
                end if;
            else
                PE <= '0';                                      -- Parity disabled
                iParityReceived <= '0';
            end if;
        end if;
    end process;

    -- Framing error and break interrupt
    iNoStopReceived <= '1' when iFStopBit = '0' and (CState = STOP) else '0';
    iBI <= '1' when iDOUT = "00000000" and
                    iParityReceived = '0' and
                    iNoStopReceived = '1' else '0';
    iFE <= '1' when iNoStopReceived = '1' else '0';

    -- Output signals
    DOUT <= iDOUT;
    BI   <= iBI;
    FE   <= iFE;
    RXFINISHED <= iRXFinished;

end rtl;

