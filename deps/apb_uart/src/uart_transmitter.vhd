--
-- UART transmitter
--
-- Author:   Sebastian Witt
-- Date:     27.01.2008
-- Version:  1.0
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

-- Serial UART transmitter
entity uart_transmitter is
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        TXCLK       : in std_logic;                             -- Transmitter clock (2x baudrate)
        TXSTART     : in std_logic;                             -- Start transmitter
        CLEAR       : in std_logic;                             -- Clear transmitter state
        WLS         : in std_logic_vector(1 downto 0);          -- Word length select
        STB         : in std_logic;                             -- Number of stop bits
        PEN         : in std_logic;                             -- Parity enable
        EPS         : in std_logic;                             -- Even parity select
        SP          : in std_logic;                             -- Stick parity
        BC          : in std_logic;                             -- Break control
        DIN         : in std_logic_vector(7 downto 0);          -- Input data
        TXFINISHED  : out std_logic;                            -- Transmitter operation finished
        SOUT        : out std_logic                             -- Transmitter output
    );
end uart_transmitter;

architecture rtl of uart_transmitter is
    -- FSM
    type state_type is (IDLE, START, BIT0, BIT1, BIT2, BIT3, BIT4, BIT5, BIT6, BIT7, PAR, STOP, STOP2);
    signal CState, NState : state_type;

    -- Signals
    signal iTx2         : std_logic;        -- Next TX step
    signal iSout        : std_logic;        -- Transmitter output
    signal iParity      : std_logic;        -- Parity
    signal iFinished    : std_logic;        -- TX finished

begin
    -- Transmitter FSM update process
    TX_PROC: process (RST, CLK)
    begin
        if (RST = '1') then
            CState <= IDLE;
            iTx2   <= '0';
        elsif (CLK'event and CLK='1') then
            if (TXCLK = '1') then           -- TX clock
                if (iTx2 = '0') then        -- Two TX clocks per step
                    CState <= NState;       -- Next step
                    iTx2 <= '1';
                else
                    if ((WLS = "00") and (STB = '1') and CState = STOP2) then
                        CState <= NState;   -- 1.5 stop bits for 5 bit word mode
                        iTx2 <= '1';
                    else
                        CState <= CState;   -- First TX clock, wait
                        iTx2 <= '0';
                    end if;
                end if;
            end if;
        end if;
    end process;

    -- Transmitter FSM
    TX_FSM: process (CState, TXSTART, DIN, WLS, PEN, SP, EPS, STB, iParity)
    begin
        -- Defaults
        NState      <= IDLE;
        iSout       <= '1';

        case CState is
            when IDLE   =>  if (TXSTART = '1') then
                                NState <= START;
                            end if;
            when START  =>  iSout  <= '0';
                            NState <= BIT0;
            when BIT0   =>  iSout  <= DIN(0);
                            NState <= BIT1;
            when BIT1   =>  iSout  <= DIN(1);
                            NState <= BIT2;
            when BIT2   =>  iSout  <= DIN(2);
                            NState <= BIT3;
            when BIT3   =>  iSout  <= DIN(3);
                            NState <= BIT4;
            when BIT4   =>  iSout  <= DIN(4);
                            if (WLS = "00") then            -- 5 bits
                                if (PEN = '1') then
                                    NState <= PAR;          -- Parity enabled
                                else
                                    NState <= STOP;         -- No parity
                                end if;
                            else
                                NState <= BIT5;
                            end if;
            when BIT5   =>  iSout  <= DIN(5);
                            if (WLS = "01") then            -- 6 bits
                                if (PEN = '1') then
                                    NState <= PAR;          -- Parity enabled
                                else
                                    NState <= STOP;         -- No parity
                                end if;
                            else
                                NState <= BIT6;
                            end if;
            when BIT6   =>  iSout  <= DIN(6);
                            if (WLS = "10") then            -- 7 bits
                                if (PEN = '1') then
                                    NState <= PAR;          -- Parity enabled
                                else
                                    NState <= STOP;         -- No parity
                                end if;
                            else
                                NState <= BIT7;
                            end if;
            when BIT7   =>  iSout  <= DIN(7);
                            if (PEN = '1') then
                                NState <= PAR;              -- Parity enabled
                            else
                                NState <= STOP;             -- No parity
                            end if;
            when PAR    =>  if (SP = '1') then              -- Sticky parity
                                if (EPS = '1') then
                                    iSout <= '0';           -- Even parity -> cleared
                                else
                                    iSout <= '1';           -- Odd parity  -> set
                                end if;
                            else
                                if (EPS = '1') then
                                    iSout <= iParity;       -- Even parity
                                else
                                    iSout <= not iParity;   -- Odd parity
                                end if;
                            end if;
                            NState <= STOP;
            when STOP   =>  if (STB = '1') then             -- 2 stop bits
                                NState <= STOP2;
                            else
                                if (TXSTART = '1') then     -- Next transmission
                                    NState <= START;
                                end if;
                            end if;
            when STOP2  =>  if (TXSTART = '1') then         -- Next transmission
                                NState <= START;
                            end if;
            when others =>  null;
        end case;


    end process;


    -- Parity generation
    TX_PAR: process (DIN, WLS)
        variable iP40, iP50, iP60, iP70 : std_logic;
    begin
        iP40 := DIN(4) xor DIN(3) xor DIN(2) xor DIN(1) xor DIN(0);
        iP50 := DIN(5) xor iP40;
        iP60 := DIN(6) xor iP50;
        iP70 := DIN(7) xor iP60;

        case WLS is
            when "00"   => iParity <= iP40;
            when "01"   => iParity <= iP50;
            when "10"   => iParity <= iP60;
            when others => iParity <= iP70;
        end case;
    end process;


    -- Signal TX finished on STOP bit transmission
    TX_FIN: process (CLK, RST)
        variable iLast : std_logic;
    begin
        if (RST = '1') then
            iFinished <= '0';
            iLast := '0';
        elsif (CLK'event and CLK = '1') then
            iFinished <= '0';
            if (iLast = '0' and CState = STOP) then
                iFinished <= '1';
            end if;

            if (CState = STOP) then
                iLast := '1';
            else
                iLast := '0';
            end if;
        end if;
    end process;

    -- Output signals
    SOUT       <= iSout when BC = '0' else '0';
    TXFINISHED <= iFinished;

end rtl;

