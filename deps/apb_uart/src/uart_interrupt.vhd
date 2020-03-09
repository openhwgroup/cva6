--
-- UART interrupt control
--
-- Author:   Sebastian Witt
-- Date:     27.01.2008
-- Version:  1.1
--
-- History:  1.0 - Initial version
--           1.1 - Automatic flow control
--
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

-- Serial UART interrupt control
entity uart_interrupt is
    port (
        CLK         : in std_logic;                                 -- Clock
        RST         : in std_logic;                                 -- Reset
        IER         : in std_logic_vector(3 downto 0);              -- IER 3:0
        LSR         : in std_logic_vector(4 downto 0);              -- LSR 4:0
        THI         : in std_logic;                                 -- Transmitter holding register empty interrupt
        RDA         : in std_logic;                                 -- Receiver data available
        CTI         : in std_logic;                                 -- Character timeout indication
        AFE         : in std_logic;                                 -- Automatic flow control enable
        MSR         : in std_logic_vector(3 downto 0);              -- MSR 3:0
        IIR         : out std_logic_vector(3 downto 0);             -- IIR 3:0
        INT         : out std_logic                                 -- Interrupt
    );
end uart_interrupt;

architecture rtl of uart_interrupt is
    -- Signals
    signal iRLSInterrupt    : std_logic;                            -- Receiver line status interrupt
    signal iRDAInterrupt    : std_logic;                            -- Received data available interrupt
    signal iCTIInterrupt    : std_logic;                            -- Character timeout indication interrupt
    signal iTHRInterrupt    : std_logic;                            -- Transmitter holding register empty interrupt
    signal iMSRInterrupt    : std_logic;                            -- Modem status interrupt
    signal iIIR             : std_logic_vector(3 downto 0);         -- IIR register
begin

    -- Priority 1: Receiver line status interrupt on: Overrun error, parity error, framing error or break interrupt
    iRLSInterrupt <= IER(2) and (LSR(1) or LSR(2) or LSR(3) or LSR(4));

    -- Priority 2: Received data available or trigger level reached in FIFO mode
    iRDAInterrupt <= IER(0) and RDA;

    -- Priority 2: Character timeout indication
    iCTIInterrupt <= IER(0) and CTI;

    -- Priority 3: Transmitter holding register empty
    iTHRInterrupt <= IER(1) and THI;

    -- Priority 4: Modem status interrupt: dCTS (when AFC is disabled), dDSR, TERI, dDCD
    iMSRInterrupt <= IER(3) and ((MSR(0) and not AFE) or MSR(1) or MSR(2) or MSR(3));

    -- IIR
    IC_IIR: process (CLK, RST)
    begin
        if (RST = '1') then
            iIIR <= "0001";     -- TODO: Invert later
        elsif (CLK'event and CLK = '1') then
            -- IIR register
            if (iRLSInterrupt = '1') then
                iIIR <= "0110";
            elsif (iCTIInterrupt = '1') then
                iIIR <= "1100";
            elsif (iRDAInterrupt = '1') then
                iIIR <= "0100";
            elsif (iTHRInterrupt = '1') then
                iIIR <= "0010";
            elsif (iMSRInterrupt = '1') then
                iIIR <= "0000";
            else
                iIIR <= "0001";
            end if;
        end if;
    end process;

    -- Outputs
    IIR <= iIIR;
    INT <= not iIIR(0);

end rtl;

