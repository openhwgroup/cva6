--
-- UART Baudrate generator
--
-- Author:   Sebastian Witt
-- Date:     27.01.2008
-- Version:  1.1
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

-- Serial UART baudrate generator
entity uart_baudgen is
    port (
        CLK         : in std_logic;                                 -- Clock
        RST         : in std_logic;                                 -- Reset
        CE          : in std_logic;                                 -- Clock enable
        CLEAR       : in std_logic;                                 -- Reset generator (synchronization)
        DIVIDER     : in std_logic_vector(15 downto 0);             -- Clock divider
        BAUDTICK    : out std_logic                                 -- 16xBaudrate tick
    );
end uart_baudgen;

architecture rtl of uart_baudgen is
    -- Signals
    signal iCounter : unsigned(15 downto 0);
begin
    -- Baudrate counter
    BG_COUNT: process (CLK, RST)
    begin
        if (RST = '1') then
            iCounter <= (others => '0');
            BAUDTICK <= '0';
        elsif (CLK'event and CLK = '1') then
            if (CLEAR = '1') then
                iCounter <= (others => '0');
            elsif (CE = '1') then
                iCounter <= iCounter + 1;
            end if;

            BAUDTICK <= '0';
            if (iCounter = unsigned(DIVIDER)) then
                iCounter <= (others => '0');
                BAUDTICK <= '1';
            end if;
        end if;
    end process;

end rtl;


