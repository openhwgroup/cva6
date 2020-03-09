--
-- Clock divider (clock enable generator)
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


entity slib_clock_div is
    generic (
        RATIO       : integer := 4      -- Clock divider ratio
    );
    port (
        CLK         : in std_logic;     -- Clock
        RST         : in std_logic;     -- Reset
        CE          : in std_logic;     -- Clock enable input
        Q           : out std_logic     -- New clock enable output
    );
end slib_clock_div;

architecture rtl of slib_clock_div is
    -- Signals
    signal iQ       : std_logic;                  -- Internal Q
    signal iCounter : integer range 0 to RATIO-1; -- Counter

begin
    -- Main process
    CD_PROC: process (RST, CLK)
    begin
        if (RST = '1') then
            iCounter <= 0;
            iQ       <= '0';
        elsif (CLK'event and CLK='1') then
            iQ <= '0';
            if (CE = '1') then
                if (iCounter = (RATIO-1)) then
                    iQ <= '1';
                    iCounter <= 0;
                else
                    iCounter <= iCounter + 1;
                end if;
            end if;
        end if;
    end process;

    -- Output signals
    Q <= iQ;

end rtl;

