--
-- Counter
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

-- Counter
entity slib_counter is
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
end slib_counter;

architecture rtl of slib_counter is
    signal iCounter : unsigned(WIDTH downto 0);         -- Counter register
begin
    -- Counter process
    COUNT_SHIFT: process (RST, CLK)
    begin
        if (RST = '1') then
            iCounter <= (others => '0');                -- Reset counter register
        elsif (CLK'event and CLK='1') then
            if (CLEAR = '1') then
                iCounter <= (others => '0');            -- Clear counter register
            elsif (LOAD = '1') then                     -- Load counter register
                iCounter <= unsigned('0' & D);
            elsif (ENABLE = '1') then                   -- Enable counter
                if (DOWN = '0') then                    -- Count up
                    iCounter <= iCounter + 1;
                else                                    -- Count down
                    iCounter <= iCounter - 1;
                end if;
            end if;
            if (iCounter(WIDTH) = '1') then             -- Clear overflow
                iCounter(WIDTH) <= '0';
            end if;
        end if;

    end process;

    -- Output ports
    Q        <= std_logic_vector(iCounter(WIDTH-1 downto 0));
    OVERFLOW <= iCounter(WIDTH);
end rtl;

