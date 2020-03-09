--
-- Majority voting filter
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


entity slib_mv_filter is
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
end slib_mv_filter;

architecture rtl of slib_mv_filter is

    -- Signals
    signal iCounter     : unsigned(WIDTH downto 0);             -- Sample counter
    signal iQ           : std_logic;                            -- Internal Q

begin
    -- Main process
    MV_PROC: process (RST, CLK)
    begin
        if (RST = '1') then
            iCounter  <= (others => '0');
            iQ        <= '0';
        elsif (CLK'event and CLK='1') then
            if (iCounter >= THRESHOLD) then                     -- Compare with threshold
                iQ <= '1';
            else
                if (SAMPLE = '1' and D = '1') then              -- Take sample
                    iCounter <= iCounter + 1;
                end if;
            end if;

            if (CLEAR = '1') then                               -- Reset logic
                iCounter  <= (others => '0');
                iQ        <= '0';
            end if;

        end if;
    end process;

    -- Output signals
    Q <= iQ;

end rtl;

