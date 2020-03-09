--
-- Signal edge detect
--
-- Author:   Sebastian Witt
-- Data:     27.01.2008
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

entity slib_edge_detect is
    port (
        CLK         : in std_logic;     -- Clock
        RST         : in std_logic;     -- Reset
        D           : in std_logic;     -- Signal input
        RE          : out std_logic;    -- Rising edge detected
        FE          : out std_logic     -- Falling edge detected
    );
end slib_edge_detect;

architecture rtl of slib_edge_detect is
    signal iDd : std_logic;             -- D register
begin
    -- Store D
    ED_D: process (RST, CLK)
    begin
        if (RST  = '1') then
            iDd <= '0';
        elsif (CLK'event and CLK='1') then
            iDd <= D;
        end if;
    end process;

    -- Output ports
    RE <= '1' when iDd = '0' and D = '1' else '0';
    FE <= '1' when iDd = '1' and D = '0' else '0';

end rtl;


