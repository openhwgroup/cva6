--
-- Input synchronization
--
-- Author:   Sebastian Witt
-- Data:     27.01.2008
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

entity slib_input_sync is
    port (
        CLK         : in std_logic;     -- Clock
        RST         : in std_logic;     -- Reset
        D           : in std_logic;     -- Signal input
        Q           : out std_logic     -- Signal output
    );
end slib_input_sync;

architecture rtl of slib_input_sync is
    signal iD : std_logic_vector(1 downto 0);
begin
    IS_D: process (RST, CLK)
    begin
        if (RST  = '1') then
            iD <= (others => '0');
        elsif (CLK'event and CLK='1') then
            iD(0) <= D;
            iD(1) <= iD(0);
        end if;
    end process;

    -- Output ports
    Q <= iD(1);

end rtl;

