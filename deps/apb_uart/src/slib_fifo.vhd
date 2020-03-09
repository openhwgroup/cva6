--
-- FIFO
--
-- Author:   Sebastian Witt
-- Date:     29.01.2008
-- Version:  1.3
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


entity slib_fifo is
    generic (
        WIDTH       : integer := 8;                             -- FIFO width
        SIZE_E      : integer := 6                              -- FIFO size (2^SIZE_E)
    );
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        CLEAR       : in std_logic;                             -- Clear FIFO
        WRITE       : in std_logic;                             -- Write to FIFO
        READ        : in std_logic;                             -- Read from FIFO
        D           : in std_logic_vector(WIDTH-1 downto 0);    -- FIFO input
        Q           : out std_logic_vector(WIDTH-1 downto 0);   -- FIFO output
        EMPTY       : out std_logic;                            -- FIFO is empty
        FULL        : out std_logic;                            -- FIFO is full
        USAGE       : out std_logic_vector(SIZE_E-1 downto 0)   -- FIFO usage
    );
end slib_fifo;

architecture rtl of slib_fifo is
    -- Signals
    signal iEMPTY   : std_logic;                                -- Internal EMPTY
    signal iFULL    : std_logic;                                -- Internal FULL
    signal iWRAddr  : unsigned(SIZE_E downto 0);                -- FIFO write address
    signal iRDAddr  : unsigned(SIZE_E downto 0);                -- FIFO read address
    signal iUSAGE   : unsigned(SIZE_E-1 downto 0);              -- FIFO usage
    -- FIFO memory
    type FIFO_Mem_Type is array (2**SIZE_E-1 downto 0) of std_logic_vector(WIDTH-1 downto 0);
    signal iFIFOMem : FIFO_Mem_Type := (others => (others => '0'));

begin
    -- Full signal (biggest difference of read and write address)
    iFULL <= '1' when (iRDAddr(SIZE_E-1 downto 0) = iWRAddr(SIZE_E-1 downto 0)) and
                      (iRDAddr(SIZE_E)           /= iWRAddr(SIZE_E)) else '0';

    -- Write/read address counter and empty signal
    FF_ADDR: process (RST, CLK)
    begin
        if (RST = '1') then
            iWRAddr <= (others => '0');
            iRDAddr <= (others => '0');
            iEMPTY  <= '1';
        elsif (CLK'event and CLK='1') then
            if (WRITE = '1' and iFULL = '0') then       -- Write to FIFO
                iWRAddr <= iWRAddr + 1;
            end if;

            if (READ = '1' and iEMPTY = '0') then       -- Read from FIFO
                iRDAddr <= iRDAddr + 1;
            end if;

            if (CLEAR = '1') then                       -- Reset FIFO
                iWRAddr <= (others => '0');
                iRDAddr <= (others => '0');
            end if;

            if (iRDAddr = iWRAddr) then                 -- Empty signal (read address same as write address)
                iEMPTY <= '1';
            else
                iEMPTY <= '0';
            end if;
        end if;
    end process;

    -- FIFO memory process
    FF_MEM: process (RST, CLK)
    begin
        if (RST = '1') then
            iFIFOMem(2**SIZE_E-1 downto 0) <= (others => (others => '0'));
            Q <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (WRITE = '1' and iFULL = '0') then
                iFIFOMem(to_integer(iWRAddr(SIZE_E-1 downto 0))) <= D;
            end if;
            Q <= iFIFOMem(to_integer(iRDAddr(SIZE_E-1 downto 0)));
        end if;
    end process;

    -- Usage counter
    FF_USAGE: process (RST, CLK)
    begin
        if (RST = '1') then
            iUSAGE <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (CLEAR = '1') then
                iUSAGE <= (others => '0');
            else
                if (READ = '0' and WRITE = '1' and iFULL = '0') then
                    iUSAGE <= iUSAGE + 1;
                end if;
                if (WRITE = '0' and READ = '1' and iEMPTY = '0') then
                    iUSAGE <= iUSAGE - 1;
                end if;
            end if;
        end if;
    end process;

    -- Output signals
    EMPTY <= iEMPTY;
    FULL  <= iFULL;
    USAGE <= std_logic_vector(iUSAGE);

end rtl;


