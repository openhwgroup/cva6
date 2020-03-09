--
-- UART 16750
--
-- Author:   Sebastian Witt
-- Date:     29.01.2008
-- Version:  1.5
--
-- History:  1.0 - Initial version
--           1.1 - THR empty interrupt register connected to RST
--           1.2 - Registered outputs
--           1.3 - Automatic flow control
--           1.4 - De-assert IIR FIFO64 when FIFO is disabled
--           1.5 - Inverted low active outputs when RST is active
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

-- Serial UART
entity apb_uart is
    port (
        CLK         : in std_logic;                             -- Clock
        RSTN        : in std_logic;                             -- Reset negated

        PSEL        : in std_logic;                             -- APB psel signal
        PENABLE     : in std_logic;                             -- APB penable signal
        PWRITE      : in std_logic;                             -- APB pwrite signal
        PADDR       : in std_logic_vector(2 downto 0);          -- APB paddr signal
      	PWDATA      : in std_logic_vector(31 downto 0);         -- APB pwdata signal
      	PRDATA      : out std_logic_vector(31 downto 0);        -- APB prdata signal
        PREADY      : out std_logic;                            -- APB pready signal
        PSLVERR     : out std_logic;                            -- APB pslverr signal

        INT         : out std_logic;                            -- Interrupt output

        OUT1N       : out std_logic;                            -- Output 1
        OUT2N       : out std_logic;                            -- Output 2
        RTSN        : out std_logic;                            -- RTS output
        DTRN        : out std_logic;                            -- DTR output
        CTSN        : in std_logic;                             -- CTS input
        DSRN        : in std_logic;                             -- DSR input
        DCDN        : in std_logic;                             -- DCD input
        RIN         : in std_logic;                             -- RI input
        SIN         : in std_logic;                             -- Receiver input
        SOUT        : out std_logic                             -- Transmitter output
    );
end apb_uart;

architecture rtl of apb_uart is
    -- UART transmitter
    component uart_transmitter is
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
    end component;
    -- UART receiver
    component uart_receiver is
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        RXCLK       : in std_logic;                             -- Receiver clock (16x baudrate)
        RXCLEAR     : in std_logic;                             -- Reset receiver state
        WLS         : in std_logic_vector(1 downto 0);          -- Word length select
        STB         : in std_logic;                             -- Number of stop bits
        PEN         : in std_logic;                             -- Parity enable
        EPS         : in std_logic;                             -- Even parity select
        SP          : in std_logic;                             -- Stick parity
        SIN         : in std_logic;                             -- Receiver input
        PE          : out std_logic;                            -- Parity error
        FE          : out std_logic;                            -- Framing error
        BI          : out std_logic;                            -- Break interrupt
        DOUT        : out std_logic_vector(7 downto 0);         -- Output data
        RXFINISHED  : out std_logic                             -- Receiver operation finished
    );
    end component;
    -- UART interrupt control
    component uart_interrupt is
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        IER         : in std_logic_vector(3 downto 0);          -- IER 3:0
        LSR         : in std_logic_vector(4 downto 0);          -- LSR 4:0
        THI         : in std_logic;                             -- Transmitter holding register empty interrupt
        RDA         : in std_logic;                             -- Receiver data available
        CTI         : in std_logic;                             -- Character timeout indication
        AFE         : in std_logic;                             -- Automatic flow control enable
        MSR         : in std_logic_vector(3 downto 0);          -- MSR 3:0
        IIR         : out std_logic_vector(3 downto 0);         -- IIR 3:0
        INT         : out std_logic                             -- Interrupt
    );
    end component;
    -- UART baudrate generator
    component uart_baudgen is
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        CE          : in std_logic;                             -- Clock enable
        CLEAR       : in std_logic;                             -- Reset generator (synchronization)
        DIVIDER     : in std_logic_vector(15 downto 0);         -- Clock divider
        BAUDTICK    : out std_logic                             -- 16xBaudrate tick
    );
    end component;
    -- UART FIFO
    component slib_fifo is
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
    end component;
    -- Edge detect
    component slib_edge_detect is
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        D           : in std_logic;                             -- Signal input
        RE          : out std_logic;                            -- Rising edge detected
        FE          : out std_logic                             -- Falling edge detected
    );
    end component;
    -- Input synchronization
    component slib_input_sync is
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        D           : in std_logic;                             -- Signal input
        Q           : out std_logic                             -- Signal output
    );
    end component;
    -- Input filter
    component slib_input_filter is
    generic (
        SIZE        : natural := 4                              -- Filter width
    );
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        CE          : in std_logic;                             -- Clock enable
        D           : in std_logic;                             -- Signal input
        Q           : out std_logic                             -- Signal output
    );
    end component;
    -- Clock enable generation
    component slib_clock_div is
    generic (
        RATIO       : integer := 8                              -- Clock divider ratio
    );
    port (
        CLK         : in std_logic;                             -- Clock
        RST         : in std_logic;                             -- Reset
        CE          : in std_logic;                             -- Clock enable input
        Q           : out std_logic                             -- New clock enable output
    );
    end component;

    -- Global device signals
    signal iWrite           : std_logic;                        -- Write to UART
    signal iRead            : std_logic;                        -- Read from UART
    signal iRST             : std_logic;                        -- RST negated

    -- UART registers read/write signals
    signal iRBRRead         : std_logic;                        -- Read from RBR
    signal iTHRWrite        : std_logic;                        -- Write to THR
    signal iDLLWrite        : std_logic;                        -- Write to DLL
    signal iDLMWrite        : std_logic;                        -- Write to DLM
    signal iIERWrite        : std_logic;                        -- Write to IER
    signal iIIRRead         : std_logic;                        -- Read from IIR
    signal iFCRWrite        : std_logic;                        -- Write to FCR
    signal iLCRWrite        : std_logic;                        -- Write to LCR
    signal iMCRWrite        : std_logic;                        -- Write to MCR
    signal iLSRRead         : std_logic;                        -- Read from LSR
    signal iMSRRead         : std_logic;                        -- Read from MSR
    signal iSCRWrite        : std_logic;                        -- Write to SCR

    -- UART registers
    signal iTSR             : std_logic_vector(7 downto 0);     -- Transmitter holding register
    signal iRBR             : std_logic_vector(7 downto 0);     -- Receiver buffer register
    signal iDLL             : std_logic_vector(7 downto 0);     -- Divisor latch LSB
    signal iDLM             : std_logic_vector(7 downto 0);     -- Divisor latch MSB
    signal iIER             : std_logic_vector(7 downto 0);     -- Interrupt enable register
    signal iIIR             : std_logic_vector(7 downto 0);     -- Interrupt identification register
    signal iFCR             : std_logic_vector(7 downto 0);     -- FIFO control register
    signal iLCR             : std_logic_vector(7 downto 0);     -- Line control register
    signal iMCR             : std_logic_vector(7 downto 0);     -- Modem control register
    signal iLSR             : std_logic_vector(7 downto 0);     -- Line status register
    signal iMSR             : std_logic_vector(7 downto 0);     -- Modem status register
    signal iSCR             : std_logic_vector(7 downto 0);     -- Scratch register

    -- IER register signals
    signal iIER_ERBI        : std_logic;                        -- IER: Enable received data available interrupt
    signal iIER_ETBEI       : std_logic;                        -- IER: Enable transmitter holding register empty interrupt
    signal iIER_ELSI        : std_logic;                        -- IER: Enable receiver line status interrupt
    signal iIER_EDSSI       : std_logic;                        -- IER: Enable modem status interrupt

    -- IIR register signals
    signal iIIR_PI          : std_logic;                        -- IIR: Pending interrupt
    signal iIIR_ID0         : std_logic;                        -- IIR: Interrupt ID0
    signal iIIR_ID1         : std_logic;                        -- IIR: Interrupt ID1
    signal iIIR_ID2         : std_logic;                        -- IIR: Interrupt ID2
    signal iIIR_FIFO64      : std_logic;                        -- IIR: 64 byte FIFO enabled

    -- FCR register signals
    signal iFCR_FIFOEnable  : std_logic;                        -- FCR: FIFO enable
    signal iFCR_RXFIFOReset : std_logic;                        -- FCR: Receiver FIFO reset
    signal iFCR_TXFIFOReset : std_logic;                        -- FCR: Transmitter FIFO reset
    signal iFCR_DMAMode     : std_logic;                        -- FCR: DMA mode select
    signal iFCR_FIFO64E     : std_logic;                        -- FCR: 64 byte FIFO enable
    signal iFCR_RXTrigger   : std_logic_vector(1 downto 0);     -- FCR: Receiver trigger

    -- LCR register signals
    signal iLCR_WLS         : std_logic_vector(1 downto 0);     -- LCR: Word length select
    signal iLCR_STB         : std_logic;                        -- LCR: Number of stop bits
    signal iLCR_PEN         : std_logic;                        -- LCR: Parity enable
    signal iLCR_EPS         : std_logic;                        -- LCR: Even parity select
    signal iLCR_SP          : std_logic;                        -- LCR: Sticky parity
    signal iLCR_BC          : std_logic;                        -- LCR: Break control
    signal iLCR_DLAB        : std_logic;                        -- LCR: Divisor latch access bit

    -- MCR register signals
    signal iMCR_DTR         : std_logic;                        -- MCR: Data terminal ready
    signal iMCR_RTS         : std_logic;                        -- MCR: Request to send
    signal iMCR_OUT1        : std_logic;                        -- MCR: OUT1
    signal iMCR_OUT2        : std_logic;                        -- MCR: OUT2
    signal iMCR_LOOP        : std_logic;                        -- MCR: Loop
    signal iMCR_AFE         : std_logic;                        -- MCR: Auto flow control enable

    -- LSR register signals
    signal iLSR_DR          : std_logic;                        -- LSR: Data ready
    signal iLSR_OE          : std_logic;                        -- LSR: Overrun error
    signal iLSR_PE          : std_logic;                        -- LSR: Parity error
    signal iLSR_FE          : std_logic;                        -- LSR: Framing error
    signal iLSR_BI          : std_logic;                        -- LSR: Break Interrupt
    signal iLSR_THRE        : std_logic;                        -- LSR: Transmitter holding register empty
    signal iLSR_THRNF       : std_logic;                        -- LSR: Transmitter holding register not full
    signal iLSR_TEMT        : std_logic;                        -- LSR: Transmitter empty
    signal iLSR_FIFOERR     : std_logic;                        -- LSR: Error in receiver FIFO

    -- MSR register signals
    signal iMSR_dCTS        : std_logic;                        -- MSR: Delta CTS
    signal iMSR_dDSR        : std_logic;                        -- MSR: Delta DSR
    signal iMSR_TERI        : std_logic;                        -- MSR: Trailing edge ring indicator
    signal iMSR_dDCD        : std_logic;                        -- MSR: Delta DCD
    signal iMSR_CTS         : std_logic;                        -- MSR: CTS
    signal iMSR_DSR         : std_logic;                        -- MSR: DSR
    signal iMSR_RI          : std_logic;                        -- MSR: RI
    signal iMSR_DCD         : std_logic;                        -- MSR: DCD

    -- UART MSR signals
    signal iCTSNs           : std_logic;                        -- Synchronized CTSN input
    signal iDSRNs           : std_logic;                        -- Synchronized DSRN input
    signal iDCDNs           : std_logic;                        -- Synchronized DCDN input
    signal iRINs            : std_logic;                        -- Synchronized RIN input
    signal iCTSn            : std_logic;                        -- Filtered CTSN input
    signal iDSRn            : std_logic;                        -- Filtered DSRN input
    signal iDCDn            : std_logic;                        -- Filtered DCDN input
    signal iRIn             : std_logic;                        -- Filtered RIN input
    signal iCTSnRE          : std_logic;                        -- CTSn rising edge
    signal iCTSnFE          : std_logic;                        -- CTSn falling edge
    signal iDSRnRE          : std_logic;                        -- DSRn rising edge
    signal iDSRnFE          : std_logic;                        -- DSRn falling edge
    signal iDCDnRE          : std_logic;                        -- DCDn rising edge
    signal iDCDnFE          : std_logic;                        -- DCDn falling edge
    signal iRInRE           : std_logic;                        -- RIn rising edge
    signal iRInFE           : std_logic;                        -- RIn falling edge

    -- UART baudrate generation signals
    signal iBaudgenDiv      : std_logic_vector(15 downto 0);    -- Baudrate divider
    signal iBaudtick16x     : std_logic;                        -- 16x Baudrate output from baudrate generator
    signal iBaudtick2x      : std_logic;                        -- 2x Baudrate for transmitter
    signal iRCLK            : std_logic;                        -- 16x Baudrate for receiver
    signal iBAUDOUTN        : std_logic;

    -- UART FIFO signals
    signal iTXFIFOClear     : std_logic;                        -- Clear TX FIFO
    signal iTXFIFOWrite     : std_logic;                        -- Write to TX FIFO
    signal iTXFIFORead      : std_logic;                        -- Read from TX FIFO
    signal iTXFIFOEmpty     : std_logic;                        -- TX FIFO is empty
    signal iTXFIFOFull      : std_logic;                        -- TX FIFO is full
    signal iTXFIFO16Full    : std_logic;                        -- TX FIFO 16 byte mode is full
    signal iTXFIFO64Full    : std_logic;                        -- TX FIFO 64 byte mode is full
    signal iTXFIFOUsage     : std_logic_vector(5 downto 0);     -- RX FIFO usage
    signal iTXFIFOQ         : std_logic_vector(7 downto 0);     -- TX FIFO output
    signal iRXFIFOClear     : std_logic;                        -- Clear RX FIFO
    signal iRXFIFOWrite     : std_logic;                        -- Write to RX FIFO
    signal iRXFIFORead      : std_logic;                        -- Read from RX FIFO
    signal iRXFIFOEmpty     : std_logic;                        -- RX FIFO is empty
    signal iRXFIFOFull      : std_logic;                        -- RX FIFO is full
    signal iRXFIFO16Full    : std_logic;                        -- RX FIFO 16 byte mode is full
    signal iRXFIFO64Full    : std_logic;                        -- RX FIFO 64 byte mode is full
    signal iRXFIFOD         : std_logic_vector(10 downto 0);    -- RX FIFO input
    signal iRXFIFOQ         : std_logic_vector(10 downto 0);    -- RX FIFO output
    signal iRXFIFOUsage     : std_logic_vector(5 downto 0);     -- RX FIFO usage
    signal iRXFIFOTrigger   : std_logic;                        -- FIFO trigger level reached
    signal iRXFIFO16Trigger : std_logic;                        -- FIFO 16 byte mode trigger level reached
    signal iRXFIFO64Trigger : std_logic;                        -- FIFO 64 byte mode trigger level reached
    signal iRXFIFOPE        : std_logic;                        -- Parity error from FIFO
    signal iRXFIFOFE        : std_logic;                        -- Frame error from FIFO
    signal iRXFIFOBI        : std_logic;                        -- Break interrupt from FIFO

    -- UART transmitter signals
    signal iSOUT            : std_logic;                        -- Transmitter output
    signal iTXStart         : std_logic;                        -- Start transmitter
    signal iTXClear         : std_logic;                        -- Clear transmitter status
    signal iTXFinished      : std_logic;                        -- TX finished, character transmitted
    signal iTXRunning       : std_logic;                        -- TX in progress

    -- UART receiver signals
    signal iSINr            : std_logic;                        -- Synchronized SIN input
    signal iSIN             : std_logic;                        -- Receiver input
    signal iRXFinished      : std_logic;                        -- RX finished, character received
    signal iRXClear         : std_logic;                        -- Clear receiver status
    signal iRXData          : std_logic_vector(7 downto 0);     -- RX data
    signal iRXPE            : std_logic;                        -- RX parity error
    signal iRXFE            : std_logic;                        -- RX frame error
    signal iRXBI            : std_logic;                        -- RX break interrupt

    -- UART control signals
    signal iFERE            : std_logic;                        -- Frame error detected
    signal iPERE            : std_logic;                        -- Parity error detected
    signal iBIRE            : std_logic;                        -- Break interrupt detected
    signal iFECounter       : integer range 0 to 64;            -- FIFO error counter
    signal iFEIncrement     : std_logic;                        -- FIFO error counter increment
    signal iFEDecrement     : std_logic;                        -- FIFO error counter decrement
    signal iRDAInterrupt    : std_logic;                        -- Receiver data available interrupt (DA or FIFO trigger level)
    signal iTimeoutCount    : unsigned(5 downto 0);             -- Character timeout counter (FIFO mode)
    signal iCharTimeout     : std_logic;                        -- Character timeout indication (FIFO mode)
    signal iLSR_THRERE      : std_logic;                        -- LSR THRE rising edge for interrupt generation
    signal iTHRInterrupt    : std_logic;                        -- Transmitter holding register empty interrupt
    signal iTXEnable        : std_logic;                        -- Transmitter enable signal
    signal iRTS             : std_logic;                        -- Internal RTS signal with/without automatic flow control


begin

    -- Global device signals
    iWrite <= '1' when PSEL = '1' and PENABLE = '1' and PWRITE = '1' else '0';
    iRead  <= '1' when PSEL = '1' and PENABLE = '1' and PWRITE = '0' else '0';
    iRST   <= '1' when RSTN = '0' else '0';

    -- UART registers read/write signals
    iRBRRead  <= '1' when iRead  = '1' and PADDR = "000" and iLCR_DLAB = '0' else '0';
    iTHRWrite <= '1' when iWrite = '1' and PADDR = "000" and iLCR_DLAB = '0' else '0';
    iDLLWrite <= '1' when iWrite = '1' and PADDR = "000" and iLCR_DLAB = '1' else '0';
    iDLMWrite <= '1' when iWrite = '1' and PADDR = "001" and iLCR_DLAB = '1' else '0';
    iIERWrite <= '1' when iWrite = '1' and PADDR = "001" and iLCR_DLAB = '0' else '0';
    iIIRRead  <= '1' when iRead  = '1' and PADDR = "010" else '0';
    iFCRWrite <= '1' when iWrite = '1' and PADDR = "010" else '0';
    iLCRWrite <= '1' when iWrite = '1' and PADDR = "011" else '0';
    iMCRWrite <= '1' when iWrite = '1' and PADDR = "100" else '0';
    iLSRRead  <= '1' when iRead  = '1' and PADDR = "101" else '0';
    iMSRRead  <= '1' when iRead  = '1' and PADDR = "110" else '0';
    iSCRWrite <= '1' when iWrite = '1' and PADDR = "111" else '0';

    -- Async. input synchronization
    UART_IS_SIN: slib_input_sync port map (CLK, iRST, SIN,  iSINr);
    UART_IS_CTS: slib_input_sync port map (CLK, iRST, CTSN, iCTSNs);
    UART_IS_DSR: slib_input_sync port map (CLK, iRST, DSRN, iDSRNs);
    UART_IS_DCD: slib_input_sync port map (CLK, iRST, DCDN, iDCDNs);
    UART_IS_RI:  slib_input_sync port map (CLK, iRST, RIN,  iRINs);

    -- Input filter for UART control signals
    UART_IF_CTS: slib_input_filter generic map (SIZE => 2) port map (CLK, iRST, iBaudtick2x, iCTSNs, iCTSn);
    UART_IF_DSR: slib_input_filter generic map (SIZE => 2) port map (CLK, iRST, iBaudtick2x, iDSRNs, iDSRn);
    UART_IF_DCD: slib_input_filter generic map (SIZE => 2) port map (CLK, iRST, iBaudtick2x, iDCDNs, iDCDn);
    UART_IF_RI:  slib_input_filter generic map (SIZE => 2) port map (CLK, iRST, iBaudtick2x, iRINs, iRIn);


    -- Divisor latch register
    UART_DLR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iDLL <= (others => '0');
            iDLM <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (iDLLWrite = '1') then
                iDLL <= PWDATA(7 downto 0);
            end if;
            if (iDLMWrite = '1') then
                iDLM <= PWDATA(7 downto 0);
            end if;
        end if;
    end process;

    -- Interrupt enable register
    UART_IER: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iIER(3 downto 0) <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (iIERWrite = '1') then
                iIER(3 downto 0) <= PWDATA(3 downto 0);
            end if;
        end if;
    end process;

    iIER_ERBI   <= iIER(0);
    iIER_ETBEI  <= iIER(1);
    iIER_ELSI   <= iIER(2);
    iIER_EDSSI  <= iIER(3);
    iIER(7 downto 4) <= (others => '0');

    -- Interrupt control and IIR
    UART_IIC: uart_interrupt port map (CLK => CLK,
                                       RST => iRST,
                                       IER => iIER(3 downto 0),
                                       LSR => iLSR(4 downto 0),
                                       THI => iTHRInterrupt,
                                       RDA => iRDAInterrupt,
                                       CTI => iCharTimeout,
                                       AFE => iMCR_AFE,
                                       MSR => iMSR(3 downto 0),
                                       IIR => iIIR(3 downto 0),
                                       INT => INT
                                      );
    -- THR empty interrupt
    UART_IIC_THRE_ED: slib_edge_detect port map (CLK => CLK, RST => iRST, D => iLSR_THRE, RE => iLSR_THRERE);
    UART_IIC_THREI: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iTHRInterrupt <= '0';
        elsif (CLK'event and CLK = '1') then
            if (iLSR_THRERE = '1' or iFCR_TXFIFOReset = '1' or (iIERWrite = '1' and PWDATA(1) = '1' and iLSR_THRE = '1')) then
                iTHRInterrupt <= '1';           -- Set on THRE, TX FIFO reset (FIFO enable) or ETBEI enable
            elsif ((iIIRRead = '1' and iIIR(3 downto 1) = "001") or iTHRWrite = '1') then
                iTHRInterrupt <= '0';           -- Clear on IIR read (if source of interrupt) or THR write
            end if;
        end if;
    end process;

    iRDAInterrupt <= '1' when (iFCR_FIFOEnable = '0' and iLSR_DR = '1') or
                              (iFCR_FIFOEnable = '1' and iRXFIFOTrigger = '1') else '0';
    iIIR_PI     <= iIIR(0);
    iIIR_ID0    <= iIIR(1);
    iIIR_ID1    <= iIIR(2);
    iIIR_ID2    <= iIIR(3);
    iIIR_FIFO64 <= iIIR(5);
    iIIR(4)  <= '0';
    iIIR(5)  <= iFCR_FIFO64E when iFCR_FIFOEnable = '1' else '0';
    iIIR(6)  <= iFCR_FIFOEnable;
    iIIR(7)  <= iFCR_FIFOEnable;

    -- Character timeout indication
    UART_CTI: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iTimeoutCount <= (others => '0');
            iCharTimeout  <= '0';
        elsif (CLK'event and CLK = '1') then
            if (iRXFIFOEmpty = '1' or iRBRRead = '1' or iRXFIFOWrite = '1') then
                iTimeoutCount <= (others => '0');
            elsif (iRXFIFOEmpty = '0' and iBaudtick2x = '1' and iTimeoutCount(5) = '0') then
                iTimeoutCount <= iTimeoutCount + 1;
            end if;

            -- Timeout indication
            if (iFCR_FIFOEnable = '1') then
                if (iRBRRead = '1') then
                    iCharTimeout <= '0';
                elsif (iTimeoutCount(5) = '1') then
                    iCharTimeout <= '1';
                end if;
            else
                iCharTimeout <= '0';
            end if;
        end if;
    end process;

    -- FIFO control register
    UART_FCR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iFCR_FIFOEnable     <= '0';
            iFCR_RXFIFOReset    <= '0';
            iFCR_TXFIFOReset    <= '0';
            iFCR_DMAMode        <= '0';
            iFCR_FIFO64E        <= '0';
            iFCR_RXTrigger      <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            -- FIFO reset pulse only
            iFCR_RXFIFOReset <= '0';
            iFCR_TXFIFOReset <= '0';

            if (iFCRWrite = '1') then
                iFCR_FIFOEnable <= PWDATA(0);
                iFCR_DMAMode    <= PWDATA(3);
                iFCR_RXTrigger  <= PWDATA(7 downto 6);

                if (iLCR_DLAB = '1') then
                    iFCR_FIFO64E    <= PWDATA(5);
                end if;

                -- RX FIFO reset control, reset on FIFO enable/disable
                if (PWDATA(1) = '1' or (iFCR_FIFOEnable = '0' and PWDATA(0) = '1') or (iFCR_FIFOEnable = '1' and PWDATA(0) = '0')) then
                    iFCR_RXFIFOReset <= '1';
                end if;
                -- TX FIFO reset control, reset on FIFO enable/disable
                if (PWDATA(2) = '1' or (iFCR_FIFOEnable = '0' and PWDATA(0) = '1') or (iFCR_FIFOEnable = '1' and PWDATA(0) = '0')) then
                    iFCR_TXFIFOReset <= '1';
                end if;
            end if;
        end if;
    end process;

    iFCR(0) <= iFCR_FIFOEnable;
    iFCR(1) <= iFCR_RXFIFOReset;
    iFCR(2) <= iFCR_TXFIFOReset;
    iFCR(3) <= iFCR_DMAMode;
    iFCR(4) <= '0';
    iFCR(5) <= iFCR_FIFO64E;
    iFCR(7 downto 6) <= iFCR_RXTrigger;

    -- Line control register
    UART_LCR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iLCR <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (iLCRWrite = '1') then
                iLCR <= PWDATA(7 downto 0);
            end if;
        end if;
    end process;

    iLCR_WLS    <= iLCR(1 downto 0);
    iLCR_STB    <= iLCR(2);
    iLCR_PEN    <= iLCR(3);
    iLCR_EPS    <= iLCR(4);
    iLCR_SP     <= iLCR(5);
    iLCR_BC     <= iLCR(6);
    iLCR_DLAB   <= iLCR(7);

    -- Modem control register
    UART_MCR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iMCR(5 downto 0) <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (iMCRWrite = '1') then
                iMCR(5 downto 0) <= PWDATA(5 downto 0);
            end if;
        end if;
    end process;

    iMCR_DTR    <= iMCR(0);
    iMCR_RTS    <= iMCR(1);
    iMCR_OUT1   <= iMCR(2);
    iMCR_OUT2   <= iMCR(3);
    iMCR_LOOP   <= iMCR(4);
    iMCR_AFE    <= iMCR(5);
    iMCR(6)     <= '0';
    iMCR(7)     <= '0';

    -- Line status register
    UART_LSR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iLSR_OE      <= '0';
            iLSR_PE      <= '0';
            iLSR_FE      <= '0';
            iLSR_BI      <= '0';
            iFECounter   <= 0;
            iLSR_FIFOERR <= '0';
        elsif (CLK'event and CLK = '1') then
            -- Overrun error
            if ((iFCR_FIFOEnable = '0' and iLSR_DR = '1' and iRXFinished = '1') or
                (iFCR_FIFOEnable = '1' and iRXFIFOFull  = '1' and iRXFinished = '1')) then
                iLSR_OE <= '1';
            elsif (iLSRRead = '1') then
                iLSR_OE <= '0';
            end if;
            -- Parity error
            if (iPERE = '1') then
                iLSR_PE <= '1';
            elsif (iLSRRead = '1') then
                iLSR_PE <= '0';
            end if;
            -- Frame error
            if (iFERE = '1') then
                iLSR_FE <= '1';
            elsif (iLSRRead = '1') then
                iLSR_FE <= '0';
            end if;
            -- Break interrupt
            if (iBIRE = '1') then
                iLSR_BI <= '1';
            elsif (iLSRRead = '1') then
                iLSR_BI <= '0';
            end if;

            -- FIFO error
            -- Datasheet: Cleared by LSR read when no subsequent errors in FIFO
            -- Observed:  Cleared when no subsequent errors in FIFO
            if (iFECounter /= 0) then
                iLSR_FIFOERR <= '1';
            --elsif (iLSRRead = '1' and iFECounter = 0 and not (iRXFIFOEmpty = '0' and iRXFIFOQ(10 downto 8) /= "000")) then
            elsif (iRXFIFOEmpty = '1' or iRXFIFOQ(10 downto 8) = "000") then
                iLSR_FIFOERR <= '0';
            end if;

            -- FIFO error counter
            if (iRXFIFOClear = '1') then
                iFECounter <= 0;
            else
                if (iFEIncrement = '1' and iFEDecrement = '0') then
                    iFECounter <= iFECounter + 1;
                elsif (iFEIncrement = '0' and iFEDecrement = '1') then
                    iFECounter <= iFECounter - 1;
                end if;
            end if;
        end if;
    end process;

    iRXFIFOPE <= '1' when iRXFIFOEmpty = '0' and iRXFIFOQ(8)  = '1' else '0';
    iRXFIFOFE <= '1' when iRXFIFOEmpty = '0' and iRXFIFOQ(9)  = '1' else '0';
    iRXFIFOBI <= '1' when iRXFIFOEmpty = '0' and iRXFIFOQ(10) = '1' else '0';
    UART_PEDET: slib_edge_detect port map (CLK, iRST, iRXFIFOPE, iPERE);
    UART_FEDET: slib_edge_detect port map (CLK, iRST, iRXFIFOFE, iFERE);
    UART_BIDET: slib_edge_detect port map (CLK, iRST, iRXFIFOBI, iBIRE);
    iFEIncrement    <= '1' when iRXFIFOWrite = '1' and iRXFIFOD(10 downto 8) /= "000" else '0';
    iFEDecrement    <= '1' when iFECounter /= 0 and iRXFIFOEmpty = '0' and (iPERE = '1' or iFERE = '1' or iBIRE = '1') else '0';

    iLSR(0)         <= iLSR_DR;
    iLSR(1)         <= iLSR_OE;
    iLSR(2)         <= iLSR_PE;
    iLSR(3)         <= iLSR_FE;
    iLSR(4)         <= iLSR_BI;
    iLSR(5)         <= iLSR_THRNF;
    iLSR(6)         <= iLSR_TEMT;
    iLSR(7)         <= '1' when iFCR_FIFOEnable = '1' and iLSR_FIFOERR = '1' else '0';
    iLSR_DR         <= '1' when iRXFIFOEmpty = '0' or iRXFIFOWrite = '1' else '0';
    iLSR_THRE       <= '1' when iTXFIFOEmpty = '1' else '0';
    iLSR_TEMT       <= '1' when iTXRunning = '0' and iLSR_THRE = '1' else '0';
    iLSR_THRNF      <= '1' when ((iFCR_FIFOEnable = '0' and iTXFIFOEmpty = '1') or (iFCR_FIFOEnable = '1' and iTXFIFOFull = '0')) else '0';

    -- Modem status register
    iMSR_CTS <= '1' when (iMCR_LOOP = '1' and iRTS = '1')      or (iMCR_LOOP = '0' and iCTSn = '0') else '0';
    iMSR_DSR <= '1' when (iMCR_LOOP = '1' and iMCR_DTR = '1')  or (iMCR_LOOP = '0' and iDSRn = '0') else '0';
    iMSR_RI  <= '1' when (iMCR_LOOP = '1' and iMCR_OUT1 = '1') or (iMCR_LOOP = '0' and iRIn  = '0') else '0';
    iMSR_DCD <= '1' when (iMCR_LOOP = '1' and iMCR_OUT2 = '1') or (iMCR_LOOP = '0' and iDCDn = '0') else '0';

    -- Edge detection for CTS, DSR, DCD and RI
    UART_ED_CTS: slib_edge_detect port map (CLK => CLK, RST => iRST, D => iMSR_CTS, RE => iCTSnRE, FE => iCTSnFE);
    UART_ED_DSR: slib_edge_detect port map (CLK => CLK, RST => iRST, D => iMSR_DSR, RE => iDSRnRE, FE => iDSRnFE);
    UART_ED_RI:  slib_edge_detect port map (CLK => CLK, RST => iRST, D => iMSR_RI,  RE => iRInRE,  FE => iRInFE);
    UART_ED_DCD: slib_edge_detect port map (CLK => CLK, RST => iRST, D => iMSR_DCD, RE => iDCDnRE, FE => iDCDnFE);

    UART_MSR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iMSR_dCTS <= '0';
            iMSR_dDSR <= '0';
            iMSR_TERI <= '0';
            iMSR_dDCD <= '0';
        elsif (CLK'event and CLK = '1') then
            -- Delta CTS
            if (iCTSnRE = '1' or iCTSnFE = '1') then
                iMSR_dCTS <= '1';
            elsif (iMSRRead = '1') then
                iMSR_dCTS <= '0';
            end if;
            -- Delta DSR
            if (iDSRnRE = '1' or iDSRnFE = '1') then
                iMSR_dDSR <= '1';
            elsif (iMSRRead = '1') then
                iMSR_dDSR <= '0';
            end if;
            -- Trailing edge RI
            if (iRInFE = '1') then
                iMSR_TERI <= '1';
            elsif (iMSRRead = '1') then
                iMSR_TERI <= '0';
            end if;
            -- Delta DCD
            if (iDCDnRE = '1' or iDCDnFE = '1') then
                iMSR_dDCD <= '1';
            elsif (iMSRRead = '1') then
                iMSR_dDCD <= '0';
            end if;
        end if;
    end process;

    iMSR(0)     <= iMSR_dCTS;
    iMSR(1)     <= iMSR_dDSR;
    iMSR(2)     <= iMSR_TERI;
    iMSR(3)     <= iMSR_dDCD;
    iMSR(4)     <= iMSR_CTS;
    iMSR(5)     <= iMSR_DSR;
    iMSR(6)     <= iMSR_RI;
    iMSR(7)     <= iMSR_DCD;

    -- Scratch register
    UART_SCR: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iSCR <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (iSCRWrite = '1') then
                iSCR <= PWDATA(7 downto 0);
            end if;
        end if;
    end process;


    -- Baudrate generator
    iBaudgenDiv <= iDLM & iDLL;
    UART_BG16: uart_baudgen port map (CLK         => CLK,
                                      RST         => iRST,
                                      CE          => '1',
                                      CLEAR       => '0',
                                      DIVIDER     => iBaudgenDiv,
                                      BAUDTICK    => iBaudtick16x
                                     );
    UART_BG2: slib_clock_div generic map (RATIO => 8)
                             port map    (CLK   => CLK,
                                          RST   => iRST,
                                          CE    => iBaudtick16x,
                                          Q     => iBaudtick2x
                                         );
    UART_RCLK: slib_edge_detect port map (CLK => CLK,
                                          RST => iRST,
                                          D   => iBAUDOUTN,
                                          RE  => iRCLK
                                         );

    -- Transmitter FIFO
    UART_TXFF: slib_fifo generic map (WIDTH => 8, SIZE_E => 6)
                         port map (CLK      => CLK,
                                   RST      => iRST,
                                   CLEAR    => iTXFIFOClear,
                                   WRITE    => iTXFIFOWrite,
                                   READ     => iTXFIFORead,
                                   D        => PWDATA(7 downto 0),
                                   Q        => iTXFIFOQ,
                                   EMPTY    => iTXFIFOEmpty,
                                   FULL     => iTXFIFO64Full,
                                   USAGE    => iTXFIFOUsage
                                  );
    -- Transmitter FIFO inputs
    iTXFIFO16Full <= iTXFIFOUsage(4);
    iTXFIFOFull   <= iTXFIFO16Full when iFCR_FIFO64E = '0' else iTXFIFO64Full;
    iTXFIFOWrite  <= '1' when ((iFCR_FIFOEnable = '0' and iTXFIFOEmpty = '1') or (iFCR_FIFOEnable = '1' and iTXFIFOFull = '0')) and iTHRWrite = '1' else '0';
    iTXFIFOClear  <= '1' when iFCR_TXFIFOReset = '1' else '0';

    -- Receiver FIFO
    UART_RXFF: slib_fifo generic map (WIDTH => 11, SIZE_E => 6)
                         port map (CLK      => CLK,
                                   RST      => iRST,
                                   CLEAR    => iRXFIFOClear,
                                   WRITE    => iRXFIFOWrite,
                                   READ     => iRXFIFORead,
                                   D        => iRXFIFOD,
                                   Q        => iRXFIFOQ,
                                   EMPTY    => iRXFIFOEmpty,
                                   FULL     => iRXFIFO64Full,
                                   USAGE    => iRXFIFOUsage
                                  );
    -- Receiver FIFO inputs
    iRXFIFORead          <= '1' when iRBRRead = '1' else '0';
    iRXFIFO16Full        <= iRXFIFOUsage(4);
    iRXFIFOFull          <= iRXFIFO16Full when iFCR_FIFO64E = '0' else iRXFIFO64Full;


    -- Receiver FIFO outputs
    iRBR                 <= iRXFIFOQ(7 downto 0);

    -- FIFO trigger level: 1, 4, 8, 14
    iRXFIFO16Trigger     <= '1' when (iFCR_RXTrigger = "00" and iRXFIFOEmpty = '0') or
                                     (iFCR_RXTrigger = "01" and (iRXFIFOUsage(2) = '1' or iRXFIFOUsage(3) = '1')) or
                                     (iFCR_RXTrigger = "10" and iRXFIFOUsage(3) = '1') or
                                     (iFCR_RXTrigger = "11" and iRXFIFOUsage(3) = '1' and iRXFIFOUsage(2) = '1' and iRXFIFOUsage(1) = '1') or
                                     iRXFIFO16Full = '1' else '0';
    -- FIFO 64 trigger level: 1, 16, 32, 56
    iRXFIFO64Trigger     <= '1' when (iFCR_RXTrigger = "00" and iRXFIFOEmpty = '0') or
                                     (iFCR_RXTrigger = "01" and (iRXFIFOUsage(4) = '1' or iRXFIFOUsage(5) = '1')) or
                                     (iFCR_RXTrigger = "10" and iRXFIFOUsage(5) = '1') or
                                     (iFCR_RXTrigger = "11" and iRXFIFOUsage(5) = '1' and iRXFIFOUsage(4) = '1' and iRXFIFOUsage(3) = '1') or
                                     iRXFIFO64Full = '1' else '0';
    iRXFIFOTrigger       <= iRXFIFO16Trigger when iFCR_FIFO64E = '0' else iRXFIFO64Trigger;

    -- Transmitter
    UART_TX: uart_transmitter port map (CLK         => CLK,
                                        RST         => iRST,
                                        TXCLK       => iBaudtick2x,
                                        TXSTART     => iTXStart,
                                        CLEAR       => iTXClear,
                                        WLS         => iLCR_WLS,
                                        STB         => iLCR_STB,
                                        PEN         => iLCR_PEN,
                                        EPS         => iLCR_EPS,
                                        SP          => iLCR_SP,
                                        BC          => iLCR_BC,
                                        DIN         => iTSR,
                                        TXFINISHED  => iTXFinished,
                                        SOUT        => iSOUT
                                       );
    iTXClear <= '0';

    -- Receiver
    UART_RX: uart_receiver    port map (CLK         => CLK,
                                        RST         => iRST,
                                        RXCLK       => iRCLK,
                                        RXCLEAR     => iRXClear,
                                        WLS         => iLCR_WLS,
                                        STB         => iLCR_STB,
                                        PEN         => iLCR_PEN,
                                        EPS         => iLCR_EPS,
                                        SP          => iLCR_SP,
                                        SIN         => iSIN,
                                        PE          => iRXPE,
                                        FE          => iRXFE,
                                        BI          => iRXBI,
                                        DOUT        => iRXData,
                                        RXFINISHED  => iRXFinished
                                       );
    iRXClear <= '0';
    iSIN <= iSINr when iMCR_LOOP = '0' else iSOUT;

    -- Transmitter enable signal
    -- TODO: Use iCTSNs instead of iMSR_CTS? Input filter increases delay for Auto-CTS recognition.
    iTXEnable <= '1' when iTXFIFOEmpty = '0' and (iMCR_AFE = '0' or (iMCR_AFE = '1' and iMSR_CTS = '1')) else '0';

    -- Transmitter process
    UART_TXPROC: process (CLK, iRST)
        type state_type is (IDLE, TXSTART, TXRUN, TXEND);
        variable State : state_type;
    begin
        if (iRST = '1') then
            State       := IDLE;
            iTSR        <= (others => '0');
            iTXStart    <= '0';
            iTXFIFORead <= '0';
            iTXRunning  <= '0';
        elsif (CLK'event and CLK = '1') then
            -- Defaults
            iTXStart    <= '0';
            iTXFIFORead <= '0';
            iTXRunning  <= '0';

            case State is
                when IDLE       =>  if (iTXEnable = '1') then
                                        iTXStart <= '1';            -- Start transmitter
                                        State := TXSTART;
                                    else
                                        State := IDLE;
                                    end if;
                when TXSTART    =>  iTSR <= iTXFIFOQ;
                                    iTXStart <= '1';                -- Start transmitter
                                    iTXFIFORead <= '1';             -- Increment TX FIFO read counter
                                    State := TXRUN;
                when TXRUN      =>  if (iTXFinished = '1') then     -- TX finished
                                        State := TXEND;
                                    else
                                        State := TXRUN;
                                    end if;
                                    iTXRunning <= '1';
                                    iTXStart   <= '1';
                when TXEND      =>  State := IDLE;
                when others     =>  State := IDLE;
            end case;
        end if;
    end process;

    -- Receiver process
    UART_RXPROC: process (CLK, iRST)
        type state_type is (IDLE, RXSAVE);
        variable State : state_type;
    begin
        if (iRST = '1') then
            State        := IDLE;
            iRXFIFOWrite <= '0';
            iRXFIFOClear <= '0';
            iRXFIFOD     <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            -- Defaults
            iRXFIFOWrite <= '0';
            iRXFIFOClear <= iFCR_RXFIFOReset;

            case State is
                when IDLE       =>  if (iRXFinished = '1') then     -- Receive finished
                                        iRXFIFOD <= iRXBI & iRXFE & iRXPE & iRXData;
                                        if (iFCR_FIFOEnable = '0') then
                                            iRXFIFOClear <= '1';    -- Non-FIFO mode
                                        end if;
                                        State := RXSAVE;
                                    else
                                        State := IDLE;
                                    end if;
                when RXSAVE    =>   if (iFCR_FIFOEnable = '0') then
                                        iRXFIFOWrite <= '1';        -- Non-FIFO mode: Overwrite
                                    elsif (iRXFIFOFull = '0') then
                                        iRXFIFOWrite <= '1';        -- FIFO mode
                                    end if;
                                    State := IDLE;
                when others     =>  State := IDLE;
            end case;
        end if;
    end process;

    -- Automatic flow control
    UART_AFC: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iRTS <= '0';
        elsif (CLK'event and CLK = '1') then
            if (iMCR_RTS = '0' or (iMCR_AFE = '1' and iRXFIFOTrigger = '1')) then
                -- Deassert when MCR_RTS is not set or AFC is enabled and the RX FIFO trigger level is reached
                iRTS <= '0';
            elsif (iMCR_RTS = '1' and (iMCR_AFE = '0' or (iMCR_AFE = '1' and iRXFIFOEmpty = '1'))) then
                -- Assert when MCR_RTS is set and AFC is disabled or when AFC is enabled and the RX FIFO is empty
                iRTS <= '1';
            end if;
        end if;
    end process;

    -- Output registers
    UART_OUTREGS: process (CLK, iRST)
    begin
        if (iRST = '1') then
            iBAUDOUTN <= '1';
            OUT1N    <= '1';
            OUT2N    <= '1';
            RTSN     <= '1';
            DTRN     <= '1';
            SOUT     <= '1';
        elsif (CLK'event and CLK = '1') then
            -- Default values
            iBAUDOUTN <= '0';
            OUT1N    <= '0';
            OUT2N    <= '0';
            RTSN     <= '0';
            DTRN     <= '0';
            SOUT     <= '0';

            -- BAUDOUTN
            if (iBaudtick16x = '0') then
                iBAUDOUTN <= '1';
            end if;
            -- OUT1N
            if (iMCR_LOOP = '1' or iMCR_OUT1 = '0') then
                OUT1N <= '1';
            end if;
            -- OUT2N
            if (iMCR_LOOP = '1' or iMCR_OUT2 = '0') then
                OUT2N <= '1';
            end if;
            -- RTS
            if (iMCR_LOOP = '1' or iRTS = '0') then
                RTSN <= '1';
            end if;
            -- DTR
            if (iMCR_LOOP = '1' or iMCR_DTR = '0') then
                DTRN <= '1';
            end if;
            -- SOUT
            if (iMCR_LOOP = '1' or iSOUT = '1') then
                SOUT <= '1';
            end if;
        end if;
    end process;


    -- UART data output
    UART_DOUT: process (PADDR, iLCR_DLAB, iRBR, iDLL, iDLM, iIER, iIIR, iLCR, iMCR, iLSR, iMSR, iSCR)
    begin
        case PADDR is
            when "000"  =>  if (iLCR_DLAB = '0') then
                                PRDATA(7 downto 0) <= iRBR;
                            else
                                PRDATA(7 downto 0) <= iDLL;
                            end if;
            when "001"  =>  if (iLCR_DLAB = '0') then
                                PRDATA(7 downto 0) <= iIER;
                            else
                                PRDATA(7 downto 0) <= iDLM;
                            end if;
            when "010"  =>  PRDATA(7 downto 0) <= iIIR;
            when "011"  =>  PRDATA(7 downto 0) <= iLCR;
            when "100"  =>  PRDATA(7 downto 0) <= iMCR;
            when "101"  =>  PRDATA(7 downto 0) <= iLSR;
            when "110"  =>  PRDATA(7 downto 0) <= iMSR;
            when "111"  =>  PRDATA(7 downto 0) <= iSCR;
            when others =>  PRDATA(7 downto 0) <= iRBR;
        end case;
    end process;

    PRDATA(31 downto 8) <= (others => '0');
    PREADY              <= '1';
    PSLVERR             <= '0';   

end rtl;


