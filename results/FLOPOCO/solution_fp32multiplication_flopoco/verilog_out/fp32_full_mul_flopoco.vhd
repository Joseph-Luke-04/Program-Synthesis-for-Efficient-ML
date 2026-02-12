library ieee;
use ieee.std_logic_1164.all;

entity fp32_full_mul_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        a         : in  std_logic_vector(31 downto 0);
        b         : in  std_logic_vector(31 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_full_mul_flopoco is
    component fp32_fma_flopoco is
        port (
            clk      : in  std_logic;
            A        : in  std_logic_vector(31 downto 0);
            B        : in  std_logic_vector(31 downto 0);
            C        : in  std_logic_vector(31 downto 0);
            negateAB : in  std_logic;
            negateC  : in  std_logic;
            RndMode  : in  std_logic_vector(1 downto 0);
            R        : out std_logic_vector(31 downto 0)
        );
    end component;

    -- FloPoCo reports 4 pipeline cycles for this IEEEFPFMA instance.
    signal donepipe : std_logic_vector(4 downto 0) := (others => '0');
begin
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                donepipe <= (others => '0');
            else
                donepipe <= donepipe(3 downto 0) & ap_start;
            end if;
        end if;
    end process;

    ap_done  <= donepipe(4);
    ap_idle  <= '1';
    ap_ready <= '1';

    -- Use FMA as multiplier: R = A * B + 0.0
    -- RndMode "00" corresponds to default rounding mode for this operator.
    u_fp32_fma_flopoco : fp32_fma_flopoco
        port map (
            clk      => ap_clk,
            A        => a,
            B        => b,
            C        => (others => '0'),
            negateAB => '0',
            negateC  => '0',
            RndMode  => "00",
            R        => ap_return
        );
end architecture;
