library ieee;
use ieee.std_logic_1164.all;

entity fp32_sum_flopoco is
    port (
        ap_clk    : in  std_logic;
        ap_rst    : in  std_logic;
        ap_start  : in  std_logic;
        ap_done   : out std_logic;
        ap_idle   : out std_logic;
        ap_ready  : out std_logic;
        s1        : in  std_logic_vector(0 downto 0);
        e1        : in  std_logic_vector(7 downto 0);
        m1        : in  std_logic_vector(22 downto 0);
        s2        : in  std_logic_vector(0 downto 0);
        e2        : in  std_logic_vector(7 downto 0);
        m2        : in  std_logic_vector(22 downto 0);
        ap_return : out std_logic_vector(31 downto 0)
    );
end entity;

architecture rtl of fp32_sum_flopoco is
    component fp32_add_flopoco is
        port (
            clk : in  std_logic;
            X   : in  std_logic_vector(31 downto 0);
            Y   : in  std_logic_vector(31 downto 0);
            R   : out std_logic_vector(31 downto 0)
        );
    end component;

    signal x_pack    : std_logic_vector(31 downto 0);
    signal y_pack    : std_logic_vector(31 downto 0);
    signal r_pack    : std_logic_vector(31 downto 0);
    signal done_pipe : std_logic_vector(7 downto 0) := (others => '0');
begin
    -- FloPoCo IEEEFPAdd here is a 7-cycle pipeline at 250MHz.
    process(ap_clk)
    begin
        if rising_edge(ap_clk) then
            if ap_rst = '1' then
                done_pipe <= (others => '0');
            else
                done_pipe <= done_pipe(6 downto 0) & ap_start;
            end if;
        end if;
    end process;

    x_pack <= s1 & e1 & m1;
    y_pack <= s2 & e2 & m2;

    ap_done   <= done_pipe(7);
    ap_idle   <= '1';
    ap_ready  <= '1';
    ap_return <= r_pack;

    u_fp32_add_flopoco : fp32_add_flopoco
        port map (
            clk => ap_clk,
            X   => x_pack,
            Y   => y_pack,
            R   => r_pack
        );
end architecture;
