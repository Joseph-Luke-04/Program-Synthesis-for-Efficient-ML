--------------------------------------------------------------------------------
--                RightShifterSticky26_by_max_25_Freq250_uid4
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Bogdan Pasca (2008-2011), Florent de Dinechin (2008-2019)
--------------------------------------------------------------------------------
-- Pipeline depth: 2 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X S
-- Output signals: R Sticky
--  approx. input signal timings: X: (c1, 0.610000ns)S: (c1, 2.488000ns)
--  approx. output signal timings: R: (c2, 0.254000ns)Sticky: (c2, 2.978000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity RightShifterSticky26_by_max_25_Freq250_uid4 is
    port (clk : in std_logic;
          X : in  std_logic_vector(25 downto 0);
          S : in  std_logic_vector(4 downto 0);
          R : out  std_logic_vector(25 downto 0);
          Sticky : out  std_logic   );
end entity;

architecture arch of RightShifterSticky26_by_max_25_Freq250_uid4 is
signal ps, ps_d1 :  std_logic_vector(4 downto 0);
   -- timing of ps: (c1, 2.488000ns)
signal Xpadded :  std_logic_vector(25 downto 0);
   -- timing of Xpadded: (c1, 0.610000ns)
signal level5 :  std_logic_vector(25 downto 0);
   -- timing of level5: (c1, 0.610000ns)
signal stk4, stk4_d1 :  std_logic;
   -- timing of stk4: (c1, 3.197500ns)
signal level4, level4_d1 :  std_logic_vector(25 downto 0);
   -- timing of level4: (c1, 2.488000ns)
signal stk3 :  std_logic;
   -- timing of stk3: (c2, 0.396500ns)
signal level3, level3_d1 :  std_logic_vector(25 downto 0);
   -- timing of level3: (c1, 3.112000ns)
signal stk2 :  std_logic;
   -- timing of stk2: (c2, 1.049000ns)
signal level2, level2_d1 :  std_logic_vector(25 downto 0);
   -- timing of level2: (c1, 3.112000ns)
signal stk1 :  std_logic;
   -- timing of stk1: (c2, 1.701500ns)
signal level1 :  std_logic_vector(25 downto 0);
   -- timing of level1: (c2, 0.254000ns)
signal stk0 :  std_logic;
   -- timing of stk0: (c2, 2.354000ns)
signal level0 :  std_logic_vector(25 downto 0);
   -- timing of level0: (c2, 0.254000ns)
signal stk :  std_logic;
   -- timing of stk: (c2, 2.978000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            ps_d1 <=  ps;
            stk4_d1 <=  stk4;
            level4_d1 <=  level4;
            level3_d1 <=  level3;
            level2_d1 <=  level2;
         end if;
      end process;
   ps<= S;
   Xpadded <= X;
   level5<= Xpadded;
   stk4 <= '1' when (level5(15 downto 0)/="0000000000000000" and ps(4)='1')   else '0';
   level4 <=  level5 when  ps(4)='0'    else (15 downto 0 => '0') & level5(25 downto 16);
   stk3 <= '1' when (level4_d1(7 downto 0)/="00000000" and ps_d1(3)='1') or stk4_d1 ='1'   else '0';
   level3 <=  level4 when  ps(3)='0'    else (7 downto 0 => '0') & level4(25 downto 8);
   stk2 <= '1' when (level3_d1(3 downto 0)/="0000" and ps_d1(2)='1') or stk3 ='1'   else '0';
   level2 <=  level3 when  ps(2)='0'    else (3 downto 0 => '0') & level3(25 downto 4);
   stk1 <= '1' when (level2_d1(1 downto 0)/="00" and ps_d1(1)='1') or stk2 ='1'   else '0';
   level1 <=  level2_d1 when  ps_d1(1)='0'    else (1 downto 0 => '0') & level2_d1(25 downto 2);
   stk0 <= '1' when (level1(0 downto 0)/="0" and ps_d1(0)='1') or stk1 ='1'   else '0';
   level0 <=  level1 when  ps_d1(0)='0'    else (0 downto 0 => '0') & level1(25 downto 1);
   stk <= stk0;
   R <= level0;
   Sticky <= stk;
end architecture;

--------------------------------------------------------------------------------
--                          IntAdder_27_Freq250_uid6
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Bogdan Pasca, Florent de Dinechin (2008-2016)
--------------------------------------------------------------------------------
-- Pipeline depth: 3 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X Y Cin
-- Output signals: R
--  approx. input signal timings: X: (c1, 0.610000ns)Y: (c2, 0.878000ns)Cin: (c2, 2.978000ns)
--  approx. output signal timings: R: (c3, 1.434000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity IntAdder_27_Freq250_uid6 is
    port (clk : in std_logic;
          X : in  std_logic_vector(26 downto 0);
          Y : in  std_logic_vector(26 downto 0);
          Cin : in  std_logic;
          R : out  std_logic_vector(26 downto 0)   );
end entity;

architecture arch of IntAdder_27_Freq250_uid6 is
signal Cin_1, Cin_1_d1 :  std_logic;
   -- timing of Cin_1: (c2, 2.978000ns)
signal X_1, X_1_d1, X_1_d2 :  std_logic_vector(27 downto 0);
   -- timing of X_1: (c1, 0.610000ns)
signal Y_1, Y_1_d1 :  std_logic_vector(27 downto 0);
   -- timing of Y_1: (c2, 0.878000ns)
signal S_1 :  std_logic_vector(27 downto 0);
   -- timing of S_1: (c3, 1.434000ns)
signal R_1 :  std_logic_vector(26 downto 0);
   -- timing of R_1: (c3, 1.434000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            Cin_1_d1 <=  Cin_1;
            X_1_d1 <=  X_1;
            X_1_d2 <=  X_1_d1;
            Y_1_d1 <=  Y_1;
         end if;
      end process;
   Cin_1 <= Cin;
   X_1 <= '0' & X(26 downto 0);
   Y_1 <= '0' & Y(26 downto 0);
   S_1 <= X_1_d2 + Y_1_d1 + Cin_1_d1;
   R_1 <= S_1(26 downto 0);
   R <= R_1 ;
end architecture;

--------------------------------------------------------------------------------
--                            LZC_26_Freq250_uid8
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Florent de Dinechin, Bogdan Pasca (2007)
--------------------------------------------------------------------------------
-- Pipeline depth: 4 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: I
-- Output signals: O
--  approx. input signal timings: I: (c3, 1.434000ns)
--  approx. output signal timings: O: (c4, 2.491000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity LZC_26_Freq250_uid8 is
    port (clk : in std_logic;
          I : in  std_logic_vector(25 downto 0);
          O : out  std_logic_vector(4 downto 0)   );
end entity;

architecture arch of LZC_26_Freq250_uid8 is
signal level5 :  std_logic_vector(30 downto 0);
   -- timing of level5: (c3, 1.434000ns)
signal digit4, digit4_d1 :  std_logic;
   -- timing of digit4: (c3, 2.143500ns)
signal level4, level4_d1 :  std_logic_vector(14 downto 0);
   -- timing of level4: (c3, 2.767500ns)
signal digit3, digit3_d1 :  std_logic;
   -- timing of digit3: (c3, 3.448500ns)
signal level3 :  std_logic_vector(6 downto 0);
   -- timing of level3: (c4, 0.590500ns)
signal digit2 :  std_logic;
   -- timing of digit2: (c4, 1.243000ns)
signal level2 :  std_logic_vector(2 downto 0);
   -- timing of level2: (c4, 1.867000ns)
signal lowBits :  std_logic_vector(1 downto 0);
   -- timing of lowBits: (c4, 2.491000ns)
signal outHighBits :  std_logic_vector(2 downto 0);
   -- timing of outHighBits: (c4, 1.243000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            digit4_d1 <=  digit4;
            level4_d1 <=  level4;
            digit3_d1 <=  digit3;
         end if;
      end process;
   -- pad input to the next power of two minus 1
   level5 <= I & "11111";
   -- Main iteration for large inputs
   digit4<= '1' when level5(30 downto 15) = "0000000000000000" else '0';
   level4<= level5(14 downto 0) when digit4='1' else level5(30 downto 16);
   digit3<= '1' when level4(14 downto 7) = "00000000" else '0';
   level3<= level4_d1(6 downto 0) when digit3_d1='1' else level4_d1(14 downto 8);
   digit2<= '1' when level3(6 downto 3) = "0000" else '0';
   level2<= level3(2 downto 0) when digit2='1' else level3(6 downto 4);
   -- Finish counting with one LUT
   with level2  select  lowBits <= 
      "11" when "000",
      "10" when "001",
      "01" when "010",
      "01" when "011",
      "00" when others;
   outHighBits <= digit4_d1 & digit3_d1 & digit2 & "";
   O <= outHighBits & lowBits ;
end architecture;

--------------------------------------------------------------------------------
--                   LeftShifter27_by_max_26_Freq250_uid10
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Bogdan Pasca (2008-2011), Florent de Dinechin (2008-2019)
--------------------------------------------------------------------------------
-- Pipeline depth: 5 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X S
-- Output signals: R
--  approx. input signal timings: X: (c3, 1.434000ns)S: (c5, 0.887000ns)
--  approx. output signal timings: R: (c5, 2.855000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity LeftShifter27_by_max_26_Freq250_uid10 is
    port (clk : in std_logic;
          X : in  std_logic_vector(26 downto 0);
          S : in  std_logic_vector(4 downto 0);
          R : out  std_logic_vector(52 downto 0)   );
end entity;

architecture arch of LeftShifter27_by_max_26_Freq250_uid10 is
signal ps :  std_logic_vector(4 downto 0);
   -- timing of ps: (c5, 0.887000ns)
signal level0, level0_d1, level0_d2 :  std_logic_vector(26 downto 0);
   -- timing of level0: (c3, 1.434000ns)
signal level1 :  std_logic_vector(27 downto 0);
   -- timing of level1: (c5, 0.887000ns)
signal level2 :  std_logic_vector(29 downto 0);
   -- timing of level2: (c5, 1.811000ns)
signal level3 :  std_logic_vector(33 downto 0);
   -- timing of level3: (c5, 1.811000ns)
signal level4 :  std_logic_vector(41 downto 0);
   -- timing of level4: (c5, 2.855000ns)
signal level5 :  std_logic_vector(57 downto 0);
   -- timing of level5: (c5, 2.855000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            level0_d1 <=  level0;
            level0_d2 <=  level0_d1;
         end if;
      end process;
   ps<= S;
   level0<= X;
   level1<= level0_d2 & (0 downto 0 => '0') when ps(0)= '1' else     (0 downto 0 => '0') & level0_d2;
   level2<= level1 & (1 downto 0 => '0') when ps(1)= '1' else     (1 downto 0 => '0') & level1;
   level3<= level2 & (3 downto 0 => '0') when ps(2)= '1' else     (3 downto 0 => '0') & level2;
   level4<= level3 & (7 downto 0 => '0') when ps(3)= '1' else     (7 downto 0 => '0') & level3;
   level5<= level4 & (15 downto 0 => '0') when ps(4)= '1' else     (15 downto 0 => '0') & level4;
   R <= level5(52 downto 0);
end architecture;

--------------------------------------------------------------------------------
--                         IntAdder_31_Freq250_uid13
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Bogdan Pasca, Florent de Dinechin (2008-2016)
--------------------------------------------------------------------------------
-- Pipeline depth: 6 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X Y Cin
-- Output signals: R
--  approx. input signal timings: X: (c5, 2.855000ns)Y: (c0, 0.000000ns)Cin: (c6, 1.251000ns)
--  approx. output signal timings: R: (c6, 3.189000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity IntAdder_31_Freq250_uid13 is
    port (clk : in std_logic;
          X : in  std_logic_vector(30 downto 0);
          Y : in  std_logic_vector(30 downto 0);
          Cin : in  std_logic;
          R : out  std_logic_vector(30 downto 0)   );
end entity;

architecture arch of IntAdder_31_Freq250_uid13 is
signal Rtmp :  std_logic_vector(30 downto 0);
   -- timing of Rtmp: (c6, 3.189000ns)
signal X_d1 :  std_logic_vector(30 downto 0);
   -- timing of X: (c5, 2.855000ns)
signal Y_d1, Y_d2, Y_d3, Y_d4, Y_d5, Y_d6 :  std_logic_vector(30 downto 0);
   -- timing of Y: (c0, 0.000000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            X_d1 <=  X;
            Y_d1 <=  Y;
            Y_d2 <=  Y_d1;
            Y_d3 <=  Y_d2;
            Y_d4 <=  Y_d3;
            Y_d5 <=  Y_d4;
            Y_d6 <=  Y_d5;
         end if;
      end process;
   Rtmp <= X_d1 + Y_d6 + Cin;
   R <= Rtmp;
end architecture;

--------------------------------------------------------------------------------
--                              fp32_add_flopoco
--                       (IEEEFPAdd_8_23_Freq250_uid2)
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Florent de Dinechin, Valentin Huguet (2016)
--------------------------------------------------------------------------------
-- Pipeline depth: 7 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X Y
-- Output signals: R
--  approx. input signal timings: X: (c0, 0.000000ns)Y: (c0, 0.000000ns)
--  approx. output signal timings: R: (c7, 1.699000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity fp32_add_flopoco is
    port (clk : in std_logic;
          X : in  std_logic_vector(31 downto 0);
          Y : in  std_logic_vector(31 downto 0);
          R : out  std_logic_vector(31 downto 0)   );
end entity;

architecture arch of fp32_add_flopoco is
   component RightShifterSticky26_by_max_25_Freq250_uid4 is
      port ( clk : in std_logic;
             X : in  std_logic_vector(25 downto 0);
             S : in  std_logic_vector(4 downto 0);
             R : out  std_logic_vector(25 downto 0);
             Sticky : out  std_logic   );
   end component;

   component IntAdder_27_Freq250_uid6 is
      port ( clk : in std_logic;
             X : in  std_logic_vector(26 downto 0);
             Y : in  std_logic_vector(26 downto 0);
             Cin : in  std_logic;
             R : out  std_logic_vector(26 downto 0)   );
   end component;

   component LZC_26_Freq250_uid8 is
      port ( clk : in std_logic;
             I : in  std_logic_vector(25 downto 0);
             O : out  std_logic_vector(4 downto 0)   );
   end component;

   component LeftShifter27_by_max_26_Freq250_uid10 is
      port ( clk : in std_logic;
             X : in  std_logic_vector(26 downto 0);
             S : in  std_logic_vector(4 downto 0);
             R : out  std_logic_vector(52 downto 0)   );
   end component;

   component IntAdder_31_Freq250_uid13 is
      port ( clk : in std_logic;
             X : in  std_logic_vector(30 downto 0);
             Y : in  std_logic_vector(30 downto 0);
             Cin : in  std_logic;
             R : out  std_logic_vector(30 downto 0)   );
   end component;

signal expFracX :  std_logic_vector(30 downto 0);
   -- timing of expFracX: (c0, 0.000000ns)
signal expFracY :  std_logic_vector(30 downto 0);
   -- timing of expFracY: (c0, 0.000000ns)
signal expXmExpY :  std_logic_vector(8 downto 0);
   -- timing of expXmExpY: (c0, 1.368000ns)
signal expYmExpX :  std_logic_vector(8 downto 0);
   -- timing of expYmExpX: (c0, 1.368000ns)
signal swap :  std_logic;
   -- timing of swap: (c0, 1.596000ns)
signal newX, newX_d1, newX_d2, newX_d3 :  std_logic_vector(31 downto 0);
   -- timing of newX: (c0, 2.220000ns)
signal newY, newY_d1, newY_d2, newY_d3 :  std_logic_vector(31 downto 0);
   -- timing of newY: (c0, 2.220000ns)
signal expDiff, expDiff_d1 :  std_logic_vector(8 downto 0);
   -- timing of expDiff: (c0, 2.220000ns)
signal expNewX, expNewX_d1, expNewX_d2, expNewX_d3, expNewX_d4, expNewX_d5 :  std_logic_vector(7 downto 0);
   -- timing of expNewX: (c0, 2.220000ns)
signal expNewY, expNewY_d1 :  std_logic_vector(7 downto 0);
   -- timing of expNewY: (c0, 2.220000ns)
signal signNewX, signNewX_d1, signNewX_d2, signNewX_d3, signNewX_d4, signNewX_d5, signNewX_d6, signNewX_d7 :  std_logic;
   -- timing of signNewX: (c0, 2.220000ns)
signal signNewY, signNewY_d1, signNewY_d2, signNewY_d3, signNewY_d4, signNewY_d5, signNewY_d6, signNewY_d7 :  std_logic;
   -- timing of signNewY: (c0, 2.220000ns)
signal EffSub, EffSub_d1, EffSub_d2, EffSub_d3, EffSub_d4, EffSub_d5, EffSub_d6, EffSub_d7 :  std_logic;
   -- timing of EffSub: (c0, 2.844000ns)
signal xExpFieldZero, xExpFieldZero_d1, xExpFieldZero_d2, xExpFieldZero_d3, xExpFieldZero_d4 :  std_logic;
   -- timing of xExpFieldZero: (c1, 0.610000ns)
signal yExpFieldZero, yExpFieldZero_d1, yExpFieldZero_d2, yExpFieldZero_d3 :  std_logic;
   -- timing of yExpFieldZero: (c1, 0.610000ns)
signal xExpFieldAllOnes, xExpFieldAllOnes_d1, xExpFieldAllOnes_d2, xExpFieldAllOnes_d3 :  std_logic;
   -- timing of xExpFieldAllOnes: (c1, 0.610000ns)
signal yExpFieldAllOnes, yExpFieldAllOnes_d1, yExpFieldAllOnes_d2, yExpFieldAllOnes_d3 :  std_logic;
   -- timing of yExpFieldAllOnes: (c1, 0.610000ns)
signal xSigFieldZero, xSigFieldZero_d1 :  std_logic;
   -- timing of xSigFieldZero: (c3, 3.006000ns)
signal ySigFieldZero, ySigFieldZero_d1 :  std_logic;
   -- timing of ySigFieldZero: (c3, 3.006000ns)
signal xIsNaN :  std_logic;
   -- timing of xIsNaN: (c4, 0.148000ns)
signal yIsNaN :  std_logic;
   -- timing of yIsNaN: (c4, 0.148000ns)
signal xIsInfinity, xIsInfinity_d1, xIsInfinity_d2, xIsInfinity_d3 :  std_logic;
   -- timing of xIsInfinity: (c4, 0.148000ns)
signal yIsInfinity, yIsInfinity_d1, yIsInfinity_d2, yIsInfinity_d3 :  std_logic;
   -- timing of yIsInfinity: (c4, 0.148000ns)
signal xIsZero, xIsZero_d1, xIsZero_d2, xIsZero_d3 :  std_logic;
   -- timing of xIsZero: (c4, 0.148000ns)
signal yIsZero, yIsZero_d1, yIsZero_d2, yIsZero_d3 :  std_logic;
   -- timing of yIsZero: (c4, 0.148000ns)
signal bothSubNormals :  std_logic;
   -- timing of bothSubNormals: (c1, 1.234000ns)
signal resultIsNaN, resultIsNaN_d1, resultIsNaN_d2, resultIsNaN_d3 :  std_logic;
   -- timing of resultIsNaN: (c4, 0.772000ns)
signal significandNewX :  std_logic_vector(23 downto 0);
   -- timing of significandNewX: (c1, 0.610000ns)
signal significandNewY :  std_logic_vector(23 downto 0);
   -- timing of significandNewY: (c1, 0.610000ns)
signal allShiftedOut :  std_logic;
   -- timing of allShiftedOut: (c1, 0.106000ns)
signal rightShiftValue :  std_logic_vector(4 downto 0);
   -- timing of rightShiftValue: (c1, 0.730000ns)
signal shiftCorrection :  std_logic;
   -- timing of shiftCorrection: (c1, 1.234000ns)
signal finalRightShiftValue :  std_logic_vector(4 downto 0);
   -- timing of finalRightShiftValue: (c1, 2.488000ns)
signal significandY00 :  std_logic_vector(25 downto 0);
   -- timing of significandY00: (c1, 0.610000ns)
signal shiftedSignificandY :  std_logic_vector(25 downto 0);
   -- timing of shiftedSignificandY: (c2, 0.254000ns)
signal stickyLow, stickyLow_d1, stickyLow_d2, stickyLow_d3, stickyLow_d4 :  std_logic;
   -- timing of stickyLow: (c2, 2.978000ns)
signal summandY :  std_logic_vector(26 downto 0);
   -- timing of summandY: (c2, 0.878000ns)
signal summandX :  std_logic_vector(26 downto 0);
   -- timing of summandX: (c1, 0.610000ns)
signal carryIn :  std_logic;
   -- timing of carryIn: (c2, 2.978000ns)
signal significandZ :  std_logic_vector(26 downto 0);
   -- timing of significandZ: (c3, 1.434000ns)
signal z1, z1_d1, z1_d2 :  std_logic;
   -- timing of z1: (c3, 1.434000ns)
signal z0, z0_d1, z0_d2 :  std_logic;
   -- timing of z0: (c3, 1.434000ns)
signal lzcZInput :  std_logic_vector(25 downto 0);
   -- timing of lzcZInput: (c3, 1.434000ns)
signal lzc, lzc_d1 :  std_logic_vector(4 downto 0);
   -- timing of lzc: (c4, 2.491000ns)
signal leftShiftVal :  std_logic_vector(4 downto 0);
   -- timing of leftShiftVal: (c5, 0.887000ns)
signal normalizedSignificand, normalizedSignificand_d1 :  std_logic_vector(52 downto 0);
   -- timing of normalizedSignificand: (c5, 2.855000ns)
signal significandPreRound :  std_logic_vector(22 downto 0);
   -- timing of significandPreRound: (c5, 2.855000ns)
signal lsb, lsb_d1 :  std_logic;
   -- timing of lsb: (c5, 2.855000ns)
signal roundBit, roundBit_d1 :  std_logic;
   -- timing of roundBit: (c5, 2.855000ns)
signal stickyBit :  std_logic;
   -- timing of stickyBit: (c6, 0.627000ns)
signal deltaExp, deltaExp_d1 :  std_logic_vector(7 downto 0);
   -- timing of deltaExp: (c4, 2.491000ns)
signal fullCancellation, fullCancellation_d1, fullCancellation_d2 :  std_logic;
   -- timing of fullCancellation: (c5, 0.149000ns)
signal expPreRound :  std_logic_vector(7 downto 0);
   -- timing of expPreRound: (c5, 0.377000ns)
signal expSigPreRound :  std_logic_vector(30 downto 0);
   -- timing of expSigPreRound: (c5, 2.855000ns)
signal roundUpBit :  std_logic;
   -- timing of roundUpBit: (c6, 1.251000ns)
signal expSigR, expSigR_d1 :  std_logic_vector(30 downto 0);
   -- timing of expSigR: (c6, 3.189000ns)
signal resultIsZero :  std_logic;
   -- timing of resultIsZero: (c7, 1.075000ns)
signal resultIsInf :  std_logic;
   -- timing of resultIsInf: (c7, 1.075000ns)
signal constInf, constInf_d1, constInf_d2, constInf_d3, constInf_d4, constInf_d5, constInf_d6, constInf_d7 :  std_logic_vector(30 downto 0);
   -- timing of constInf: (c0, 0.000000ns)
signal constNaN, constNaN_d1, constNaN_d2, constNaN_d3, constNaN_d4, constNaN_d5, constNaN_d6, constNaN_d7 :  std_logic_vector(30 downto 0);
   -- timing of constNaN: (c0, 0.000000ns)
signal expSigR2 :  std_logic_vector(30 downto 0);
   -- timing of expSigR2: (c7, 1.699000ns)
signal signR :  std_logic;
   -- timing of signR: (c7, 1.699000ns)
signal computedR :  std_logic_vector(31 downto 0);
   -- timing of computedR: (c7, 1.699000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            newX_d1 <=  newX;
            newX_d2 <=  newX_d1;
            newX_d3 <=  newX_d2;
            newY_d1 <=  newY;
            newY_d2 <=  newY_d1;
            newY_d3 <=  newY_d2;
            expDiff_d1 <=  expDiff;
            expNewX_d1 <=  expNewX;
            expNewX_d2 <=  expNewX_d1;
            expNewX_d3 <=  expNewX_d2;
            expNewX_d4 <=  expNewX_d3;
            expNewX_d5 <=  expNewX_d4;
            expNewY_d1 <=  expNewY;
            signNewX_d1 <=  signNewX;
            signNewX_d2 <=  signNewX_d1;
            signNewX_d3 <=  signNewX_d2;
            signNewX_d4 <=  signNewX_d3;
            signNewX_d5 <=  signNewX_d4;
            signNewX_d6 <=  signNewX_d5;
            signNewX_d7 <=  signNewX_d6;
            signNewY_d1 <=  signNewY;
            signNewY_d2 <=  signNewY_d1;
            signNewY_d3 <=  signNewY_d2;
            signNewY_d4 <=  signNewY_d3;
            signNewY_d5 <=  signNewY_d4;
            signNewY_d6 <=  signNewY_d5;
            signNewY_d7 <=  signNewY_d6;
            EffSub_d1 <=  EffSub;
            EffSub_d2 <=  EffSub_d1;
            EffSub_d3 <=  EffSub_d2;
            EffSub_d4 <=  EffSub_d3;
            EffSub_d5 <=  EffSub_d4;
            EffSub_d6 <=  EffSub_d5;
            EffSub_d7 <=  EffSub_d6;
            xExpFieldZero_d1 <=  xExpFieldZero;
            xExpFieldZero_d2 <=  xExpFieldZero_d1;
            xExpFieldZero_d3 <=  xExpFieldZero_d2;
            xExpFieldZero_d4 <=  xExpFieldZero_d3;
            yExpFieldZero_d1 <=  yExpFieldZero;
            yExpFieldZero_d2 <=  yExpFieldZero_d1;
            yExpFieldZero_d3 <=  yExpFieldZero_d2;
            xExpFieldAllOnes_d1 <=  xExpFieldAllOnes;
            xExpFieldAllOnes_d2 <=  xExpFieldAllOnes_d1;
            xExpFieldAllOnes_d3 <=  xExpFieldAllOnes_d2;
            yExpFieldAllOnes_d1 <=  yExpFieldAllOnes;
            yExpFieldAllOnes_d2 <=  yExpFieldAllOnes_d1;
            yExpFieldAllOnes_d3 <=  yExpFieldAllOnes_d2;
            xSigFieldZero_d1 <=  xSigFieldZero;
            ySigFieldZero_d1 <=  ySigFieldZero;
            xIsInfinity_d1 <=  xIsInfinity;
            xIsInfinity_d2 <=  xIsInfinity_d1;
            xIsInfinity_d3 <=  xIsInfinity_d2;
            yIsInfinity_d1 <=  yIsInfinity;
            yIsInfinity_d2 <=  yIsInfinity_d1;
            yIsInfinity_d3 <=  yIsInfinity_d2;
            xIsZero_d1 <=  xIsZero;
            xIsZero_d2 <=  xIsZero_d1;
            xIsZero_d3 <=  xIsZero_d2;
            yIsZero_d1 <=  yIsZero;
            yIsZero_d2 <=  yIsZero_d1;
            yIsZero_d3 <=  yIsZero_d2;
            resultIsNaN_d1 <=  resultIsNaN;
            resultIsNaN_d2 <=  resultIsNaN_d1;
            resultIsNaN_d3 <=  resultIsNaN_d2;
            stickyLow_d1 <=  stickyLow;
            stickyLow_d2 <=  stickyLow_d1;
            stickyLow_d3 <=  stickyLow_d2;
            stickyLow_d4 <=  stickyLow_d3;
            z1_d1 <=  z1;
            z1_d2 <=  z1_d1;
            z0_d1 <=  z0;
            z0_d2 <=  z0_d1;
            lzc_d1 <=  lzc;
            normalizedSignificand_d1 <=  normalizedSignificand;
            lsb_d1 <=  lsb;
            roundBit_d1 <=  roundBit;
            deltaExp_d1 <=  deltaExp;
            fullCancellation_d1 <=  fullCancellation;
            fullCancellation_d2 <=  fullCancellation_d1;
            expSigR_d1 <=  expSigR;
            constInf_d1 <=  constInf;
            constInf_d2 <=  constInf_d1;
            constInf_d3 <=  constInf_d2;
            constInf_d4 <=  constInf_d3;
            constInf_d5 <=  constInf_d4;
            constInf_d6 <=  constInf_d5;
            constInf_d7 <=  constInf_d6;
            constNaN_d1 <=  constNaN;
            constNaN_d2 <=  constNaN_d1;
            constNaN_d3 <=  constNaN_d2;
            constNaN_d4 <=  constNaN_d3;
            constNaN_d5 <=  constNaN_d4;
            constNaN_d6 <=  constNaN_d5;
            constNaN_d7 <=  constNaN_d6;
         end if;
      end process;

   -- Exponent difference and swap
   expFracX <= X(30 downto 0);
   expFracY <= Y(30 downto 0);
   expXmExpY <= ('0' & X(30 downto 23)) - ('0'  & Y(30 downto 23)) ;
   expYmExpX <= ('0' & Y(30 downto 23)) - ('0'  & X(30 downto 23)) ;
   swap <= '0' when expFracX >= expFracY else '1';
   newX <= X when swap = '0' else Y;
   newY <= Y when swap = '0' else X;
   expDiff <= expXmExpY when swap = '0' else expYmExpX;
   expNewX <= newX(30 downto 23);
   expNewY <= newY(30 downto 23);
   signNewX <= newX(31);
   signNewY <= newY(31);
   EffSub <= signNewX xor signNewY;
   -- Special case dectection
   xExpFieldZero <= '1' when expNewX_d1="00000000" else '0';
   yExpFieldZero <= '1' when expNewY_d1="00000000" else '0';
   xExpFieldAllOnes <= '1' when expNewX_d1="11111111" else '0';
   yExpFieldAllOnes <= '1' when expNewY_d1="11111111" else '0';
   xSigFieldZero <= '1' when newX_d3(22 downto 0)="00000000000000000000000" else '0';
   ySigFieldZero <= '1' when newY_d3(22 downto 0)="00000000000000000000000" else '0';
   xIsNaN <= xExpFieldAllOnes_d3 and not xSigFieldZero_d1;
   yIsNaN <= yExpFieldAllOnes_d3 and not ySigFieldZero_d1;
   xIsInfinity <= xExpFieldAllOnes_d3 and xSigFieldZero_d1;
   yIsInfinity <= yExpFieldAllOnes_d3 and ySigFieldZero_d1;
   xIsZero <= xExpFieldZero_d3 and xSigFieldZero_d1;
   yIsZero <= yExpFieldZero_d3 and ySigFieldZero_d1;
   bothSubNormals <=  xExpFieldZero and yExpFieldZero;
   resultIsNaN <=  xIsNaN or yIsNaN  or  (xIsInfinity and yIsInfinity and EffSub_d4);
   significandNewX <= not(xExpFieldZero) & newX_d1(22 downto 0);
   significandNewY <= not(yExpFieldZero) & newY_d1(22 downto 0);

   -- Significand alignment
   allShiftedOut <= '1' when (expDiff_d1 >= 26) else '0';
   rightShiftValue <= expDiff_d1(4 downto 0) when allShiftedOut='0' else CONV_STD_LOGIC_VECTOR(26,5) ;
   shiftCorrection <= '1' when (yExpFieldZero='1' and xExpFieldZero='0') else '0'; -- only other cases are: both normal or both subnormal
   finalRightShiftValue <= rightShiftValue - ("0000" & shiftCorrection);
   significandY00 <= significandNewY & "00";
   RightShifterComponent: RightShifterSticky26_by_max_25_Freq250_uid4
      port map ( clk  => clk,
                 S => finalRightShiftValue,
                 X => significandY00,
                 R => shiftedSignificandY,
                 Sticky => stickyLow);
   summandY <= ('0' & shiftedSignificandY) xor (26 downto 0 => EffSub_d2);


   -- Significand addition
   summandX <= '0' & significandNewX & '0' & '0';
   carryIn <= EffSub_d2 and not stickyLow;
   fracAdder: IntAdder_27_Freq250_uid6
      port map ( clk  => clk,
                 Cin => carryIn,
                 X => summandX,
                 Y => summandY,
                 R => significandZ);

   -- Cancellation detection, renormalization (see explanations in IEEEFPAdd.cpp) 
   z1 <=  significandZ(26); -- bit of weight 1
   z0 <=  significandZ(25); -- bit of weight 0
   lzcZInput <= significandZ(26 downto 1);
   IEEEFPAdd_8_23_Freq250_uid2LeadingZeroCounter: LZC_26_Freq250_uid8
      port map ( clk  => clk,
                 I => lzcZInput,
                 O => lzc);
   leftShiftVal <= 
      lzc_d1 when ((z1_d2='1') or (z1_d2='0' and z0_d2='1' and xExpFieldZero_d4='1') or (z1_d2='0' and z0_d2='0' and xExpFieldZero_d4='0' and lzc_d1<=expNewX_d5)  or (xExpFieldZero_d4='0' and lzc_d1>=26) ) 
      else (expNewX_d5(4 downto 0)) when (xExpFieldZero_d4='0' and (lzc_d1 < 26) and (("000"&lzc_d1)>=expNewX_d5)) 
       else "0000"&'1';
   LeftShifterComponent: LeftShifter27_by_max_26_Freq250_uid10
      port map ( clk  => clk,
                 S => leftShiftVal,
                 X => significandZ,
                 R => normalizedSignificand);
   significandPreRound <= normalizedSignificand(25 downto 3); -- remove the implicit zero/one
   lsb <= normalizedSignificand(3);
   roundBit <= normalizedSignificand(2);
   stickyBit <= stickyLow_d4 or  normalizedSignificand_d1(1)or  normalizedSignificand_d1(0);
   deltaExp <=    -- value to subtract to exponent for normalization
      "00000000" when ( (z1_d1='0' and z0_d1='1' and xExpFieldZero_d3='0')
          or  (z1_d1='0' and z0_d1='0' and xExpFieldZero_d3='1') )
      else "11111111" when ( (z1_d1='1')  or  (z1_d1='0' and z0_d1='1' and xExpFieldZero_d3='1'))
      else ("000" & lzc)-'1' when (z1_d1='0' and z0_d1='0' and xExpFieldZero_d3='0' and lzc<=expNewX_d4 and lzc<26)      else expNewX_d4;
   fullCancellation <= '1' when (lzc_d1>=26) else '0';
   expPreRound <= expNewX_d5 - deltaExp_d1; -- we may have a first overflow here
   expSigPreRound <= expPreRound & significandPreRound; 
   -- Final rounding, with the mantissa overflowing in the exponent  
   roundUpBit <= '1' when roundBit_d1='1' and (stickyBit='1' or (stickyBit='0' and lsb_d1='1')) else '0';
   roundingAdder: IntAdder_31_Freq250_uid13
      port map ( clk  => clk,
                 Cin => roundUpBit,
                 X => expSigPreRound,
                 Y => "0000000000000000000000000000000",
                 R => expSigR);
   -- Final packing
   resultIsZero <= '1' when (fullCancellation_d2='1' and expSigR_d1(30 downto 23)="00000000") else '0';
   resultIsInf <= '1' when resultIsNaN_d3='0' and (((xIsInfinity_d3='1' and yIsInfinity_d3='1'  and EffSub_d7='0')  or (xIsInfinity_d3='0' and yIsInfinity_d3='1')  or (xIsInfinity_d3='1' and yIsInfinity_d3='0')  or  (expSigR_d1(30 downto 23)="11111111"))) else '0';
   constInf <= "11111111" & "00000000000000000000000";
   constNaN <= "1111111111111111111111111111111";
   expSigR2 <= constInf_d7 when resultIsInf='1' else constNaN_d7 when resultIsNaN_d3='1' else expSigR_d1;
   signR <= '0' when ((resultIsNaN_d3='1'  or (resultIsZero='1' and xIsInfinity_d3='0' and yIsInfinity_d3='0')) and (xIsZero_d3='0' or yIsZero_d3='0' or (signNewX_d7 /= signNewY_d7)) )  else signNewX_d7;
   computedR <= signR & expSigR2;
   R <= computedR;
end architecture;

