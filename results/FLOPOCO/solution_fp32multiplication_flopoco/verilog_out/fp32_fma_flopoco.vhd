--------------------------------------------------------------------------------
--                   RightShifter24_by_max_76_Freq250_uid4
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Bogdan Pasca (2008-2011), Florent de Dinechin (2008-2019)
--------------------------------------------------------------------------------
-- Pipeline depth: 0 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X S
-- Output signals: R
--  approx. input signal timings: X: (c0, 0.000000ns)S: (c0, 0.000000ns)
--  approx. output signal timings: R: (c0, 3.402000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity RightShifter24_by_max_76_Freq250_uid4 is
    port (clk : in std_logic;
          X : in  std_logic_vector(23 downto 0);
          S : in  std_logic_vector(6 downto 0);
          R : out  std_logic_vector(99 downto 0)   );
end entity;

architecture arch of RightShifter24_by_max_76_Freq250_uid4 is
signal ps :  std_logic_vector(6 downto 0);
   -- timing of ps: (c0, 0.000000ns)
signal level0 :  std_logic_vector(23 downto 0);
   -- timing of level0: (c0, 0.000000ns)
signal level1 :  std_logic_vector(24 downto 0);
   -- timing of level1: (c0, 0.000000ns)
signal level2 :  std_logic_vector(26 downto 0);
   -- timing of level2: (c0, 0.894000ns)
signal level3 :  std_logic_vector(30 downto 0);
   -- timing of level3: (c0, 0.894000ns)
signal level4 :  std_logic_vector(38 downto 0);
   -- timing of level4: (c0, 1.908000ns)
signal level5 :  std_logic_vector(54 downto 0);
   -- timing of level5: (c0, 1.908000ns)
signal level6 :  std_logic_vector(86 downto 0);
   -- timing of level6: (c0, 3.402000ns)
signal level7 :  std_logic_vector(150 downto 0);
   -- timing of level7: (c0, 3.402000ns)
begin
   ps<= S;
   level0<= X;
   level1 <=  (0 downto 0 => '0') & level0 when ps(0) = '1' else    level0 & (0 downto 0 => '0');
   level2 <=  (1 downto 0 => '0') & level1 when ps(1) = '1' else    level1 & (1 downto 0 => '0');
   level3 <=  (3 downto 0 => '0') & level2 when ps(2) = '1' else    level2 & (3 downto 0 => '0');
   level4 <=  (7 downto 0 => '0') & level3 when ps(3) = '1' else    level3 & (7 downto 0 => '0');
   level5 <=  (15 downto 0 => '0') & level4 when ps(4) = '1' else    level4 & (15 downto 0 => '0');
   level6 <=  (31 downto 0 => '0') & level5 when ps(5) = '1' else    level5 & (31 downto 0 => '0');
   level7 <=  (63 downto 0 => '0') & level6 when ps(6) = '1' else    level6 & (63 downto 0 => '0');
   R <= level7(150 downto 51);
end architecture;

--------------------------------------------------------------------------------
--                            LZC_52_Freq250_uid6
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Florent de Dinechin, Bogdan Pasca (2007)
--------------------------------------------------------------------------------
-- Pipeline depth: 2 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: I
-- Output signals: O
--  approx. input signal timings: I: (c0, 3.402000ns)
--  approx. output signal timings: O: (c2, 2.396000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity LZC_52_Freq250_uid6 is
    port (clk : in std_logic;
          I : in  std_logic_vector(51 downto 0);
          O : out  std_logic_vector(5 downto 0)   );
end entity;

architecture arch of LZC_52_Freq250_uid6 is
signal level6, level6_d1 :  std_logic_vector(62 downto 0);
   -- timing of level6: (c0, 3.402000ns)
signal digit5, digit5_d1 :  std_logic;
   -- timing of digit5: (c1, 0.715000ns)
signal level5 :  std_logic_vector(30 downto 0);
   -- timing of level5: (c1, 1.339000ns)
signal digit4, digit4_d1 :  std_logic;
   -- timing of digit4: (c1, 2.048500ns)
signal level4, level4_d1 :  std_logic_vector(14 downto 0);
   -- timing of level4: (c1, 2.672500ns)
signal digit3, digit3_d1 :  std_logic;
   -- timing of digit3: (c1, 3.353500ns)
signal level3 :  std_logic_vector(6 downto 0);
   -- timing of level3: (c2, 0.495500ns)
signal digit2 :  std_logic;
   -- timing of digit2: (c2, 1.148000ns)
signal level2 :  std_logic_vector(2 downto 0);
   -- timing of level2: (c2, 1.772000ns)
signal lowBits :  std_logic_vector(1 downto 0);
   -- timing of lowBits: (c2, 2.396000ns)
signal outHighBits :  std_logic_vector(3 downto 0);
   -- timing of outHighBits: (c2, 1.148000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            level6_d1 <=  level6;
            digit5_d1 <=  digit5;
            digit4_d1 <=  digit4;
            level4_d1 <=  level4;
            digit3_d1 <=  digit3;
         end if;
      end process;
   -- pad input to the next power of two minus 1
   level6 <= I & "11111111111";
   -- Main iteration for large inputs
   digit5<= '1' when level6_d1(62 downto 31) = "00000000000000000000000000000000" else '0';
   level5<= level6_d1(30 downto 0) when digit5='1' else level6_d1(62 downto 32);
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
   outHighBits <= digit5_d1 & digit4_d1 & digit3_d1 & digit2 & "";
   O <= outHighBits & lowBits ;
end architecture;

--------------------------------------------------------------------------------
--                    LeftShifter76_by_max_75_Freq250_uid8
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Bogdan Pasca (2008-2011), Florent de Dinechin (2008-2019)
--------------------------------------------------------------------------------
-- Pipeline depth: 4 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: X S
-- Output signals: R
--  approx. input signal timings: X: (c0, 3.402000ns)S: (c2, 2.396000ns)
--  approx. output signal timings: R: (c4, 0.394000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity LeftShifter76_by_max_75_Freq250_uid8 is
    port (clk : in std_logic;
          X : in  std_logic_vector(75 downto 0);
          S : in  std_logic_vector(6 downto 0);
          R : out  std_logic_vector(150 downto 0)   );
end entity;

architecture arch of LeftShifter76_by_max_75_Freq250_uid8 is
signal ps, ps_d1, ps_d2 :  std_logic_vector(6 downto 0);
   -- timing of ps: (c2, 2.396000ns)
signal level0, level0_d1, level0_d2 :  std_logic_vector(75 downto 0);
   -- timing of level0: (c0, 3.402000ns)
signal level1, level1_d1 :  std_logic_vector(76 downto 0);
   -- timing of level1: (c2, 2.396000ns)
signal level2 :  std_logic_vector(78 downto 0);
   -- timing of level2: (c3, 0.328000ns)
signal level3 :  std_logic_vector(82 downto 0);
   -- timing of level3: (c3, 0.328000ns)
signal level4 :  std_logic_vector(90 downto 0);
   -- timing of level4: (c3, 1.862000ns)
signal level5, level5_d1 :  std_logic_vector(106 downto 0);
   -- timing of level5: (c3, 1.862000ns)
signal level6 :  std_logic_vector(138 downto 0);
   -- timing of level6: (c4, 0.394000ns)
signal level7 :  std_logic_vector(202 downto 0);
   -- timing of level7: (c4, 0.394000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            ps_d1 <=  ps;
            ps_d2 <=  ps_d1;
            level0_d1 <=  level0;
            level0_d2 <=  level0_d1;
            level1_d1 <=  level1;
            level5_d1 <=  level5;
         end if;
      end process;
   ps<= S;
   level0<= X;
   level1<= level0_d2 & (0 downto 0 => '0') when ps(0)= '1' else     (0 downto 0 => '0') & level0_d2;
   level2<= level1_d1 & (1 downto 0 => '0') when ps_d1(1)= '1' else     (1 downto 0 => '0') & level1_d1;
   level3<= level2 & (3 downto 0 => '0') when ps_d1(2)= '1' else     (3 downto 0 => '0') & level2;
   level4<= level3 & (7 downto 0 => '0') when ps_d1(3)= '1' else     (7 downto 0 => '0') & level3;
   level5<= level4 & (15 downto 0 => '0') when ps_d1(4)= '1' else     (15 downto 0 => '0') & level4;
   level6<= level5_d1 & (31 downto 0 => '0') when ps_d2(5)= '1' else     (31 downto 0 => '0') & level5_d1;
   level7<= level6 & (63 downto 0 => '0') when ps_d2(6)= '1' else     (63 downto 0 => '0') & level6;
   R <= level7(150 downto 0);
end architecture;

--------------------------------------------------------------------------------
--                              fp32_fma_flopoco
--                       (IEEEFPFMA_8_23_Freq250_uid2)
-- Inputs: this FMA computes A*B+C
-- VHDL generated for Zynq7000 @ 250MHz
-- This operator is part of the Infinite Virtual Library FloPoCoLib
-- All rights reserved 
-- Authors: Florent de Dinechin (2009-2019)
--------------------------------------------------------------------------------
-- Pipeline depth: 4 cycles
-- Clock period (ns): 4
-- Target frequency (MHz): 250
-- Input signals: A B C negateAB negateC RndMode
-- Output signals: R
--  approx. input signal timings: A: (c0, 0.000000ns)B: (c0, 0.000000ns)C: (c0, 0.000000ns)negateAB: (c0, 0.000000ns)negateC: (c0, 0.000000ns)RndMode: (c0, 0.000000ns)
--  approx. output signal timings: R: (c4, 0.394000ns)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
library std;
use std.textio.all;
library work;

entity fp32_fma_flopoco is
    port (clk : in std_logic;
          A : in  std_logic_vector(31 downto 0);
          B : in  std_logic_vector(31 downto 0);
          C : in  std_logic_vector(31 downto 0);
          negateAB : in  std_logic;
          negateC : in  std_logic;
          RndMode : in  std_logic_vector(1 downto 0);
          R : out  std_logic_vector(31 downto 0)   );
end entity;

architecture arch of fp32_fma_flopoco is
   component RightShifter24_by_max_76_Freq250_uid4 is
      port ( clk : in std_logic;
             X : in  std_logic_vector(23 downto 0);
             S : in  std_logic_vector(6 downto 0);
             R : out  std_logic_vector(99 downto 0)   );
   end component;

   component LZC_52_Freq250_uid6 is
      port ( clk : in std_logic;
             I : in  std_logic_vector(51 downto 0);
             O : out  std_logic_vector(5 downto 0)   );
   end component;

   component LeftShifter76_by_max_75_Freq250_uid8 is
      port ( clk : in std_logic;
             X : in  std_logic_vector(75 downto 0);
             S : in  std_logic_vector(6 downto 0);
             R : out  std_logic_vector(150 downto 0)   );
   end component;

signal Asgn, Asgn_d1, Asgn_d2 :  std_logic;
   -- timing of Asgn: (c0, 0.000000ns)
signal AexpField :  std_logic_vector(7 downto 0);
   -- timing of AexpField: (c0, 0.000000ns)
signal AsigField :  std_logic_vector(22 downto 0);
   -- timing of AsigField: (c0, 0.000000ns)
signal AisNormal :  std_logic;
   -- timing of AisNormal: (c0, 0.000000ns)
signal AisInfOrNaN :  std_logic;
   -- timing of AisInfOrNaN: (c0, 0.000000ns)
signal AhasNonNullSig :  std_logic;
   -- timing of AhasNonNullSig: (c0, 0.000000ns)
signal AisZero, AisZero_d1, AisZero_d2 :  std_logic;
   -- timing of AisZero: (c0, 0.000000ns)
signal AisInf :  std_logic;
   -- timing of AisInf: (c0, 0.000000ns)
signal AisNaN :  std_logic;
   -- timing of AisNaN: (c0, 0.000000ns)
signal Bsgn, Bsgn_d1, Bsgn_d2 :  std_logic;
   -- timing of Bsgn: (c0, 0.000000ns)
signal BexpField :  std_logic_vector(7 downto 0);
   -- timing of BexpField: (c0, 0.000000ns)
signal BsigField :  std_logic_vector(22 downto 0);
   -- timing of BsigField: (c0, 0.000000ns)
signal BisNormal :  std_logic;
   -- timing of BisNormal: (c0, 0.000000ns)
signal BisInfOrNaN :  std_logic;
   -- timing of BisInfOrNaN: (c0, 0.000000ns)
signal BhasNonNullSig :  std_logic;
   -- timing of BhasNonNullSig: (c0, 0.000000ns)
signal BisZero, BisZero_d1, BisZero_d2 :  std_logic;
   -- timing of BisZero: (c0, 0.000000ns)
signal BisInf :  std_logic;
   -- timing of BisInf: (c0, 0.000000ns)
signal BisNaN :  std_logic;
   -- timing of BisNaN: (c0, 0.000000ns)
signal Aexp :  std_logic_vector(7 downto 0);
   -- timing of Aexp: (c0, 0.000000ns)
signal Bexp :  std_logic_vector(7 downto 0);
   -- timing of Bexp: (c0, 0.000000ns)
signal Asig :  std_logic_vector(23 downto 0);
   -- timing of Asig: (c0, 0.000000ns)
signal Bsig :  std_logic_vector(23 downto 0);
   -- timing of Bsig: (c0, 0.000000ns)
signal AexpPlusBexp, AexpPlusBexp_d1, AexpPlusBexp_d2 :  std_logic_vector(8 downto 0);
   -- timing of AexpPlusBexp: (c0, 0.000000ns)
signal Csgn, Csgn_d1, Csgn_d2 :  std_logic;
   -- timing of Csgn: (c0, 0.000000ns)
signal CexpField :  std_logic_vector(7 downto 0);
   -- timing of CexpField: (c0, 0.000000ns)
signal CsigField :  std_logic_vector(22 downto 0);
   -- timing of CsigField: (c0, 0.000000ns)
signal CisNormal, CisNormal_d1, CisNormal_d2 :  std_logic;
   -- timing of CisNormal: (c0, 0.000000ns)
signal CisInfOrNaN :  std_logic;
   -- timing of CisInfOrNaN: (c0, 0.000000ns)
signal ChasNonNullSig :  std_logic;
   -- timing of ChasNonNullSig: (c0, 0.000000ns)
signal CisZero, CisZero_d1, CisZero_d2 :  std_logic;
   -- timing of CisZero: (c0, 0.000000ns)
signal CisInf :  std_logic;
   -- timing of CisInf: (c0, 0.000000ns)
signal CisNaN :  std_logic;
   -- timing of CisNaN: (c0, 0.000000ns)
signal RisNaN, RisNaN_d1, RisNaN_d2, RisNaN_d3, RisNaN_d4 :  std_logic;
   -- timing of RisNaN: (c0, 0.000000ns)
signal tentativeRisInf, tentativeRisInf_d1, tentativeRisInf_d2, tentativeRisInf_d3, tentativeRisInf_d4 :  std_logic;
   -- timing of tentativeRisInf: (c0, 0.000000ns)
signal Cexp, Cexp_d1, Cexp_d2 :  std_logic_vector(7 downto 0);
   -- timing of Cexp: (c0, 0.000000ns)
signal effectiveSub :  std_logic;
   -- timing of effectiveSub: (c0, 0.000000ns)
signal Csig :  std_logic_vector(23 downto 0);
   -- timing of Csig: (c0, 0.000000ns)
signal expDiffPrepare :  std_logic_vector(9 downto 0);
   -- timing of expDiffPrepare: (c0, 0.000000ns)
signal expDiff :  std_logic_vector(9 downto 0);
   -- timing of expDiff: (c0, 0.000000ns)
signal tmpExpComp1 :  std_logic_vector(9 downto 0);
   -- timing of tmpExpComp1: (c0, 0.000000ns)
signal expDiffVerySmall :  std_logic;
   -- timing of expDiffVerySmall: (c0, 0.000000ns)
signal tmpExpComp2 :  std_logic_vector(9 downto 0);
   -- timing of tmpExpComp2: (c0, 0.000000ns)
signal expDiffSmall, expDiffSmall_d1, expDiffSmall_d2 :  std_logic;
   -- timing of expDiffSmall: (c0, 0.000000ns)
signal tmpExpComp3 :  std_logic_vector(9 downto 0);
   -- timing of tmpExpComp3: (c0, 0.000000ns)
signal expDiffNotLarge :  std_logic;
   -- timing of expDiffNotLarge: (c0, 0.000000ns)
signal ShiftValue, ShiftValue_d1, ShiftValue_d2 :  std_logic_vector(6 downto 0);
   -- timing of ShiftValue: (c0, 0.000000ns)
signal CsigShifted :  std_logic_vector(99 downto 0);
   -- timing of CsigShifted: (c0, 3.402000ns)
signal sticky1, sticky1_d1, sticky1_d2, sticky1_d3, sticky1_d4 :  std_logic;
   -- timing of sticky1: (c0, 3.402000ns)
signal CsigShiftedT :  std_logic_vector(75 downto 0);
   -- timing of CsigShiftedT: (c0, 3.402000ns)
signal P :  std_logic_vector(47 downto 0);
   -- timing of P: (c0, 0.000000ns)
signal Paligned :  std_logic_vector(75 downto 0);
   -- timing of Paligned: (c0, 0.000000ns)
signal CsigInverted :  std_logic_vector(76 downto 0);
   -- timing of CsigInverted: (c0, 3.402000ns)
signal BigSum :  std_logic_vector(76 downto 0);
   -- timing of BigSum: (c0, 3.402000ns)
signal BigSum2 :  std_logic_vector(76 downto 0);
   -- timing of BigSum2: (c0, 3.402000ns)
signal RsgnTentative, RsgnTentative_d1, RsgnTentative_d2 :  std_logic;
   -- timing of RsgnTentative: (c0, 3.402000ns)
signal BigSumAbs :  std_logic_vector(75 downto 0);
   -- timing of BigSumAbs: (c0, 3.402000ns)
signal BigSumAbsLowerBits :  std_logic_vector(51 downto 0);
   -- timing of BigSumAbsLowerBits: (c0, 3.402000ns)
signal L :  std_logic_vector(5 downto 0);
   -- timing of L: (c2, 2.396000ns)
signal tmpExpCompRes1, tmpExpCompRes1_d1, tmpExpCompRes1_d2 :  std_logic_vector(9 downto 0);
   -- timing of tmpExpCompRes1: (c0, 0.000000ns)
signal tmpExpCompRes2 :  std_logic_vector(9 downto 0);
   -- timing of tmpExpCompRes2: (c2, 2.396000ns)
signal RisSubNormal, RisSubNormal_d1, RisSubNormal_d2 :  std_logic;
   -- timing of RisSubNormal: (c2, 2.396000ns)
signal RisZero, RisZero_d1, RisZero_d2 :  std_logic;
   -- timing of RisZero: (c2, 2.396000ns)
signal RisSubNormalOrZero :  std_logic;
   -- timing of RisSubNormalOrZero: (c2, 2.396000ns)
signal Rsgn, Rsgn_d1, Rsgn_d2 :  std_logic;
   -- timing of Rsgn: (c2, 2.396000ns)
signal shiftValueCaseSubnormal, shiftValueCaseSubnormal_d1, shiftValueCaseSubnormal_d2 :  std_logic_vector(8 downto 0);
   -- timing of shiftValueCaseSubnormal: (c0, 0.000000ns)
signal normShiftValue :  std_logic_vector(6 downto 0);
   -- timing of normShiftValue: (c2, 2.396000ns)
signal BigSumNormd :  std_logic_vector(150 downto 0);
   -- timing of BigSumNormd: (c4, 0.394000ns)
signal expTentative, expTentative_d1, expTentative_d2 :  std_logic_vector(9 downto 0);
   -- timing of expTentative: (c2, 2.396000ns)
signal sticky2 :  std_logic;
   -- timing of sticky2: (c4, 0.394000ns)
signal fracTentative :  std_logic_vector(26 downto 0);
   -- timing of fracTentative: (c4, 0.394000ns)
signal fracLeadingBitsNormal :  std_logic_vector(1 downto 0);
   -- timing of fracLeadingBitsNormal: (c4, 0.394000ns)
signal fracLeadingBits :  std_logic_vector(1 downto 0);
   -- timing of fracLeadingBits: (c4, 0.394000ns)
signal fracResultNormd :  std_logic_vector(22 downto 0);
   -- timing of fracResultNormd: (c4, 0.394000ns)
signal fracResultRoundBit :  std_logic;
   -- timing of fracResultRoundBit: (c4, 0.394000ns)
signal fracResultStickyBit :  std_logic;
   -- timing of fracResultStickyBit: (c4, 0.394000ns)
signal round :  std_logic;
   -- timing of round: (c4, 0.394000ns)
signal expUpdate :  std_logic_vector(9 downto 0);
   -- timing of expUpdate: (c4, 0.394000ns)
signal exponentResult1 :  std_logic_vector(9 downto 0);
   -- timing of exponentResult1: (c4, 0.394000ns)
signal resultBeforeRound :  std_logic_vector(32 downto 0);
   -- timing of resultBeforeRound: (c4, 0.394000ns)
signal resultRounded :  std_logic_vector(32 downto 0);
   -- timing of resultRounded: (c4, 0.394000ns)
signal Roverflowed :  std_logic;
   -- timing of Roverflowed: (c4, 0.394000ns)
signal finalRisInf :  std_logic;
   -- timing of finalRisInf: (c4, 0.394000ns)
signal Inf, Inf_d1, Inf_d2, Inf_d3, Inf_d4 :  std_logic_vector(30 downto 0);
   -- timing of Inf: (c0, 0.000000ns)
signal NaN, NaN_d1, NaN_d2, NaN_d3, NaN_d4 :  std_logic_vector(30 downto 0);
   -- timing of NaN: (c0, 0.000000ns)
signal negateAB_d1, negateAB_d2 :  std_logic;
   -- timing of negateAB: (c0, 0.000000ns)
signal negateC_d1, negateC_d2 :  std_logic;
   -- timing of negateC: (c0, 0.000000ns)
begin
   process(clk)
      begin
         if clk'event and clk = '1' then
            Asgn_d1 <=  Asgn;
            Asgn_d2 <=  Asgn_d1;
            AisZero_d1 <=  AisZero;
            AisZero_d2 <=  AisZero_d1;
            Bsgn_d1 <=  Bsgn;
            Bsgn_d2 <=  Bsgn_d1;
            BisZero_d1 <=  BisZero;
            BisZero_d2 <=  BisZero_d1;
            AexpPlusBexp_d1 <=  AexpPlusBexp;
            AexpPlusBexp_d2 <=  AexpPlusBexp_d1;
            Csgn_d1 <=  Csgn;
            Csgn_d2 <=  Csgn_d1;
            CisNormal_d1 <=  CisNormal;
            CisNormal_d2 <=  CisNormal_d1;
            CisZero_d1 <=  CisZero;
            CisZero_d2 <=  CisZero_d1;
            RisNaN_d1 <=  RisNaN;
            RisNaN_d2 <=  RisNaN_d1;
            RisNaN_d3 <=  RisNaN_d2;
            RisNaN_d4 <=  RisNaN_d3;
            tentativeRisInf_d1 <=  tentativeRisInf;
            tentativeRisInf_d2 <=  tentativeRisInf_d1;
            tentativeRisInf_d3 <=  tentativeRisInf_d2;
            tentativeRisInf_d4 <=  tentativeRisInf_d3;
            Cexp_d1 <=  Cexp;
            Cexp_d2 <=  Cexp_d1;
            expDiffSmall_d1 <=  expDiffSmall;
            expDiffSmall_d2 <=  expDiffSmall_d1;
            ShiftValue_d1 <=  ShiftValue;
            ShiftValue_d2 <=  ShiftValue_d1;
            sticky1_d1 <=  sticky1;
            sticky1_d2 <=  sticky1_d1;
            sticky1_d3 <=  sticky1_d2;
            sticky1_d4 <=  sticky1_d3;
            RsgnTentative_d1 <=  RsgnTentative;
            RsgnTentative_d2 <=  RsgnTentative_d1;
            tmpExpCompRes1_d1 <=  tmpExpCompRes1;
            tmpExpCompRes1_d2 <=  tmpExpCompRes1_d1;
            RisSubNormal_d1 <=  RisSubNormal;
            RisSubNormal_d2 <=  RisSubNormal_d1;
            RisZero_d1 <=  RisZero;
            RisZero_d2 <=  RisZero_d1;
            Rsgn_d1 <=  Rsgn;
            Rsgn_d2 <=  Rsgn_d1;
            shiftValueCaseSubnormal_d1 <=  shiftValueCaseSubnormal;
            shiftValueCaseSubnormal_d2 <=  shiftValueCaseSubnormal_d1;
            expTentative_d1 <=  expTentative;
            expTentative_d2 <=  expTentative_d1;
            Inf_d1 <=  Inf;
            Inf_d2 <=  Inf_d1;
            Inf_d3 <=  Inf_d2;
            Inf_d4 <=  Inf_d3;
            NaN_d1 <=  NaN;
            NaN_d2 <=  NaN_d1;
            NaN_d3 <=  NaN_d2;
            NaN_d4 <=  NaN_d3;
            negateAB_d1 <=  negateAB;
            negateAB_d2 <=  negateAB_d1;
            negateC_d1 <=  negateC;
            negateC_d2 <=  negateC_d1;
         end if;
      end process;

    -- Input decomposition 
   Asgn <= A(31);
   AexpField <= A(30 downto 23);
   AsigField <= A(22 downto 0);
   AisNormal <= A(23) or A(24) or A(25) or A(26) or A(27) or A(28) or A(29) or A(30);
   AisInfOrNaN <= A(23) and A(24) and A(25) and A(26) and A(27) and A(28) and A(29) and A(30);
   AhasNonNullSig <= A(0) or A(1) or A(2) or A(3) or A(4) or A(5) or A(6) or A(7) or A(8) or A(9) or A(10) or A(11) or A(12) or A(13) or A(14) or A(15) or A(16) or A(17) or A(18) or A(19) or A(20) or A(21) or A(22);
   AisZero <= (not AisNormal) and not AhasNonNullSig;
   AisInf <= AisInfOrNaN and not AhasNonNullSig;
   AisNaN <= AisInfOrNaN and AhasNonNullSig;
   Bsgn <= B(31);
   BexpField <= B(30 downto 23);
   BsigField <= B(22 downto 0);
   BisNormal <= B(23) or B(24) or B(25) or B(26) or B(27) or B(28) or B(29) or B(30);
   BisInfOrNaN <= B(23) and B(24) and B(25) and B(26) and B(27) and B(28) and B(29) and B(30);
   BhasNonNullSig <= B(0) or B(1) or B(2) or B(3) or B(4) or B(5) or B(6) or B(7) or B(8) or B(9) or B(10) or B(11) or B(12) or B(13) or B(14) or B(15) or B(16) or B(17) or B(18) or B(19) or B(20) or B(21) or B(22);
   BisZero <= (not BisNormal) and not BhasNonNullSig;
   BisInf <= BisInfOrNaN and not BhasNonNullSig;
   BisNaN <= BisInfOrNaN and BhasNonNullSig;

   -- unbiased exponents make everything simpler but may lead to suboptimal arch 
   Aexp <= AexpField - ("0" & (6 downto 1 => '1') & AisNormal);
   Bexp <= BexpField - ("0" & (6 downto 1 => '1') & BisNormal);

   -- mantissa with the implicit 1 or 0 appended 
   Asig <= AisNormal & AsigField ;
   Bsig <= BisNormal & BsigField ;
   AexpPlusBexp <= (Aexp(7) & Aexp) + (Bexp(7) & Bexp) ;
   Csgn <= C(31);
   CexpField <= C(30 downto 23);
   CsigField <= C(22 downto 0);
   CisNormal <= C(23) or C(24) or C(25) or C(26) or C(27) or C(28) or C(29) or C(30);
   CisInfOrNaN <= C(23) and C(24) and C(25) and C(26) and C(27) and C(28) and C(29) and C(30);
   ChasNonNullSig <= C(0) or C(1) or C(2) or C(3) or C(4) or C(5) or C(6) or C(7) or C(8) or C(9) or C(10) or C(11) or C(12) or C(13) or C(14) or C(15) or C(16) or C(17) or C(18) or C(19) or C(20) or C(21) or C(22);
   CisZero <= (not CisNormal) and not ChasNonNullSig;
   CisInf <= CisInfOrNaN and not ChasNonNullSig;
   CisNaN <= CisInfOrNaN and ChasNonNullSig;
   -- result NaN iff one input is NaN, or 0*inf+x, or +/-(inf-inf)
   -- not tentative: the last case may not happen for finite A and B and inf C, as in this case AB remains finite
   RisNaN <= AisNaN or BisNaN or CisNaN or ((AisInf or BisInf) and CisInf and ((Asgn xor Bsgn) xor Csgn));
   -- result inf iff either AB or C is inf, and both have the same sign
   -- tentative, AB+C may overflow
   tentativeRisInf <= (((AisInf and not (BisZero or BisNaN)) or (BisInf and not (AisZero or AisNaN))) and (not CisNaN) and ((CisInf and not ((Asgn xor Bsgn) xor Csgn)) or not CisInf))
      or (CisInf and (not (AisNaN or BisNaN)) and (((AisInf or BisInf) and not ((Asgn xor Bsgn) xor Csgn)) or not (AisInf or BisInf)));

   -- unbiased exponents make everything simpler but may lead to suboptimal arch 
   Cexp <= CexpField - ("0" & (6 downto 1 => '1') & CisNormal);
   effectiveSub <= (negateAB xor Asgn xor Bsgn) xor (negateC xor Csgn);

   -- mantissa with the implicit 1 or 0 appended 
   Csig <= CisNormal & CsigField ;

    -- Computation of the exponent difference 
   expDiffPrepare <= ("00" & AexpField) + ("00" & BexpField) - ("000" & (6 downto 1 => '1') & AisNormal) - BisNormal;
   expDiff <= ("00" & CexpField) - expDiffPrepare - CisNormal;

    -- Addend shift datapath 
   -- Some logic to determine shift distance and tentative result exponent 
   tmpExpComp1 <= expDiff + "0000110000";
   expDiffVerySmall <= tmpExpComp1(9);  -- if expDiff < -2p
   tmpExpComp2 <= expDiff - "0000000011";
   expDiffSmall <= tmpExpComp2(9);  -- if expDiff < 3
   tmpExpComp3 <= expDiff - "0000011011";
   expDiffNotLarge <= tmpExpComp3(9);  -- if expDiff < p+3
   ShiftValue <= 
           "1001100" when expDiffVerySmall='1'
      else "0011011" - (expDiff (6 downto 0)) when expDiffNotLarge='1'
      else "0000000" ;
   RightShifterComponent: RightShifter24_by_max_76_Freq250_uid4
      port map ( clk  => clk,
                 S => ShiftValue,
                 X => Csig,
                 R => CsigShifted);
   sticky1 <= CsigShifted(0) or CsigShifted(1) or CsigShifted(2) or CsigShifted(3) or CsigShifted(4) or CsigShifted(5) or CsigShifted(6) or CsigShifted(7) or CsigShifted(8) or CsigShifted(9) or CsigShifted(10) or CsigShifted(11) or CsigShifted(12) or CsigShifted(13) or CsigShifted(14) or CsigShifted(15) or CsigShifted(16) or CsigShifted(17) or CsigShifted(18) or CsigShifted(19) or CsigShifted(20) or CsigShifted(21) or CsigShifted(22) or CsigShifted(23);
   CsigShiftedT <= CsigShifted(99 downto 24);

    -- Product datapath (using naive * operator, may improve in the future)
   P <= Asig * Bsig ;
   Paligned <= (25 downto 0 => '0') & P & "00";

    -- The sum at last 
   CsigInverted <= ('0' &CsigShiftedT) when effectiveSub='0'  else ('1' & not CsigShiftedT);
   BigSum <= CsigInverted + ('0' & Paligned) + effectiveSub;  -- P +/-CeffectiveSub is a carry in
   BigSum2 <= CsigShiftedT - ('0' & Paligned);
   RsgnTentative <= Asgn xor Bsgn xor negateAB xor BigSum(76);
   BigSumAbs <= BigSum(75 downto 0) when (BigSum2(76) or not effectiveSub)='1' else BigSum2(75 downto 0);
   BigSumAbsLowerBits <= BigSumAbs(51 downto 0);
   IEEEFPFMA_8_23_Freq250_uid2LeadingZeroCounter: LZC_52_Freq250_uid6
      port map ( clk  => clk,
                 I => BigSumAbsLowerBits,
                 O => L);
   tmpExpCompRes1 <= (AexpPlusBexp(8) & AexpPlusBexp) + "0010000001";
   tmpExpCompRes2 <= tmpExpCompRes1_d2 - ((9 downto 6 => '0') & L);
   RisSubNormal <= (expDiffSmall_d2 or not CisNormal_d2) and  tmpExpCompRes2(9);
   RisZero <= expDiffSmall_d2 when L="110100"  else '0';
   RisSubNormalOrZero <= RisSubNormal or RisZero;
   Rsgn <=      (Asgn_d2 xor Bsgn_d2 xor negateAB_d2) and (Csgn_d2 xor negateC_d2) when ((AisZero_d2 or BisZero_d2) and CisZero_d2)='1'  -- negative only for -0 + -0 
      else '0' when RisZero='1'  -- covers 1-1 = +0
      else RsgnTentative_d2;  -- covers to underflow to zero case
   shiftValueCaseSubnormal <= AexpPlusBexp + "010011001";
   normShiftValue <= 
           L + "0011001" when (expDiffSmall_d2 and not RisSubNormal)='1'
      else shiftValueCaseSubnormal_d2(6 downto 0) when (expDiffSmall_d2 and RisSubNormal)='1'
      else ShiftValue_d2; -- undo inital shift
   NormalizationShifter: LeftShifter76_by_max_75_Freq250_uid8
      port map ( clk  => clk,
                 S => normShiftValue,
                 X => BigSumAbs,
                 R => BigSumNormd);
   -- TODO opt: push all the constant additions to exponentUpdate
   expTentative <= 
           "1110000011" when RisZero='1'
      else "1110000010" when RisSubNormal='1'
      else (AexpPlusBexp_d2(8) & AexpPlusBexp_d2 - ((9 downto 6 => '0') & L))  + "0000000011" when (expDiffSmall_d2 and not RisSubNormal)='1'
      else (Cexp_d2(7) & Cexp_d2(7) & Cexp_d2) + "0000000001" ;
   sticky2 <= BigSumNormd(0) or BigSumNormd(1) or BigSumNormd(2) or BigSumNormd(3) or BigSumNormd(4) or BigSumNormd(5) or BigSumNormd(6) or BigSumNormd(7) or BigSumNormd(8) or BigSumNormd(9) or BigSumNormd(10) or BigSumNormd(11) or BigSumNormd(12) or BigSumNormd(13) or BigSumNormd(14) or BigSumNormd(15) or BigSumNormd(16) or BigSumNormd(17) or BigSumNormd(18) or BigSumNormd(19) or BigSumNormd(20) or BigSumNormd(21) or BigSumNormd(22) or BigSumNormd(23) or BigSumNormd(24) or BigSumNormd(25) or BigSumNormd(26) or BigSumNormd(27) or BigSumNormd(28) or BigSumNormd(29) or BigSumNormd(30) or BigSumNormd(31) or BigSumNormd(32) or BigSumNormd(33) or BigSumNormd(34) or BigSumNormd(35) or BigSumNormd(36) or BigSumNormd(37) or BigSumNormd(38) or BigSumNormd(39) or BigSumNormd(40) or BigSumNormd(41) or BigSumNormd(42) or BigSumNormd(43) or BigSumNormd(44) or BigSumNormd(45) or BigSumNormd(46) or BigSumNormd(47) or BigSumNormd(48) or BigSumNormd(49);

   fracTentative <= BigSumNormd(76 downto 50);

    -- Last 2-bit normalization 
   fracLeadingBitsNormal <=  fracTentative(26 downto 25) ;
   fracLeadingBits <= "01" when RisSubNormal_d2='1' else  fracLeadingBitsNormal;
   fracResultNormd <=
           fracTentative(23 downto 1)  when fracLeadingBits = "00" 
      else fracTentative(24 downto 2)  when fracLeadingBits = "01" 
      else fracTentative(25 downto 3);
   fracResultRoundBit <=
           fracTentative(0) 	 when fracLeadingBits = "00" 
      else fracTentative(1)    when fracLeadingBits = "01" 
      else fracTentative(2) ;
   fracResultStickyBit <=
           sticky1_d4 or sticky2	 when fracLeadingBits = "00" 
      else fracTentative(0) or sticky1_d4 or sticky2    when fracLeadingBits = "01" 
      else fracTentative(1) or fracTentative(0) or  sticky1_d4 or sticky2;
   round <= fracResultRoundBit and (fracResultStickyBit or fracResultNormd(0));
   expUpdate <= "0001111101" when RisZero_d2 = '1'       -- bias - 2
         else   "0001111101" when fracLeadingBits = "00" -- bias - 2
         else   "0001111110" when fracLeadingBits = "01" -- bias - 1 
         else   "0001111111";                            -- bias 
   exponentResult1 <= expTentative_d2 + expUpdate;
   resultBeforeRound <= exponentResult1 & fracResultNormd;
   resultRounded <= resultBeforeRound + ((32 downto 1 => '0') & round);
   Roverflowed <= resultRounded(32) or resultRounded(31) or (resultRounded(30) and resultRounded(29) and resultRounded(28) and resultRounded(27) and resultRounded(26) and resultRounded(25) and resultRounded(24) and resultRounded(23));
   finalRisInf <= tentativeRisInf_d4 or Roverflowed; 
   Inf <= (30 downto 23 => '1') & (22 downto 0 => '0');
   NaN <= (30 downto 23 => '1') & (22 downto 0 => '1');
   R <= 
           Rsgn_d2 & Inf_d4 when ((not RisNaN_d4) and finalRisInf)='1'
      else '0'  & NaN_d4 when RisNaN_d4='1'
      else Rsgn_d2 & resultRounded(30 downto 0);
end architecture;

