/- Pure compression roundtrip and ordinary cross-command state smoke. -/
import StructuralW10Cert20261016.CompressedCommands
open Lean Elab Command
elab "assert_w10_option" : command => do
  if maxRecDepth.get (← getOptions) != 4096 then
    throwError "expanded set_option did not persist"
w10_expand 2721 281 ["hR>~@=UD3iz`yi0%Z&ZmU2J5,5Y2pntD28>^{Z:AaIK|3&uBT'o--7U=/8+1deg0>-+E(T$/qhy&{iaoH!,mJs~ypAJ/T0Kp&{3nu$5TWgPv`;uT8nheVjoc!86$F}guZBOP7B6ey-oW{-$mzfLFF{hsxCEj:mjs&{!~I;fZ%3AY<+6rA)e4~j!)e<u-e,iXyS<8ad6Ap?)mSR^i3qEfS!yIx=ryrYu.G%~-vU+,AK}BcLUQkxd*$Zpv5K`6N,4%yegD_Y<{6GeMKq)'JZ:XSv'HX6[9m(c2/7ZbLp5*_SD37H>L8^jfGs}5OF",
"jh?CIZr&bVfoR7eOf_NDf!n9#a;s^F"]

assert_w10_option
theorem middle : answer = 42 := by decide
w10_expand 69 77 [";g}a=8dM`@.umQsHC]s)Bl/v{,]w&aN>F.1g-~O6cN5787nyg{l,)>hT;*WJG5Iaslw]TMmv-`w$!J5Pom]vE$i}}?[X'6"]

example : W10CompressedSmoke.seed = 41 := by decide
#print axioms W10CompressedSmoke.first
#print axioms W10CompressedSmoke.middle
#print axioms W10CompressedSmoke.second
