theory BitwiseOperations
  imports Main "HOL-Library.Bit_Operations"
begin


type_synonym yul_word = nat

definition yul_and :: "yul_word \<Rightarrow> yul_word \<Rightarrow> yul_word" where
  "yul_and x y \<equiv> x AND y"


end
