theory Program1
  imports Main
begin

type_synonym word = nat

definition pmul :: "word => word => word" where
  "pmul x y = x * y"

definition pdiv :: "word => word => word" where
  "pdiv x y = (if y = 0 then 0 else x div y)"

definition pmod :: "word => word => word" where
  "pmod x y = (if y = 0 then 0 else x mod y)"


value "pmul 3 4"    
value "pmul 0 5"     

value "pdiv 10 2"    
value "pdiv 10 0"     

value "pmod 10 3"   
value "pmod 10 0"   

lemma pmul_comm: "pmul x y = pmul y x"
  unfolding pmul_def by simp

lemma pmul_zero_left: "pmul 0 x = 0"
  unfolding pmul_def by simp

lemma pmul_zero_right: "pmul x 0 = 0"
  unfolding pmul_def by simp


end
