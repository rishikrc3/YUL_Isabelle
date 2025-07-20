theory ERC20_Arithmetic
  imports Main
begin

type_synonym word256 = nat


definition safeAdd :: "word256 => word256 => word256 option" where
  "safeAdd a b = (if a + b < 2^256 then Some (a + b) else None)"


lemma safeAdd_no_overflow:
  assumes "a + b < 2^256"
  shows   "safeAdd a b = Some (a + b)"
  using assms
  unfolding safeAdd_def
  by simp

lemma safeAdd_overflow:
  assumes "a + b \<ge> 2^256"
  shows   "safeAdd a b = None"
  using assms
  unfolding safeAdd_def
  by simp

lemma test_safeAdd_basic:
  "safeAdd 5 7 = Some 12"
  by (simp add: safeAdd_def)

lemma test_safeAdd_overflow_edge:
  "safeAdd (2^256 - 1) 1 = None"
  by (simp add: safeAdd_def)

end
