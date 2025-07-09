theory ERC20_Utilities
  imports Main
begin

type_synonym word256 = nat
type_synonym yul_bool = nat

definition yul_iszero :: "word256 => yul_bool" where
  "yul_iszero x = (if x = 0 then 1 else 0)"

definition yul_gt :: "word256 => word256 => yul_bool" where
  "yul_gt a b = (if a > b then 1 else 0)"

definition yul_lt :: "word256 => word256 => yul_bool" where
  "yul_lt a b = (if a < b then 1 else 0)"

definition yul_lte :: "word256 => word256 => yul_bool" where
  "yul_lte a b = yul_iszero (yul_gt a b)"

definition yul_gte :: "word256 => word256 => yul_bool" where
  "yul_gte a b = yul_iszero (yul_lt a b)"

lemma yul_lte_correct:
  "yul_lte a b = (if a <= b then 1 else 0)"
  unfolding yul_lte_def yul_iszero_def yul_gt_def
  by auto

lemma yul_gte_correct:
  "yul_gte a b = (if a >= b then 1 else 0)"
  unfolding yul_gte_def yul_iszero_def yul_lt_def
  by auto

lemma test_lte_basic:
  "yul_lte 5 10 = 1"
  by (simp add: yul_lte_correct)

lemma test_lte_false:
  "yul_lte 10 5 = 0"
  by (simp add: yul_lte_correct)

lemma test_lte_equal:
  "yul_lte 7 7 = 1"
  by (simp add: yul_lte_correct)

lemma test_gte_basic:
  "yul_gte 10 5 = 1"
  by (simp add: yul_gte_correct)

lemma test_gte_false:
  "yul_gte 5 10 = 0"
  by (simp add: yul_gte_correct)

lemma test_gte_equal:
  "yul_gte 7 7 = 1"
  by (simp add: yul_gte_correct)

lemma test_lte_zero_zero:
  "yul_lte 0 0 = 1"
  by (simp add: yul_lte_correct)

lemma test_lte_zero_one:
  "yul_lte 0 1 = 1"
  by (simp add: yul_lte_correct)

lemma test_lte_one_zero:
  "yul_lte 1 0 = 0"
  by (simp add: yul_lte_correct)

lemma test_gte_zero_zero:
  "yul_gte 0 0 = 1"
  by (simp add: yul_gte_correct)

lemma test_gte_one_zero:
  "yul_gte 1 0 = 1"
  by (simp add: yul_gte_correct)

lemma test_gte_zero_one:
  "yul_gte 0 1 = 0"
  by (simp add: yul_gte_correct)

lemma test_lte_large:
  "yul_lte 1000000 1000001 = 1"
  by (simp add: yul_lte_correct)

lemma test_gte_large:
  "yul_gte 1000001 1000000 = 1"
  by (simp add: yul_gte_correct)

lemma test_lte_boundary:
  "yul_lte 1 2 = 1"
  by (simp add: yul_lte_correct)

lemma test_gte_boundary:
  "yul_gte 2 1 = 1"
  by (simp add: yul_gte_correct)

lemma test_lte_gte_dual:
  "yul_lte a b = yul_gte b a"
  by (simp add: yul_lte_correct yul_gte_correct)

lemma test_return_type_lte:
  "yul_lte a b = 0 \<or> yul_lte a b = 1"
  by (simp add: yul_lte_correct)

lemma test_return_type_gte:
  "yul_gte a b = 0 \<or> yul_gte a b = 1"
  by (simp add: yul_gte_correct)

end