theory Proof
  imports Main
begin

type_synonym word = nat  

definition STOP   :: "word \<times> word"          where "STOP \<equiv> (0, 0)"

definition yadd   :: "word \<Rightarrow> word \<Rightarrow> word"   where "yadd x y \<equiv> x + y"
definition ysub   :: "word \<Rightarrow> word \<Rightarrow> word"   where "ysub x y \<equiv> x - y"
definition ymul   :: "word \<Rightarrow> word \<Rightarrow> word"   where "ymul x y \<equiv> x * y"
definition ydiv   :: "word \<Rightarrow> word \<Rightarrow> word"   where "ydiv x y \<equiv> (if y = 0 then 0 else x div y)"
definition ymod   :: "word \<Rightarrow> word \<Rightarrow> word"   where "ymod x y \<equiv> (if y = 0 then 0 else x mod y)"
definition ysmod  :: "int  \<Rightarrow> int  \<Rightarrow> int"    where "ysmod x y \<equiv> (if y = 0 then 0 else x mod y)"
definition yexp   :: "word \<Rightarrow> word \<Rightarrow> word"   where "yexp x y \<equiv> x ^ y"
definition ylt    :: "word \<Rightarrow> word \<Rightarrow> word"   where "ylt  x y \<equiv> (if x < y then 1 else 0)"
definition ygt    :: "word \<Rightarrow> word \<Rightarrow> word"   where "ygt  x y \<equiv> (if x > y then 1 else 0)"
definition yslt   :: "int  \<Rightarrow> int  \<Rightarrow> word"   where "yslt x y \<equiv> (if x < y then 1 else 0)"
definition ysgt   :: "int  \<Rightarrow> int  \<Rightarrow> word"   where "ysgt x y \<equiv> (if x > y then 1 else 0)"
definition yeq    :: "word \<Rightarrow> word \<Rightarrow> word"   where "yeq  x y \<equiv> (if x = y then 1 else 0)"
definition yiszero:: "word \<Rightarrow> word"          where "yiszero x \<equiv> (if x = 0 then 1 else 0)"


lemma proof_stop:   "STOP = (0,0)"                       by (simp add: STOP_def)
lemma proof_add:    "yadd x y = x + y"                   by (simp add: yadd_def)
lemma proof_sub:    "ysub x y = x - y"                   by (simp add: ysub_def)
lemma proof_mul:    "ymul x y = x * y"                   by (simp add: ymul_def)
lemma proof_div:    "ydiv x y = (if y = 0 then 0 else x div y)"
                                                        by (simp add: ydiv_def)
lemma proof_mod:    "ymod x y = (if y = 0 then 0 else x mod y)"
                                                        by (simp add: ymod_def)
lemma proof_smod:   "ysmod x y = (if y = 0 then 0 else x mod y)"
                                                        by (simp add: ysmod_def)
lemma proof_exp:    "yexp x y = x ^ y"                  by (simp add: yexp_def)
lemma proof_lt:     "ylt  x y = (if x < y then 1 else 0)" by (simp add: ylt_def)
lemma proof_gt:     "ygt  x y = (if x > y then 1 else 0)" by (simp add: ygt_def)
lemma proof_slt:    "yslt x y = (if x < y then 1 else 0)" by (simp add: yslt_def)
lemma proof_sgt:    "ysgt x y = (if x > y then 1 else 0)" by (simp add: ysgt_def)
lemma proof_eq:     "yeq  x y = (if x = y then 1 else 0)" by (simp add: yeq_def)
lemma proof_iszero: "yiszero x = (if x = 0 then 1 else 0)" by (simp add: yiszero_def)

(* UNIT TESTS*)

(* STOP *)
lemma test_stop_1: "fst STOP = 0" by (simp add: STOP_def)
lemma test_stop_2: "snd STOP = 0" by (simp add: STOP_def)

(* yadd *)
lemma test_yadd_1: "yadd 2 3 =5" by (simp add: yadd_def)
lemma test_yadd_2: "yadd 0 4 = 4" by (simp add: yadd_def)

(* ysub *)
lemma test_ysub_1: "ysub 5 2 = 3" by (simp add: ysub_def)
lemma test_ysub_2: "ysub 3 5 = 0" by (simp add: ysub_def)

(* ymul *)
lemma test_ymul_1: "ymul 3 4 = 12" by (simp add: ymul_def)
lemma test_ymul_2: "ymul 0 7 = 0"  by (simp add: ymul_def)

(* ydiv *)
lemma test_ydiv_1: "ydiv 10 2 = 5" by (simp add: ydiv_def)
lemma test_ydiv_2: "ydiv 10 0 = 0" by (simp add: ydiv_def)

(* ymod *)
lemma test_ymod_1: "ymod 10 3 = 1" by (simp add: ymod_def)
lemma test_ymod_2: "ymod 7 0 = 0"  by (simp add: ymod_def)

(* ysmod *)
lemma test_ysmod_1: "ysmod (-10) 3 = 2" by (simp add: ysmod_def)
lemma test_ysmod_2: "ysmod 7 0 = 0"     by (simp add: ysmod_def)

(* yexp *)
lemma test_yexp_1: "yexp 2 3 = 8" by (simp add: yexp_def)
lemma test_yexp_2: "yexp 5 0 = 1" by (simp add: yexp_def)

(* ylt *)
lemma test_ylt_1: "ylt 2 5 = 1" by (simp add: ylt_def)
lemma test_ylt_2: "ylt 7 4 = 0" by (simp add: ylt_def)

(* ygt *)
lemma test_ygt_1: "ygt 5 2 = 1" by (simp add: ygt_def)
lemma test_ygt_2: "ygt 3 8 = 0" by (simp add: ygt_def)

(* yslt *)
lemma test_yslt_1: "yslt (-2) 3 = 1" by (simp add: yslt_def)
lemma test_yslt_2: "yslt 7 4 = 0"    by (simp add: yslt_def)

(* ysgt *)
lemma test_ysgt_1: "ysgt 5 (-1) = 1" by (simp add: ysgt_def)
lemma test_ysgt_2: "ysgt (-3) 0 = 0" by (simp add: ysgt_def)

(* yeq *)
lemma test_yeq_1: "yeq 3 3 = 1" by (simp add: yeq_def)
lemma test_yeq_2: "yeq 4 5 = 0" by (simp add: yeq_def)

(* yiszero *)
lemma test_yiszero_1: "yiszero 0 = 1" by (simp add: yiszero_def)
lemma test_yiszero_2: "yiszero 7 = 0" by (simp add: yiszero_def)