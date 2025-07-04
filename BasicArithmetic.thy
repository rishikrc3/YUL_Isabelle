theory BasicArithmetic
  imports Main 
begin
type_synonym word  = nat  
type_synonym sword = int  

definition pstop   :: "word * word"          where "pstop      = (0, 0)"

(* --- basic arithmetic (totalised) --------------------------- *)
definition padd    :: "word => word => word"   where "padd  x y  = x + y"
definition psub    :: "word => word => word"   where "psub  x y  = x - y"
definition pmul    :: "word => word => word"   where "pmul  x y  = x * y"
definition pdiv    :: "word => word => word"   where "pdiv  x y  = (if y = 0 then 0 else x div y)"
definition psdiv   :: "sword => sword => sword" where "psdiv x y = (if y = 0 then 0 else x div y)"
definition pmod    :: "word => word => word"   where "pmod  x y  = (if y = 0 then 0 else x mod y)"
definition psmod   :: "sword => sword => sword" where "psmod x y = (if y = 0 then 0 else x mod y)"
definition pexp    :: "word => word => word"   where "pexp  x y  = x ^ y"


(* --- comparisons, return 1 / 0 ------------------------------ *)
definition plt     :: "word  => word  => word" where "plt  x y   = (if x <  y then 1 else 0)"
definition pgt     :: "word  => word  => word" where "pgt  x y   = (if x >  y then 1 else 0)"
definition pslt    :: "sword => sword => word" where "pslt x y   = (if x <  y then 1 else 0)"
definition psgt    :: "sword => sword => word" where "psgt x y   = (if x >  y then 1 else 0)"
definition peq     :: "word  => word  => word" where "peq  x y   = (if x =  y then 1 else 0)"
definition piszero :: "word  => word"         where "piszero x  = (if x = 0 then 1 else 0)"

(* ------------- padd / psub --------------------------------- *)
lemma padd_comm:        "padd x y = padd y x"                 by (simp add: padd_def)
lemma padd_zero_left:   "padd 0 x = x"                        by (simp add: padd_def)
lemma padd_zero_right:  "padd x 0 = x"                        by (simp add: padd_def)
lemma psub_zero:        "psub x 0 = x"                        by (simp add: psub_def)
lemma psub_self:        "psub x x = 0"                        by (simp add: psub_def)

(* ------------- pmul ---------------------------------------- *)
lemma pmul_comm:        "pmul x y = pmul y x"                 by (simp add: pmul_def)
lemma pmul_zero_left:   "pmul 0 x = 0"                        by (simp add: pmul_def)
lemma pmul_zero_right:  "pmul x 0 = 0"                        by (simp add: pmul_def)

(* ------------- pdiv / pmod --------------------------------- *)
lemma pdiv_self_non0:   "x ~= 0 ==> pdiv x x = 1"             by (simp add: pdiv_def)
lemma pmod_self_non0:   "x ~= 0 ==> pmod x x = 0"             by (simp add: pmod_def)

(* ------------- comparisons --------------------------------- *)
lemma peq_refl:         "peq x x = 1"                         by (simp add: peq_def)
lemma plt_irrefl:       "plt x x = 0"                         by (simp add: plt_def)
lemma plt_swap:         "plt x y = pgt y x"                   by (simp add: plt_def pgt_def)
lemma piszero_0:        "piszero 0 = 1"                       by (simp add: piszero_def)
lemma piszero_non0:     "x ~= 0 ==> piszero x = 0"            by (simp add: piszero_def)


end
