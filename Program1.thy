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
(* do it using case*)
function power :: "word => word => word" where
  "power base n = 
     (if n = 0 then 1
      else if n = 1 then base
      else let r = power (pmul base base) (pdiv n 2) in
           if pmod n 2 = 1 then pmul base r else r)"
  by pat_completeness auto

termination
  apply (relation "measure (\<lambda>(_, n). n)")
  apply auto
  apply (simp add: pdiv_def)
  done


(* 
    function power(base, exponent) -> result
    {
        switch exponent
        case 0 { result := 1 }
        case 1 { result := base }
        default
        {
            result := power(mul(base, base), div(exponent, 2))
            switch mod(exponent, 2)
                case 1 { result := mul(base, result) }
        }
    }
 
*)



value "power 2 0"   (* 1   *)
value "power 2 1"   (* 2   *)
value "power 2 2"   (* 4   *)
value "power 2 5"   (* 32  *)
value "power 3 4"   (* 81  *)
value "power 5 3"   (* 125 *)
value "power 10 3"  (* 1000 *)
value "power 0 5"   (* 0   *)



lemma power_0 [simp]:   "power b 0 = 1"
  by simp

lemma power_1 [simp]:   "power b 1 = b"
  by simp

lemma power_two:        "power b 2 = pmul b b"
  by (simp add: pdiv_def pmod_def pmul_def)

lemma power_zero_base: "1 <= n ==> power 0 n = 0"
  by (induct n rule: nat_less_induct)
     (auto simp: pdiv_def pmod_def pmul_def)

lemma power_one_base:   "power 1 n = 1"
  by (induction n rule: nat_less_induct)
     (auto simp: pdiv_def pmod_def pmul_def)





end
