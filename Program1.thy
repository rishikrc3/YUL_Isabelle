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


function power :: "word => word => word" where
  "power base n =
     (case n of
        0           => 1
      | Suc 0       => base
      | Suc (Suc m) =>
           (let r = power (pmul base base) (pdiv (Suc (Suc m)) 2)
            in case pmod (Suc (Suc m)) 2 of
                   0 => r
                 | _ => pmul base r))"
  by pat_completeness auto        

lemma pdiv_less_self: "2 <= n ==> pdiv n 2 < n"
  unfolding pdiv_def by (simp)
termination
  by (relation "measure (%(_,n). n)")
     (auto simp: pdiv_less_self)

                                  
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

value "power 2 0"    (* 1    *)
value "power 2 1"    (* 2    *)
value "power 2 2"    (* 4    *)
value "power 2 5"    (* 32   *)
value "power 3 4"    (* 81   *)
value "power 5 3"    (* 125  *)
value "power 10 3"   (* 1000 *)
value "power 0 5"    (* 0    *)

lemma power_0 [simp]: "power b 0 = 1"
  by simp
lemma power_1 [simp]: "power b 1 = b"
  by simp
lemma power_two: "power b 2 = pmul b b"
  by (simp add: pdiv_def pmod_def pmul_def)


end