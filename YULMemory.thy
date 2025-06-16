theory YULMemory
  imports Main
begin

type_synonym val     = nat
type_synonym storage = "nat \<Rightarrow> val option"

definition empty_storage :: storage where
  "empty_storage _ = None"

definition sstore :: "storage \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> storage" where
  "sstore st slot v = st(slot := Some v)"

definition sload :: "storage \<Rightarrow> nat \<Rightarrow> val option" where
  "sload st slot = st slot"

(* Unit Tests *)

lemma test_sload_written:
  "sload (sstore empty_storage 3 9) 3 = Some 9"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sload_unset:
  "sload empty_storage 5 = None"
  by (simp add: sload_def empty_storage_def)

lemma test_sstore_overwrite:
  "sload (sstore (sstore empty_storage 3 10) 3 42) 3 = Some 42"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_slot_9:
  "(sstore empty_storage 9 3) 9 = Some 3"
  by (simp add: sstore_def empty_storage_def)

lemma test_sload_after_store:
  "sload (sstore empty_storage 9 3) 9 = Some 3"
  by (simp add: sload_def sstore_def empty_storage_def)

end
