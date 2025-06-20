theory SLoadSStore
  imports Main
begin

type_synonym val     = nat
type_synonym storage = "nat => val option"

definition empty_storage :: storage where
  "empty_storage _ = None"

definition sstore :: "storage =>  nat => val => storage" where
  "sstore st slot v = st(slot := Some v)"

definition sload :: "storage => nat => val option" where
  "sload st slot = st slot"

(* Checking the default value at slot 5 in an empty storage — should be None *)
value "empty_storage 5"

(* Checking the value at slot 3 in empty storage using sload — should also be None *)
value "sload empty_storage 3"

(* Storing value 99 at slot 3 — this evaluates to the internal representation: Some 99 at slot 3 *)
value "(sstore empty_storage 3 99) 3"

(* Using sload to check the value at slot 3 after storing 99 — should return Some 99 *)
value "sload (sstore empty_storage 3 99) 3"


lemma test_sload_empty_slot:
  "sload empty_storage 0 = None"
  by (simp add: sload_def empty_storage_def)

lemma test_sload_unset_slot:
  "sload empty_storage 100 = None"
  by (simp add: sload_def empty_storage_def)

lemma test_sstore_basic:
  "sload (sstore empty_storage 3 99) 3 = Some 99"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_slot_not_affecting_other:
  "sload (sstore empty_storage 3 99) 2 = None"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_multiple_slots:
  "sload (sstore (sstore empty_storage 3 99) 4 88) 4 = Some 88"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_overwrite_same_slot:
  "sload (sstore (sstore empty_storage 5 123) 5 456) 5 = Some 456"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_and_check_previous_slot:
  "sload (sstore (sstore empty_storage 1 42) 2 21) 1 = Some 42"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_and_empty_slot_check:
  "sload (sstore empty_storage 9 999) 8 = None"
  by (simp add: sload_def sstore_def empty_storage_def)

lemma test_sstore_zero_slot:
  "sload (sstore empty_storage 0 7) 0 = Some 7"
  by (simp add: sload_def sstore_def empty_storage_def)

end
