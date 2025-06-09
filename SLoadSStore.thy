theory SLoadSStore
  imports Main
begin

type_synonym val     = nat
type_synonym storage = "nat => val option"

definition empty_storage :: storage where
  "empty_storage _ = None"

definition sstore :: "storage => nat => val => storage" where
  "sstore st slot v = st(slot := Some v)"

lemma test_sstore_new_slot:
  "(sstore empty_storage 3 99) 3 = Some 99"
  by (simp add: sstore_def empty_storage_def)

lemma test_sstore_other_slot_unchanged:
  "(sstore empty_storage 3 99) 2 = None"
  by (simp add: sstore_def empty_storage_def)

lemma test_sstore_overwrite:
  "((sstore (sstore empty_storage 3 10) 3 20) 3) = Some 20"
  by (simp add: sstore_def empty_storage_def)

end
