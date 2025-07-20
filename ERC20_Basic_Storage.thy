theory ERC20_Basic_Storage
  imports SLoadSStore
begin

type_synonym word256 = nat

(* Storage slots for owner and totalSupply *)
definition ownerPos :: nat
  where "ownerPos = 0"

definition totalSupplyPos :: nat
  where "totalSupplyPos = 1"

(* Compute the storage slot for an account's balance *)
definition accountToStorageOffset :: "word256 => nat"
  where "accountToStorageOffset acc = (0x1000 :: nat) + acc"

(* Read operations on storage *)
definition owner :: "storage => val option"
  where "owner st = sload st ownerPos"

definition totalSupply :: "storage => val option"
  where "totalSupply st = sload st totalSupplyPos"

definition balanceOf :: "storage => word256 => val option"
  where "balanceOf st acc = sload st (accountToStorageOffset acc)"

(* === Test lemmas === *)
lemma test_owner_empty:
  "owner empty_storage = None"
  by (simp add: owner_def empty_storage_def sload_def)

lemma test_owner_set:
  "owner (sstore empty_storage ownerPos 123) = Some 123"
  by (simp add: owner_def sstore_def empty_storage_def sload_def)

lemma test_totalSupply_empty:
  "totalSupply empty_storage = None"
  by (simp add: totalSupply_def empty_storage_def sload_def)

lemma test_totalSupply_set:
  "totalSupply (sstore empty_storage totalSupplyPos 456) = Some 456"
  by (simp add: totalSupply_def sstore_def empty_storage_def sload_def)

lemma test_accountToStorageOffset:
  "accountToStorageOffset 10 = (0x1000 :: nat) + 10"
  by (simp add: accountToStorageOffset_def)

lemma test_balanceOf_empty:
  "balanceOf empty_storage 42 = None"
  by (simp add: balanceOf_def empty_storage_def sload_def)

lemma test_balanceOf_set:
  "balanceOf (sstore empty_storage (accountToStorageOffset 7) 789) 7 = Some 789"
  by (simp add: balanceOf_def sstore_def empty_storage_def sload_def
                accountToStorageOffset_def)

end
