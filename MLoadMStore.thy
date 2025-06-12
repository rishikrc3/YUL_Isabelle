theory MLoadMStore
  imports Main
begin

type_synonym val    = nat
type_synonym memory = "nat => val option"


definition empty_memory :: memory where
  "empty_memory _ = None"


definition mstore :: "memory  =>  nat => val => memory" where
  "mstore mem addr v = mem(addr := Some v)"


definition mload :: "memory => nat => val option" where
  "mload mem addr = mem addr"


value "empty_memory 0"                         
value "mload empty_memory 10"                
value "mstore empty_memory 4 255 4"            
value "mload (mstore empty_memory 4 255) 4"    



lemma test_mload_empty:
  "mload empty_memory 0 = None"
  by (simp add: mload_def empty_memory_def)

lemma test_mstore_basic:
  "mload (mstore empty_memory 10 42) 10 = Some 42"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_other_addr_untouched:
  "mload (mstore empty_memory 5 99) 6 = None"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_multiple:
  "mload (mstore (mstore empty_memory 3 100) 4 200) 4 = Some 200"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_overwrite:
  "mload (mstore (mstore empty_memory 1 11) 1 22) 1 = Some 22"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_then_check_previous:
  "mload (mstore (mstore empty_memory 8 88) 9 99) 8 = Some 88"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_and_empty_check:
  "mload (mstore empty_memory 7 77) 6 = None"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_zero_addr:
  "mload (mstore empty_memory 0 1) 0 = Some 1"
  by (simp add: mload_def mstore_def empty_memory_def)

end
