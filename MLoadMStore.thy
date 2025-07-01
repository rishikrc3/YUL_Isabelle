theory MLoadMStore
  imports Main
begin

type_synonym val    = nat
type_synonym memory = "val list"


definition empty_memory :: memory where
  "empty_memory = []"

definition mstore :: "memory => nat=> val=> memory" where
  "mstore mem addr v =
     (if addr < length mem
      then list_update mem addr v
      else mem @ replicate (addr - length mem) 0 @ [v])"

definition mload :: "memory => nat => val option" where
  "mload mem addr =
     (if addr < length mem
      then Some (mem ! addr)
      else None)"

fun mcopy :: "nat => nat => nat => memory => memory" where
  "mcopy _ _ 0 mem = mem"
| "mcopy t f (Suc s) mem =
     (case mload mem f of
        None   \<Rightarrow> mcopy (t + 1) (f + 1) s mem
      | Some v \<Rightarrow> mcopy (t + 1) (f + 1) s (mstore mem t v))"


(* Tests *)

value "empty_memory"
  (* = [] *)

value "mload empty_memory 10"
  (* = None *)

value "mstore empty_memory 4 255"
  (* = [0, 0, 0, 0, 255] *)

value "mload (mstore empty_memory 4 255) 4"
  (* = Some 255 *)
(*
  mload XXX ....
*)

value "mcopy 0 2 2 [10, 20, 30, 40, 50]"
value "mcopy 5 0 3 [1, 2, 3]"
value "mcopy 6 0 2 [10, 20]"
lemma test_mload_empty:
  "mload empty_memory 0 = None"
  by (simp add: mload_def empty_memory_def)

lemma test_mstore_basic:
  "mload (mstore empty_memory 10 42) 10 = Some 42"
  unfolding mload_def mstore_def empty_memory_def
  by (simp add: nth_append)


lemma test_mstore_other_addr_untouched:
  "mload (mstore empty_memory 5 99) 6 = None"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_multiple:
  "mload (mstore (mstore empty_memory 3 100) 4 200) 4 = Some 200"
  unfolding mload_def mstore_def empty_memory_def
  by (simp add: nth_append nth_list_update)


lemma test_mstore_overwrite:
  "mload (mstore (mstore empty_memory 1 11) 1 22) 1 = Some 22"
  by (simp add: mload_def mstore_def empty_memory_def)

lemma test_mstore_then_check_previous:
  "mload (mstore (mstore empty_memory 8 88) 9 99) 8 = Some 88"
  unfolding mload_def mstore_def empty_memory_def
  by (simp add: nth_append nth_list_update)

lemma test_mstore_and_empty_check:
  "mload (mstore empty_memory 7 77) 6 = Some 0"
  unfolding mload_def mstore_def empty_memory_def
  by (simp add: nth_append)


lemma test_mstore_zero_addr:
  "mload (mstore empty_memory 0 1) 0 = Some 1"
  by (simp add: mload_def mstore_def empty_memory_def)

section \<open>mcopy Test Lemmas\<close>

lemma test_mcopy_empty:
  "mcopy 0 0 0 empty_memory = empty_memory"
  "mcopy 5 10 0 [1,2,3] = [1,2,3]"
  by (simp_all add: empty_memory_def)




end
(*
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MemoryModel {
    mapping(uint256 => uint256) private mem;
    uint256 private maxIndex = 0;

    function mstore(uint256 addr, uint256 v) public {
        mem[addr] = v;
        if (addr >= maxIndex) {
            maxIndex = addr + 1;
        }
    }
    
    function mload(uint256 addr) public view returns (uint256) {
        if (addr >= maxIndex) {
            return type(uint256).max;
        }
        return mem[addr];
    }
    
    
    function isInitialized(uint256 addr) public view returns (bool) {
        return addr < maxIndex;
    
    function mcopy(uint256 t, uint256 f, uint256 s) public {
        for (uint256 i = 0; i < s; i++) {
            uint256 v = mload(f + i);
            // EVM semantics: treat the “none” sentinel as zero
            if (v == type(uint256).max) {
                v = 0;
            }
            mstore(t + i, v);
        }
    }
}*)