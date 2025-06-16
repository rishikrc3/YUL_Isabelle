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
    }
}*)