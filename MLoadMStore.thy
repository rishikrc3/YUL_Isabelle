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

section \<open>mcopy \<close>

fun mcopy :: "nat => nat => nat => memory => memory" where
  "mcopy t f 0 mem = mem"
| "mcopy t f (Suc s) mem =
     mcopy (t + 1) (f + 1) s
       (mstore mem t (case mload mem f of None => 0 | Some v => v))"

value "mcopy 3 0 3 (mstore (mstore (mstore empty_memory 0 1) 1 2) 2 3)"
(* expected result: [1,2,3,1,2,3] *)


(* Let's start with simple unit tests for mcopy *)
lemma mcopy_single_step:
  "mcopy 0 0 1 [42] = [42]"
  by (simp add: mload_def mstore_def)

lemma mcopy_single_step_empty:
  "mcopy 0 0 1 [] = [0]"
  by (simp add: mload_def mstore_def)

(* Let's try a simpler two-step case first *)
lemma mcopy_simple_copy:
  "mcopy 1 0 1 [5] = [5, 5]"
  by (simp add: mload_def mstore_def)

lemma mcopy_two_steps:
  "mcopy 2 0 2 [1, 2] = [1, 2, 1, 2]"
  by eval


(* Helper lemmas for mstore length *)
lemma mstore_length_in_bounds:
  "addr < length mem --> length (mstore mem addr v) = length mem"
  by (simp add: mstore_def)

lemma mstore_length_extend:
  "addr >= length mem --> length (mstore mem addr v) = addr + 1"
  by (simp add: mstore_def)

(* Just to verify mcopy actually copies correctly *)

lemma mcopy_correctness_simple:
  "mload (mcopy 1 0 1 [42]) 1 = Some 42"
  by eval




section "A tiny example program that stores v at 0 and copies it to 1"


definition simple_program :: "val => memory" where
  "simple_program v = mcopy 1 0 1 (mstore empty_memory 0 v)"

lemma simple_program_test:
  "simple_program 42 = [42, 42]"
  by (simp add: simple_program_def mstore_def
                mload_def empty_memory_def)

lemma store_copy_load_same:
  "mload (simple_program v) 0 = mload (simple_program v) 1"
  by (simp add: simple_program_def mstore_def
                mload_def empty_memory_def)

lemma concrete_store_copy_same:
  "mload (simple_program 99) 0 = Some 99 \<and>
   mload (simple_program 99) 1 = Some 99"
  by (simp add: simple_program_def mstore_def
                mload_def empty_memory_def)

value "simple_program 0"
(* = [0, 0] *)

value "simple_program 5"
(* = [5, 5] *)

value "simple_program 42"
(* = [42, 42] *)

value "simple_program 99"
(* = [99, 99] *)


end