theory ERC20_Calldata
  imports Main
begin

type_synonym word256 = nat

type_synonym calldata = "nat => word256"

definition BYTES_PER_WORD :: nat where "BYTES_PER_WORD = 32"

definition HEADER_SIZE :: nat where "HEADER_SIZE = 4"

definition TWO_POW_224 :: nat where "TWO_POW_224 = 2^224"

abbreviation SELECTOR_transfer :: nat where "SELECTOR_transfer == 0xa9059cbb"
abbreviation SELECTOR_approve  :: nat where "SELECTOR_approve  == 0x095ea7b3"
abbreviation SELECTOR_balanceOf :: nat where "SELECTOR_balanceOf == 0x70a08231"

record evm_context =
  calldata_content :: calldata
  calldata_size    :: nat

definition calldataload :: "evm_context => nat => word256" where
  "calldataload ctx p == calldata_content ctx p"

definition calldatasize :: "evm_context => nat" where
  "calldatasize ctx == calldata_size ctx"

definition selector :: "evm_context => word256" where
  "selector ctx == calldataload ctx 0 div TWO_POW_224"

definition decode_uint :: "evm_context => nat => word256 option" where
  "decode_uint ctx i ==
     (let pos = HEADER_SIZE + i * BYTES_PER_WORD in
      if calldatasize ctx < pos + BYTES_PER_WORD
      then None
      else Some (calldataload ctx pos))"

lemma selector_range:
  assumes "calldataload ctx 0 < 2^256"
  shows   "selector ctx < 2^32"
  using assms
  unfolding selector_def TWO_POW_224_def
  by (simp add: power_add)

lemma decode_uint_size:
  assumes "decode_uint ctx i = Some v"
  shows   "calldatasize ctx >= HEADER_SIZE + (i + 1) * BYTES_PER_WORD"
  using assms
  unfolding decode_uint_def BYTES_PER_WORD_def HEADER_SIZE_def Let_def calldatasize_def
  by (auto split: if_splits)

end
