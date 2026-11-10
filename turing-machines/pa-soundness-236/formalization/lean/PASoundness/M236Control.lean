import PASoundness.M236UnifiedDecrement
/-! Source-independent return-control decoding for literal grammar paths. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- The one-separator return retains an exact prefix of the original control
word and its terminating marker; this does not identify a source jump. -/
theorem one_return (runs rest : List (Fin 6)) (word : List Bool) (scratch : Nat)
    (bit : Bool) (pcTail : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hsplit : counterWord runs = List.replicate scratch true ++ false :: counterWord rest)
    (hprefix : counterPush rest [] = true :: bit :: pcTail) :
    ([true, true, false] ++ word) = (counterWord rest).reverse ++ false :: List.replicate scratch true ∧
      (counterWord rest).reverse ++ [true] = [true, true, bit] ++ pcTail := by
  constructor
  · have h := congrArg List.reverse hsplit
    rw [hword, List.reverse_reverse] at h
    simpa [List.reverse_append, List.reverse_cons] using h
  · have h := Redispatch.counter_push_reverse rest []
    rw [hprefix] at h
    simpa using h.symm

/-- The two-separator zero return retains the exact control-word prefix and
both erased finite scratch suffixes. -/
theorem zero_return (runs rest : List (Fin 6)) (word : List Bool) (scratch1 scratch2 : Nat)
    (bit : Bool) (pcTail : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hsplit : counterWord runs = List.replicate scratch1 true ++ false ::
      (List.replicate scratch2 true ++ false :: counterWord rest))
    (hprefix : counterPush rest [] = true :: bit :: pcTail) :
    ([true, true, false] ++ word) = (counterWord rest).reverse ++ false ::
        (List.replicate scratch2 true ++ false :: List.replicate scratch1 true) ∧
      (counterWord rest).reverse ++ [true] = [true, true, bit] ++ pcTail := by
  constructor
  · have h := congrArg List.reverse hsplit
    rw [hword, List.reverse_reverse] at h
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using h
  · have h := Redispatch.counter_push_reverse rest []
    rw [hprefix] at h
    simpa using h.symm

/-- Every named increment path has a checked finite return-control
factorization, without assuming a counter encoding. -/
theorem increment_control (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none)) :
    ∃ (pcHead : List Bool) (scratch : Nat) (bit : Bool) (pcTail : List Bool),
      ([true, true, false] ++ word) = pcHead ++ false :: List.replicate scratch true ∧
      pcHead ++ [true] = [true, true, bit] ++ pcTail := by
  obtain ⟨runs, hword⟩ := Redispatch.named_path_codec hpath
  obtain ⟨scratch, rest, bit, pcTail, hsplit, hprefix⟩ := Redispatch.counter_split_control runs word hword
  exact ⟨(counterWord rest).reverse, scratch, bit, pcTail, one_return runs rest word scratch bit pcTail hword hsplit hprefix⟩

/-- Every named decrement path has a checked two-separator factorization for
its zero return; the selected source branch is still a separate relation. -/
theorem decrement_zero_control (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)) :
    ∃ (pcHead : List Bool) (scratch1 scratch2 : Nat) (bit : Bool) (pcTail : List Bool),
      ([true, true, false] ++ word) = pcHead ++ false ::
        (List.replicate scratch2 true ++ false :: List.replicate scratch1 true) ∧
      pcHead ++ [true] = [true, true, bit] ++ pcTail := by
  obtain ⟨runs, hword⟩ := Redispatch.named_path_codec hpath
  have hfalse := DecrementRoot.decrement_path_has_false r word write hpath
  obtain ⟨scratch1, scratch2, rest, bit, pcTail, hsplit, hprefix⟩ :=
    DecrementRoot.counter_split_twice runs word hword hfalse
  exact ⟨(counterWord rest).reverse, scratch1, scratch2, bit, pcTail,
    zero_return runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix⟩

/-- Remove the initial finite run of ones and its first zero. -/
def pop (xs : List Bool) : Option (Nat × List Bool) :=
  match xs with
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (pop rest).map (fun (n, tail) => (n + 1, tail))

theorem pop_run (scratch : Nat) (rest : List Bool) :
    pop (List.replicate scratch true ++ false :: rest) = some (scratch, rest) := by
  induction scratch with
  | zero => rfl
  | succ scratch ih => simp [List.replicate_succ, pop, ih]

/-- The first and second return controls are decoded solely from path bits. -/
def decodeOne (word : List Bool) : Option (Bool × List Bool) := do
  let (_, rest) ← pop ([true, true, false] ++ word).reverse
  match rest.reverse ++ [true] with
  | true :: true :: bit :: tail => some (bit, tail)
  | _ => none

def decodeZero (word : List Bool) : Option (Bool × List Bool) := do
  let (_, rest1) ← pop ([true, true, false] ++ word).reverse
  let (_, rest2) ← pop rest1
  match rest2.reverse ++ [true] with
  | true :: true :: bit :: tail => some (bit, tail)
  | _ => none

theorem decodeOne_named (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none)) :
    ∃ (bit : Bool) (pcTail : List Bool), decodeOne word = some (bit, pcTail) := by
  obtain ⟨runs, hword⟩ := Redispatch.named_path_codec hpath
  obtain ⟨scratch, rest, bit, pcTail, hsplit, hprefix⟩ := Redispatch.counter_split_control runs word hword
  have hreturn := (one_return runs rest word scratch bit pcTail hword hsplit hprefix).2
  refine ⟨bit, pcTail, ?_⟩
  unfold decodeOne
  rw [← hword, hsplit, pop_run]
  simp [hreturn]

theorem decodeZero_named (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)) :
    ∃ (bit : Bool) (pcTail : List Bool), decodeZero word = some (bit, pcTail) := by
  obtain ⟨runs, hword⟩ := Redispatch.named_path_codec hpath
  have hfalse := DecrementRoot.decrement_path_has_false r word write hpath
  obtain ⟨scratch1, scratch2, rest, bit, pcTail, hsplit, hprefix⟩ :=
    DecrementRoot.counter_split_twice runs word hword hfalse
  have hreturn := (zero_return runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix).2
  refine ⟨bit, pcTail, ?_⟩
  unfold decodeZero
  rw [← hword, hsplit, pop_run]
  simp [pop_run, hreturn]

/-- Exact control decoding from a proved two-scratch counter split. -/
theorem decodeZero_of_split (runs rest : List (Fin 6)) (word : List Bool)
    (scratch1 scratch2 : Nat) (bit : Bool) (pcTail : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hsplit : counterWord runs = List.replicate scratch1 true ++ false ::
      (List.replicate scratch2 true ++ false :: counterWord rest))
    (hprefix : counterPush rest [] = true :: bit :: pcTail) :
    decodeZero word = some (bit, pcTail) := by
  have hreturn := (zero_return runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix).2
  unfold decodeZero
  rw [← hword, hsplit, pop_run]
  simp [pop_run, hreturn]

/-- The literal zero-branch return's recorded control suffix is exactly the
result of the fixed, source-independent path-bit decoder. -/
theorem physical_root_zero_decoded (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat) (bit : Bool)
      (pcTail : List Bool) (finish : Config 237),
      decodeZero word = some (bit, pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨runs, rest, time, endHead, scratch1, scratch2, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_zero_detail registers r hzero reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch1, scratch2, bit, pcTail, finish,
    decodeZero_of_split runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix,
    ht, hp, hr, hq, hd, hout⟩

example : decodeZero [false, false, false, false] = some (false, [false, false, true]) := by decide
example : decodeZero [false, false, true, false, false] = some (false, [false, false, true, true]) := by decide
example : decodeZero [false, false, false, false] ≠ some (true, [false, false, true]) := by decide

/-- Decrement's positive branch uses the same one-separator path decoder. -/
theorem decodeOne_decrement_named (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)) :
    ∃ (bit : Bool) (pcTail : List Bool), decodeOne word = some (bit, pcTail) := by
  obtain ⟨runs, hword⟩ := Redispatch.named_path_codec hpath
  obtain ⟨scratch, rest, bit, pcTail, hsplit, hprefix⟩ := Redispatch.counter_split_control runs word hword
  have hreturn := (one_return runs rest word scratch bit pcTail hword hsplit hprefix).2
  refine ⟨bit, pcTail, ?_⟩
  unfold decodeOne
  rw [← hword, hsplit, pop_run]
  simp [hreturn]

theorem decodeOne_of_split (runs rest : List (Fin 6)) (word : List Bool)
    (scratch : Nat) (bit : Bool) (pcTail : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hsplit : counterWord runs = List.replicate scratch true ++ false :: counterWord rest)
    (hprefix : counterPush rest [] = true :: bit :: pcTail) :
    decodeOne word = some (bit, pcTail) := by
  have hreturn := (one_return runs rest word scratch bit pcTail hword hsplit hprefix).2
  unfold decodeOne
  rw [← hword, hsplit, pop_run]
  simp [hreturn]

/-- The positive decrement's physical return tail equals the one-separator
path decoder, including the explicit additional zero reserve block. -/
theorem physical_root_positive_decoded (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat)
    (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail : List Bool) (finish : Config 237),
      decodeOne word = some (bit, pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨runs, rest, time, endHead, scratch, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_positive_detail registers r value hvalue reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch, bit, pcTail, finish,
    decodeOne_of_split runs rest word scratch bit pcTail hword hsplit hprefix,
    ht, hp, hr, hq, hd, hout⟩

/-- The increment's literal return tail equals the one-separator decoder. -/
theorem physical_root_increment_decoded (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail : List Bool) (finish : Config 237),
      decodeOne word = some (bit, pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨runs, rest, time, endHead, scratch, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd⟩ :=
    Redispatch.physical_root_increment_detail registers r reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch, bit, pcTail, finish,
    decodeOne_of_split runs rest word scratch bit pcTail hword hsplit hprefix,
    ht, hp, hr, hq, hd⟩
end PASoundness.M236.Control
