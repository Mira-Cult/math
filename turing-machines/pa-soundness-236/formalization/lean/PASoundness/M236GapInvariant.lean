import PASoundness.M236AdjacentCoverage
import PASoundness.M236SkipSuccessor
/-! Conservation of control length plus zero gap for normal physical returns. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- The finite literal grammar has no leaf deeper than 25 bits. -/
theorem leaf_length_checked : Grammar.completePaths.all (fun w => decide (w.length ≤ 25)) = true := by decide

theorem leaf_length_le (word : List Bool) (h : Grammar.LeafPath Grammar.nodes 157 word) :
    word.length ≤ 25 := by
  have hm := Grammar.every_leaf_path word h
  exact of_decide_eq_true ((List.all_eq_true.mp leaf_length_checked) word hm)

/-- A normal return trades each removed trailing one for one extra zero of
gap; this is an exact path-length identity. -/
theorem normal_length (runs rest : List (Fin 6)) (word : List Bool) (scratch : Nat)
    (bit : Bool) (pcTail : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hsplit : counterWord runs = List.replicate scratch true ++ false :: counterWord rest)
    (hprefix : counterPush rest [] = true :: bit :: pcTail) :
    word.length = scratch + pcTail.length := by
  obtain ⟨h1, h2⟩ := one_return runs rest word scratch bit pcTail hword hsplit hprefix
  have hl1 := congrArg List.length h1
  have hl2 := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse,
    List.length_replicate] at hl1 hl2
  omega

/-- Given enough total control space for the successor, a normal return is
exactly another prepared root tape with two separator zeros. The sum of gap
and path length is conserved. -/
theorem normal_gap_factor (word next pcTail : List Bool) (scratch gap : Nat) (bit : Bool)
    (hpair : (word, next) ∈ adjacentPaths) (hdecode : decodeOne word = some (bit, pcTail))
    (hlen : word.length = scratch + pcTail.length)
    (hmargin : next.length ≤ gap + word.length) (suffix : List Bool) :
    ∃ gap', pcTail ++ (List.replicate (gap + scratch + 2) false ++ suffix) =
        next ++ false :: false :: (List.replicate gap' false ++ suffix) ∧
      next.length + gap' = word.length + gap := by
  obtain ⟨b, p, hd, he, hbound⟩ := adjacent_successor hpair
  rw [hdecode] at hd
  cases hd
  let need := next.length - pcTail.length
  have he' : pcTail ++ List.replicate need false = next := he
  have hlen' : next.length = pcTail.length + need := by
    have h := congrArg List.length he'
    simpa using h.symm
  have hn : need ≤ gap + scratch := by omega
  let gap' := gap + scratch - need
  have htotal : need + 2 + gap' = gap + scratch + 2 := by dsimp [gap']; omega
  have hzeros : List.replicate (gap + scratch + 2) false =
      List.replicate need false ++ List.replicate 2 false ++ List.replicate gap' false := by
    rw [List.replicate_append_replicate, List.replicate_append_replicate, htotal]
  refine ⟨gap', ?_, ?_⟩
  · calc
      _ = (pcTail ++ List.replicate need false) ++ false :: false ::
          (List.replicate gap' false ++ suffix) := by simp [hzeros, List.append_assoc]
      _ = _ := by rw [he']
  · dsimp [gap']; omega
/-- A named increment preserves the path-length-plus-gap budget and returns
with the next literal path and both separator zeros already present. -/
theorem physical_increment_preserves_gap_budget (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      (word, next) ∈ adjacentPaths ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨runs, rest, time, endHead, scratch, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd⟩ :=
    Redispatch.physical_root_increment_detail registers r reserve gap word write hpath head left tail c hrel
  obtain ⟨next, hpair⟩ := named_adjacent_exists hpath
  have hlen := normal_length runs rest word scratch bit pcTail hword hsplit hprefix
  have hdecode := decodeOne_of_split runs rest word scratch bit pcTail hword hsplit hprefix
  have hnext := leaf_length_le next (adjacent_next_leaf hpair)
  have hmargin : next.length ≤ gap + word.length := by omega
  obtain ⟨gap', hf, hc⟩ := normal_gap_factor word next pcTail scratch gap bit hpair hdecode hlen hmargin
    (true :: false :: (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))
  rw [hf] at hr
  exact ⟨next, gap', time, endHead, finish, hpair, hc, by omega, ht, hp, hr, hq, hd⟩

/-- A positive named decrement preserves the same control budget and retains
the physical implementation's additional zero reserve block. -/
theorem physical_positive_preserves_gap_budget (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      (word, next) ∈ adjacentPaths ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨runs, rest, time, endHead, scratch, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_positive_detail registers r value hvalue reserve gap word write hpath head left tail c hrel
  obtain ⟨next, hpair⟩ := named_adjacent_exists hpath
  have hlen := normal_length runs rest word scratch bit pcTail hword hsplit hprefix
  have hdecode := decodeOne_of_split runs rest word scratch bit pcTail hword hsplit hprefix
  have hnext := leaf_length_le next (adjacent_next_leaf hpair)
  have hmargin : next.length ≤ gap + word.length := by omega
  obtain ⟨gap', hf, hc⟩ := normal_gap_factor word next pcTail scratch gap bit hpair hdecode hlen hmargin
    (true :: false :: (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))
  rw [hf] at hr
  exact ⟨next, gap', time, endHead, finish, hpair, hc, by omega, ht, hp, hr, hq, hd, hout⟩
/-- On a zero decrement, the two skipped separators contribute exactly one
additional zero to the control-space budget. -/
theorem zero_length (runs rest : List (Fin 6)) (word : List Bool) (scratch1 scratch2 : Nat)
    (bit : Bool) (pcTail : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hsplit : counterWord runs = List.replicate scratch1 true ++ false ::
      (List.replicate scratch2 true ++ false :: counterWord rest))
    (hprefix : counterPush rest [] = true :: bit :: pcTail) :
    word.length = scratch1 + scratch2 + 1 + pcTail.length := by
  obtain ⟨h1, h2⟩ := zero_return runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix
  have hl1 := congrArg List.length h1
  have hl2 := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse,
    List.length_replicate] at hl1 hl2
  omega

/-- Rebuild a zero-decrement successor and two separator zeros while preserving
the exact sum of path length and zero-gap length. -/
theorem zero_gap_factor (word next pcTail : List Bool) (scratch1 scratch2 gap : Nat)
    (hlen : word.length = scratch1 + scratch2 + 1 + pcTail.length)
    (he : pcTail ++ List.replicate (next.length - pcTail.length) false = next)
    (hmargin : next.length ≤ gap + word.length) (suffix : List Bool) :
    ∃ gap', pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++ suffix) =
        next ++ false :: false :: (List.replicate gap' false ++ suffix) ∧
      next.length + gap' = word.length + gap := by
  let need := next.length - pcTail.length
  have he' : pcTail ++ List.replicate need false = next := he
  have hlen' : next.length = pcTail.length + need := by
    have h := congrArg List.length he'
    simpa using h.symm
  have hn : need ≤ gap + scratch2 + scratch1 + 1 := by omega
  let gap' := gap + scratch2 + scratch1 + 1 - need
  have htotal : need + 2 + gap' = gap + (scratch2 + scratch1 + 3) := by dsimp [gap']; omega
  have hzeros : List.replicate (gap + (scratch2 + scratch1 + 3)) false =
      List.replicate need false ++ List.replicate 2 false ++ List.replicate gap' false := by
    rw [List.replicate_append_replicate, List.replicate_append_replicate, htotal]
  refine ⟨gap', ?_, ?_⟩
  · calc
      _ = (pcTail ++ List.replicate need false) ++ false :: false ::
          (List.replicate gap' false ++ suffix) := by simp [hzeros, List.append_assoc]
      _ = _ := by rw [he']
  · dsimp [gap']; omega

/-- A zero named decrement preserves the same path-length-plus-gap budget and
returns with its skipped literal successor and both separator zeros present. -/
theorem physical_zero_preserves_gap_budget_with_successor (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Grammar.LeafPath Grammar.nodes 157 next ∧
      (∃ bit tail, decodeZero word = some (bit, tail) ∧ resolveZeros Grammar.nodes 158 157 tail = some next) ∧
      next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨runs, rest, time, endHead, scratch1, scratch2, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_zero_detail registers r hzero reserve gap word write hpath head left tail c hrel
  have hlen := zero_length runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix
  have hdecode := decodeZero_of_split runs rest word scratch1 scratch2 bit pcTail hword hsplit hprefix
  obtain ⟨b, p, next, hdec, hresolved, hleaf, he, hbound⟩ := decrement_skipped_leaf r word write hpath
  rw [hdecode] at hdec
  cases hdec
  have hnext := leaf_length_le next hleaf
  have hmargin : next.length ≤ gap + word.length := by omega
  obtain ⟨gap', hf, hc⟩ := zero_gap_factor word next pcTail scratch1 scratch2 gap hlen he hmargin
    (true :: false :: (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))
  rw [hf] at hr
  exact ⟨next, gap', time, endHead, finish, hleaf, ⟨bit, pcTail, hdecode, hresolved⟩, hc, by omega, ht, hp, hr, hq, hd, hout⟩

theorem physical_zero_preserves_gap_budget (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hbudget : 25 ≤ gap + word.length) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (next : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Grammar.LeafPath Grammar.nodes 157 next ∧ next.length + gap' = word.length + gap ∧
      25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨next, gap', time, endHead, finish, hleaf, hsuccessor, hc, hb, ht, hp, hr, hq, hd, hout⟩ :=
    physical_zero_preserves_gap_budget_with_successor registers r hzero reserve gap word write hpath hbudget head left tail c hrel
  exact ⟨next, gap', time, endHead, finish, hleaf, hc, hb, ht, hp, hr, hq, hd, hout⟩

end PASoundness.M236.Control
