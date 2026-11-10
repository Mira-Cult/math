import PASoundness.M236Cycle
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Redispatch
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A finite encoded counter containing a zero splits at its first zero,
leaving an encoded counter after a finite run of ones. -/
theorem counter_split (runs : List (Fin 6)) (h : false ∈ counterWord runs) :
    ∃ scratch : Nat, ∃ rest : List (Fin 6),
      counterWord runs = List.replicate scratch true ++ false :: counterWord rest := by
  induction runs with
  | nil => simp [counterWord] at h
  | cons zeros runs ih =>
    by_cases hz : zeros.val = 0
    · have hm : false ∈ counterWord runs := by simpa [counterWord, hz] using h
      obtain ⟨scratch, rest, hr⟩ := ih hm
      exact ⟨scratch + 1, rest, by simp [counterWord, hz, List.replicate_succ, hr]⟩
    · let z : Fin 6 := ⟨zeros.val - 1, by have := zeros.isLt; omega⟩
      have hv : zeros.val = (zeros.val - 1) + 1 := by omega
      refine ⟨0, z :: runs, ?_⟩
      simp only [counterWord, List.replicate_zero, List.nil_append]
      rw [hv, List.replicate_succ]
      rfl

/-- A source-format control path supplies the prepared increment counter
prefix without an extra control-prefix assumption. -/
theorem counter_split_control (runs : List (Fin 6)) (word : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse) :
    ∃ (scratch : Nat) (rest : List (Fin 6)) (bit : Bool) (pcTail : List Bool),
      counterWord runs = List.replicate scratch true ++ false :: counterWord rest ∧
      counterPush rest [] = true :: bit :: pcTail := by
  have hm : false ∈ counterWord runs := by rw [hword]; simp
  obtain ⟨scratch, rest, hsplit⟩ := counter_split runs hm
  have hr := congrArg List.reverse hsplit
  rw [hword, List.reverse_reverse] at hr
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.cons_append, List.nil_append] at hr
  have hpush := counter_push_reverse rest []
  cases hc : (counterWord rest).reverse with
  | nil => simp [hc] at hr
  | cons a t =>
    cases a with
    | false => simp [hc] at hr
    | true =>
      cases t with
      | nil => simp [hc] at hr
      | cons b t =>
        cases b with
        | false => simp [hc] at hr
        | true =>
          cases t with
          | nil =>
            refine ⟨scratch, rest, true, [], hsplit, ?_⟩
            simpa [hc] using hpush
          | cons bit pc =>
            refine ⟨scratch, rest, bit, pc ++ [true], hsplit, ?_⟩
            simpa [hc] using hpush

private theorem ones_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Encoded nine-register tape after the gap anchor. -/
def selectedPayload (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (tail : List Bool) : List Bool :=
  bank (UnaryIncrementNine.before registers r) ++
    (List.replicate (registers r + 1) true ++ false ::
      (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail))

/-- From an explicit clean grammar-root tape, the literal machines prepare,
redispatch, increment the selected register, and return to root silently.
No blank-start or source reachability is assumed. -/
theorem physical_root_increment_detail (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (runs rest : List (Fin 6)) (time : Nat) (endHead : Int) (scratch : Nat) (pcBit : Bool)
      (pcTail : List Bool) (finish : Config 237),
      counterWord runs = ([true, true, false] ++ word).reverse ∧
      counterWord runs = List.replicate scratch true ++ false :: counterWord rest ∧
      counterPush rest [] = true :: pcBit :: pcTail ∧
      0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨runs, pre, bit, middle, hword, hw, hp, hr, hq, ht⟩ :=
    physical_root_prepare_redispatch r gap word write hpath head left
      (false :: selectedPayload registers r reserve tail) c hrel
  obtain ⟨scratch, rest, pcBit, pcTail, hsplit, hprefix⟩ := counter_split_control runs word hword
  obtain ⟨pre', bit', hw', hbit⟩ := named_increment_ending r write hpath rfl
  have hbit' : write = bit := by
    have h := congrArg List.reverse (hw'.symm.trans hw)
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons.injEq] at h
    exact hbit.trans h.1
  have hleft : write :: (pre.reverse ++ false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate scratch true ++ false :: (counterWord rest ++ List.replicate 6 false ++ false :: left) := by
    have he : write :: (pre.reverse ++ false :: true :: true :: (List.replicate 7 false ++ left)) =
        counterWord runs ++ List.replicate 7 false ++ left := by
      rw [hword, hw, hbit']
      simp [List.reverse_append, List.reverse_cons, List.append_assoc]
    rw [he, hsplit]
    simp [List.replicate_succ, List.append_assoc]
  let entryHead := Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int))
  have hentry : Related ⟨Selector.entryState r, entryHead,
      ⟨List.replicate scratch true ++ false :: (counterWord rest ++ List.replicate 6 false ++ false :: left),
        true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++
          (List.replicate (registers r + 1) true ++ false ::
            (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)))⟩⟩ middle := by
    have hright : List.replicate gap true ++ true :: false :: selectedPayload registers r reserve tail =
        bank (gap :: UnaryIncrementNine.before registers r) ++
          (List.replicate (registers r + 1) true ++ false ::
            (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)) := by
      simp only [bank, List.cons_append, selectedPayload, ones_shift, List.append_assoc]
    simpa only [entryHead, Grammar.finalTape, Move.apply, moveRight, List.drop_succ_cons,
      List.drop_zero, hleft, hright] using hr
  obtain ⟨first, values, finish, he, hs, hf, hq2, ht2, hd⟩ :=
    SelectorRoot.physical_named_increment_root registers r reserve gap scratch rest pcBit pcTail
      entryHead left tail middle hprefix hentry
  let t1 := word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
  let t2 := shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
    (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
      (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9) +
    (counterTime rest + 6) + 10
  let finalHead := entryHead + 2 + (shiftTime (gap :: UnaryIncrementNine.before registers r) : Int) +
    ((registers r + 2 : Nat) : Int) + (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
    ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1 -
    (counterTime rest : Int) - 6 + 10
  refine ⟨runs, rest, t1 + t2, finalHead, scratch, pcBit, pcTail, finish,
    hword, hsplit, hprefix, ?_, ?_, ?_, ?_, hd⟩
  · dsimp [t1, t2]; omega
  · simpa using hp.trans (machineWordSystem raw rawLabels) hs
  · exact hf
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq2


theorem physical_root_increment (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (pcTail : List Bool) (finish : Config 237),
      0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨runs, rest, time, endHead, scratch, pcBit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd⟩ :=
    physical_root_increment_detail registers r reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch, pcTail, finish, ht, hp, hr, hq, hd⟩

/-- A finite regression witness for preparation followed by an increment of
register zero from a zero bank. -/
example : rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false, false, false, false, true, false] ++
        bank (List.replicate 9 0) ++ [false]⟩⟩ 132
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, true, true, true, false, false, false, false, true, false] ++
        bank (1 :: List.replicate 8 0)⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false, false, false, false, true, false] ++
        bank (List.replicate 9 0) ++ [false]⟩⟩ 131
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, true, true, true, false, false, false, false, true, false] ++
        bank (1 :: List.replicate 8 0)⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, false, true, true, false, false, false, false, false, true, false] ++
          bank (List.replicate 9 0) ++ [false]⟩⟩ 131 ≠
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, false, true, true, true, false, false, false, false, true, false] ++
          bank (1 :: List.replicate 8 0)⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.Redispatch
