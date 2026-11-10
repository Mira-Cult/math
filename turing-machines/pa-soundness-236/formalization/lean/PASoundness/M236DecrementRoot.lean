import PASoundness.M236DecrementPreparation
import PASoundness.M236DecrementShift
import PASoundness.M236ZeroFullCleanup
/-! Concrete grammar-root decrement segments for both branches. The root
tape is explicit and is not derived from blank-start source execution. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementRoot
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

private theorem ones_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem counter_split_twice (runs : List (Fin 6)) (word : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hfalse : false ∈ word) :
    ∃ (scratch1 scratch2 : Nat) (rest : List (Fin 6)) (bit : Bool) (pcTail : List Bool),
      counterWord runs = List.replicate scratch1 true ++ false ::
        (List.replicate scratch2 true ++ false :: counterWord rest) ∧
      counterPush rest [] = true :: bit :: pcTail := by
  have hc : 1 < (counterWord runs).count false := by
    rw [hword]
    have hw : 0 < word.count false := List.count_pos_iff.mpr hfalse
    simp [List.count_append]
    omega
  obtain ⟨scratch1, rest1, hs1⟩ := Redispatch.counter_split runs (by
    apply List.count_pos_iff.mp
    omega)
  have hsCount := congrArg (List.count false) hs1
  have hc1 : 0 < (counterWord rest1).count false := by
    simp [List.count_replicate] at hsCount
    omega
  obtain ⟨scratch2, rest2, hs2⟩ := Redispatch.counter_split rest1 (List.count_pos_iff.mp hc1)
  have hsplit : counterWord runs = List.replicate scratch1 true ++ false ::
      (List.replicate scratch2 true ++ false :: counterWord rest2) := by rw [hs1, hs2]
  have hr := congrArg List.reverse hsplit
  rw [hword, List.reverse_reverse] at hr
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.cons_append, List.nil_append, List.append_assoc] at hr
  have hpush := Redispatch.counter_push_reverse rest2 []
  cases hz : (counterWord rest2).reverse with
  | nil => simp [hz] at hr
  | cons a t =>
    cases a with
    | false => simp [hz] at hr
    | true =>
      cases t with
      | nil => simp [hz] at hr
      | cons b t =>
        cases b with
        | false => simp [hz] at hr
        | true =>
          cases t with
          | nil =>
            refine ⟨scratch1, scratch2, rest2, true, [], hsplit, ?_⟩
            simpa [hz] using hpush
          | cons bit pc =>
            refine ⟨scratch1, scratch2, rest2, bit, pc ++ [true], hsplit, ?_⟩
            simpa [hz] using hpush

/-- A checked named decrement path on a clean grammar-root tape prepares and
executes a positive decrement. The extra terminal zero block is explicit. -/
theorem physical_root_positive_detail (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat)
    (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (runs rest : List (Fin 6)) (time : Nat) (endHead : Int) (scratch : Nat) (pcBit : Bool)
      (pcTail : List Bool) (finish : Config 237),
      counterWord runs = ([true, true, false] ++ word).reverse ∧
      counterWord runs = List.replicate scratch true ++ false :: counterWord rest ∧
      counterPush rest [] = true :: pcBit :: pcTail ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨runs, pre, bit, mid, hword, hw, hp, hr, hq, ht⟩ :=
    Preparation.physical_decrement_root_prepare_redispatch r gap word write hpath head left
      (false :: Redispatch.selectedPayload registers r reserve tail) c hrel
  obtain ⟨scratch, rest, pcBit, pcTail, hsplit, hprefix⟩ := Redispatch.counter_split_control runs word hword
  obtain ⟨pre', bit', hw', hbit⟩ := Preparation.named_decrement_ending r write hpath rfl
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
  have hright : List.replicate gap true ++ true :: false :: Redispatch.selectedPayload registers r reserve tail =
      bank (gap :: UnaryIncrementNine.before registers r) ++ true :: true ::
        (List.replicate value true ++ false :: (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)) := by
    simp [Redispatch.selectedPayload, bank, hvalue, List.replicate_succ, List.append_assoc, ones_shift]
  let entryHead := Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int))
  have hentry : Related ⟨DecrementSelector.entryState r, entryHead,
      ⟨List.replicate scratch true ++ false :: (counterWord rest ++ List.replicate 6 false ++ false :: left),
        true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++ true :: true ::
          (List.replicate value true ++ false :: (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)))⟩⟩ mid := by
    simpa only [entryHead, Grammar.finalTape, Move.apply, moveRight, List.drop_succ_cons,
      List.drop_zero, hleft, hright] using hr
  obtain ⟨time2, endHead, finish, ht2, hp2, hr2, hq2, hd, hout⟩ :=
    DecrementShift.physical_named_positive_root registers r value hvalue reserve gap scratch rest pcBit pcTail
      hprefix entryHead left tail mid hentry
  let time1 := word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
  refine ⟨runs, rest, time1 + time2, endHead, scratch, pcBit, pcTail, finish,
    hword, hsplit, hprefix, ?_, ?_, hr2, ?_, hd, hout⟩
  · dsimp [time1]; omega
  · simpa [time1] using hp.trans (machineWordSystem raw rawLabels) hp2
  · simpa [time1] using hq.trans (machineWordSystem machine machineLabels) hq2


theorem physical_root_positive (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat)
    (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (pcTail : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨runs, rest, time, endHead, scratch, pcBit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    physical_root_positive_detail registers r value hvalue reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch, pcTail, finish, ht, hp, hr, hq, hd, hout⟩

/-- Every named decrement path contains a zero: the unique all-one leaf
path reaches an increment entry. -/
theorem decrement_path_has_false (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)) :
    false ∈ word := by
  have hcheck : Grammar.completePaths.all
      (fun w => decide (false ∈ w ∨ w = [true, true, true, true, true, true, true])) = true := by decide
  have hm := Grammar.every_leaf_path word (Redispatch.named_leaf_path hpath)
  have hd : false ∈ word ∨ word = [true, true, true, true, true, true, true] :=
    of_decide_eq_true ((List.all_eq_true.mp hcheck) word hm)
  rcases hd with hf | hw
  · exact hf
  · have hknown : Preparation.NamedPath Grammar.nodes 157 [true, true, true, true, true, true, true]
        (.leaf "3.k.stage.inc" 54 true .right none) := by
      apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
      apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
      apply Preparation.NamedPath.step 155 154 true _ _ (by decide)
      apply Preparation.NamedPath.step 154 153 true _ _ (by decide)
      apply Preparation.NamedPath.step 153 152 true _ _ (by decide)
      apply Preparation.NamedPath.step 152 151 true _ _ (by decide)
      exact Preparation.NamedPath.leaf 151 true _ (by decide) ⟨_, _, _, _, _, rfl⟩
    rw [hw] at hpath
    obtain ⟨pre1, bit1, hword1, hb1⟩ := Preparation.follow_named hknown rfl 0 [] []
    obtain ⟨pre2, bit2, hword2, hb2⟩ := Preparation.follow_named hpath rfl 0 [] []
    have hstate := congrArg (fun z : Configuration 237 => z.state) (hb1.endpoint.symm.trans hb2.endpoint)
    have hne : ∀ r : Fin 9, DecrementSelector.entryState r ≠ 54 := by decide
    exact False.elim (hne r hstate.symm)

/-- A named decrement path containing a zero, from an explicit clean root
tape with a zero-valued selected register, returns to the root unchanged. -/
theorem physical_root_zero_detail (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (runs rest : List (Fin 6)) (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat)
      (pcBit : Bool) (pcTail : List Bool) (finish : Config 237),
      counterWord runs = ([true, true, false] ++ word).reverse ∧
      counterWord runs = List.replicate scratch1 true ++ false ::
        (List.replicate scratch2 true ++ false :: counterWord rest) ∧
      counterPush rest [] = true :: pcBit :: pcTail ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨runs, pre, bit, mid, hword, hw, hp, hr, hq, ht⟩ :=
    Preparation.physical_decrement_root_prepare_redispatch r gap word write hpath head left
      (false :: Redispatch.selectedPayload registers r reserve tail) c hrel
  have hfalse := DecrementRoot.decrement_path_has_false r word write hpath
  obtain ⟨scratch1, scratch2, rest, pcBit, pcTail, hsplit, hprefix⟩ := DecrementRoot.counter_split_twice runs word hword hfalse
  obtain ⟨pre', bit', hw', hbit⟩ := Preparation.named_decrement_ending r write hpath rfl
  have hbit' : write = bit := by
    have h := congrArg List.reverse (hw'.symm.trans hw)
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons.injEq] at h
    exact hbit.trans h.1
  have hleft : write :: (pre.reverse ++ false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate scratch1 true ++ false :: (List.replicate scratch2 true ++ false ::
        (counterWord rest ++ List.replicate 6 false ++ false :: left)) := by
    have he : write :: (pre.reverse ++ false :: true :: true :: (List.replicate 7 false ++ left)) =
        counterWord runs ++ List.replicate 7 false ++ left := by
      rw [hword, hw, hbit']
      simp [List.reverse_append, List.reverse_cons, List.append_assoc]
    rw [he, hsplit]
    simp [List.replicate_succ, List.append_assoc]
  have hright : List.replicate gap true ++ true :: false :: Redispatch.selectedPayload registers r reserve tail =
      bank (gap :: UnaryIncrementNine.before registers r) ++ true :: false ::
        (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail) := by
    simp [Redispatch.selectedPayload, bank, hzero, List.replicate_succ, List.append_assoc, ones_shift]
  let entryHead := Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int))
  have hentry : Related ⟨DecrementSelector.entryState r, entryHead,
      ⟨List.replicate scratch1 true ++ false :: (List.replicate scratch2 true ++ false ::
        (counterWord rest ++ List.replicate 6 false ++ false :: left)),
        true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++ true :: false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail))⟩⟩ mid := by
    simpa only [entryHead, Grammar.finalTape, Move.apply, moveRight, List.drop_succ_cons,
      List.drop_zero, hleft, hright] using hr
  obtain ⟨time2, endHead, finish, ht2, hp2, hr2, hq2, hd, hout⟩ :=
    DecrementReturn.physical_named_zero_root registers r hzero reserve gap scratch1 scratch2 rest pcBit pcTail
      hprefix entryHead left (false :: tail) mid hentry
  let time1 := word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
  refine ⟨runs, rest, time1 + time2, endHead, scratch1, scratch2, pcBit, pcTail, finish,
    hword, hsplit, hprefix, ?_, ?_, hr2, ?_, hd, hout⟩
  · dsimp [time1]; omega
  · simpa [time1] using hp.trans (machineWordSystem raw rawLabels) hp2
  · simpa [time1] using hq.trans (machineWordSystem machine machineLabels) hq2



theorem physical_root_zero (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat) (pcTail : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨runs, rest, time, endHead, scratch1, scratch2, pcBit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    physical_root_zero_detail registers r hzero reserve gap word write hpath head left tail c hrel
  exact ⟨time, endHead, scratch1, scratch2, pcTail, finish, ht, hp, hr, hq, hd, hout⟩

/-- Every register has a checked named decrement path in the literal grammar. -/
theorem decrement_path_exists (r : Fin 9) :
    ∃ (word : List Bool) (write : Bool), Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by omega
  rcases hr with h | h | h | h | h | h | h | h | h <;> subst r
  · refine ⟨[false, false, true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
    apply Preparation.NamedPath.step 30 4 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 4 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, false, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 2 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 2 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[true, true, true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
    apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
    apply Preparation.NamedPath.step 155 154 true _ _ (by decide)
    apply Preparation.NamedPath.step 154 145 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 145 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[true, true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
    apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
    apply Preparation.NamedPath.step 155 144 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 144 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, true, false, false, false, true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
    apply Preparation.NamedPath.step 36 35 false _ _ (by decide)
    apply Preparation.NamedPath.step 35 34 true _ _ (by decide)
    apply Preparation.NamedPath.step 34 33 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 33 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[true, true, true, true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
    apply Preparation.NamedPath.step 156 155 true _ _ (by decide)
    apply Preparation.NamedPath.step 155 154 true _ _ (by decide)
    apply Preparation.NamedPath.step 154 153 true _ _ (by decide)
    apply Preparation.NamedPath.step 153 146 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 146 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 156 true _ _ (by decide)
    apply Preparation.NamedPath.step 156 84 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 84 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, true, true, false, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 139 true _ _ (by decide)
    apply Preparation.NamedPath.step 139 132 false _ _ (by decide)
    apply Preparation.NamedPath.step 132 83 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 83 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, true, false, false, true, false, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
    apply Preparation.NamedPath.step 36 25 true _ _ (by decide)
    apply Preparation.NamedPath.step 25 14 false _ _ (by decide)
    apply Preparation.NamedPath.step 14 13 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 13 false _ (by decide) ⟨_, _, _, _, _, rfl⟩


/-- Concrete prepared tapes witnessing the zero branch for all nine registers. -/
theorem concrete_zero (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (head : Int) (left tail : List Bool) :
    ∃ (word : List Bool) (write : Bool) (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat)
      (pcTail : List Bool) (finish : Config 237),
      Preparation.NamedPath Grammar.nodes 157 word
        (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) ∧
      0 < time ∧
      (machineWordSystem raw rawLabels).Block (Redispatch.rootConfig registers r reserve gap word head left tail) time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block
        (mapConfig (Redispatch.rootConfig registers r reserve gap word head left tail)) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ false :: tail) =
        some (UnaryNine.values registers ++ reserve, false :: tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨word, write, hpath⟩ := decrement_path_exists r
  let c := Redispatch.rootConfig registers r reserve gap word head left tail
  have hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c := Redispatch.realize_related _
  obtain ⟨time, endHead, scratch1, scratch2, pcTail, finish, ht, hp, hr, hq, hd, hout⟩ :=
    physical_root_zero registers r hzero reserve gap word write hpath head left tail c hrel
  exact ⟨word, write, time, endHead, scratch1, scratch2, pcTail, finish, hpath, ht, hp, hr, hq, hd, hout⟩

/-- Concrete prepared tapes witnessing every positive decrement branch. -/
theorem concrete_positive (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat)
    (gap : Nat) (head : Int) (left tail : List Bool) :
    ∃ (word : List Bool) (write : Bool) (time : Nat) (endHead : Int) (scratch : Nat)
      (pcTail : List Bool) (finish : Config 237),
      Preparation.NamedPath Grammar.nodes 157 word
        (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) ∧
      0 < time ∧
      (machineWordSystem raw rawLabels).Block (Redispatch.rootConfig registers r reserve gap word head left tail) time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block
        (mapConfig (Redispatch.rootConfig registers r reserve gap word head left tail)) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨word, write, hpath⟩ := decrement_path_exists r
  let c := Redispatch.rootConfig registers r reserve gap word head left tail
  have hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c := Redispatch.realize_related _
  obtain ⟨time, endHead, scratch, pcTail, finish, ht, hp, hr, hq, hd, hout⟩ :=
    physical_root_positive registers r value hvalue reserve gap word write hpath head left tail c hrel
  exact ⟨word, write, time, endHead, scratch, pcTail, finish, hpath, ht, hp, hr, hq, hd, hout⟩

example : rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, false, false, false, false, false, false, true, false, true, false] ++
        bank (List.replicate 8 0) ++ [false]⟩⟩ 96
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, true, false, false, false, false, false, true, false] ++
        bank (List.replicate 9 0) ++ [false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, false, false, false, false, false, false, true, false, true, false] ++
        bank (List.replicate 8 0) ++ [false]⟩⟩ 95
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, true, false, false, false, false, false, true, false] ++
        bank (List.replicate 9 0) ++ [false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, true, false, false, false, false, false, false, true, false, true, false] ++
          bank (List.replicate 8 0) ++ [false]⟩⟩ 95 ≠
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, true, true, false, false, false, false, false, true, false] ++
          bank (List.replicate 9 0) ++ [false]⟩⟩ := by decide
  exact bad h.endpoint

example : rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, false, false, false, false, false, false, true, false, true, true, false] ++
        bank (List.replicate 8 0) ++ [false]⟩⟩ 130
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, false, true, false, false, false, false, true, false] ++
        bank (List.replicate 10 0)⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, false, false, false, false, false, false, true, false, true, true, false] ++
        bank (List.replicate 8 0) ++ [false]⟩⟩ 129
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, true, false, true, false, false, false, false, true, false] ++
        bank (List.replicate 10 0)⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, true, false, false, false, false, false, false, true, false, true, true, false] ++
          bank (List.replicate 8 0) ++ [false]⟩⟩ 129 ≠
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, true, false, true, false, false, false, false, true, false] ++
          bank (List.replicate 10 0)⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.DecrementRoot
