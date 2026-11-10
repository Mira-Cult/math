import PASoundness.M236Preparation

/-! Physical return from the filled-gap preparation to the program counter.
All full-tape preconditions are explicit; no source reachability is assumed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Redispatch
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 64 crosses an arbitrary finite run of ones, preserving the tape. -/
theorem counter_ones (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨64, head, moveLeft ⟨List.replicate count true ++ left, true :: right⟩ true⟩ count
      ⟨64, head - (count : Int), moveLeft ⟨left, true :: (List.replicate count true ++ right)⟩ true⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨64, head, moveLeft ⟨left, true :: right⟩ true⟩
  | succ count ih =>
    have hs := counter_segment ⟨0, by decide⟩ head (List.replicate count true ++ left) right
    have hb := hs.trans rawSystem (ih (head - 1) (true :: right))
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, List.replicate_zero, List.nil_append, replicate_shift] using hb

/-- State 72 returns left across the filled gap and its separator, then the
return counter crosses the marker. The gap, marker, anchor and every other
cell are retained. -/
theorem prepared_to_counter (gap : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨72, head + ((gap + 1 : Nat) : Int),
        moveLeft ⟨List.replicate gap true ++ false :: true :: left, true :: tail⟩ true⟩
      (gap + 2)
      ⟨64, head - 1,
        moveLeft ⟨left, true :: false :: (List.replicate gap true ++ true :: tail)⟩ true⟩ [] := by
  have r72t : raw.table.row 72 true = ⟨true, .left, 64, false⟩ := by decide
  have e72t : rawLabels.at 72 true = none := by decide
  cases gap with
  | zero =>
    have r72f : raw.table.row 72 false = ⟨false, .left, 72, false⟩ := by decide
    have e72f : rawLabels.at 72 false = none := by decide
    have h0 : rawSystem.step ⟨72, head + 1, ⟨true :: left, false :: true :: tail⟩⟩ =
        (⟨72, head, ⟨left, true :: false :: true :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r72f, e72f,
        Move.apply, moveLeft]
    have h1 : rawSystem.step ⟨72, head, ⟨left, true :: false :: true :: tail⟩⟩ =
        (⟨64, head - 1, moveLeft ⟨left, true :: false :: true :: tail⟩ true⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r72t, e72t, Move.apply]
    simpa [moveLeft] using (WordEventSystem.Block.single rawSystem h0).trans rawSystem
      (WordEventSystem.Block.single rawSystem h1)
  | succ gap =>
    have h0 : rawSystem.step
        ⟨72, head + ((gap + 2 : Nat) : Int),
          ⟨List.replicate gap true ++ false :: true :: left, true :: true :: tail⟩⟩ =
        (⟨64, head + ((gap + 1 : Nat) : Int),
          moveLeft ⟨List.replicate gap true ++ false :: true :: left, true :: true :: tail⟩ true⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r72t, e72t, Move.apply]
      omega
    have hscan := counter_ones gap (head + ((gap + 1 : Nat) : Int)) (false :: true :: left) (true :: tail)
    have hmarker := counter_segment ⟨1, by decide⟩
      (head + ((gap + 1 : Nat) : Int) - (gap : Int)) left
      (List.replicate gap true ++ true :: tail)
    have hb := ((WordEventSystem.Block.single rawSystem h0).trans rawSystem hscan).trans rawSystem hmarker
    have hh : head + ((gap + 1 : Nat) : Int) - (gap : Int) - ((1 + 1 : Nat) : Int) = head - 1 := by omega
    have ht : 1 + gap + (1 + 1) = (gap + 1) + 2 := by omega
    simpa only [List.replicate_succ, List.cons_append, moveLeft, List.drop_succ_cons,
      List.drop_zero, List.headD_cons, List.nil_append, List.replicate_zero, hh, ht, replicate_shift,
      Nat.add_assoc] using hb

/-- Every named path is a leaf path in the checked grammar. -/
theorem named_leaf_path {nodes : Vector Grammar.Node 158} {i : Fin 158}
    {word : List Bool} {e : Grammar.Edge} (h : Preparation.NamedPath nodes i word e) :
    Grammar.LeafPath nodes i word := by
  induction h with
  | leaf i b e he hl =>
    obtain ⟨name, target, write, move, event, rfl⟩ := hl
    exact Grammar.LeafPath.leaf i b name target write move event he
  | step i j b tail e he rest ih => exact Grammar.LeafPath.step i j b tail he ih

/-- The grammar's checked codec provides a suitable counter word for every
named path, so the encoding side condition is not an unverified assumption. -/
theorem named_path_codec {word : List Bool} {e : Grammar.Edge}
    (h : Preparation.NamedPath Grammar.nodes 157 word e) :
    ∃ runs : List (Fin 6), counterWord runs = ([true, true, false] ++ word).reverse := by
  obtain ⟨runs, bit, tail, hw, hp⟩ := Grammar.leaf_path_codec word (named_leaf_path h)
  exact ⟨runs, hw⟩

/-- The counter reconstructs the scanned control word in physical order. -/
theorem counter_push_reverse (runs : List (Fin 6)) (right : List Bool) :
    true :: counterPush runs right = (counterWord runs).reverse ++ true :: right := by
  induction runs generalizing right with
  | nil => rfl
  | cons zeros rest ih =>
    simp only [counterWord, counterPush, ih, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append]

/-- A source-format `110` path is restored exactly, followed by the marker
and filled gap. The path-to-counter encoding is a proved equality. -/
theorem prepared_root (r : Fin 9) (gap : Nat) (runs : List (Fin 6)) (word : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨Selector.entryState r, head,
        ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
          false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
      ((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10)
      ⟨79, head + 3 - (counterTime runs : Int),
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          word ++ true :: false :: (List.replicate gap true ++ true :: tail)⟩⟩ [] := by
  let pc := counterWord runs ++ List.replicate 6 false ++ false :: left
  have hprep := Preparation.prepare_gap r gap head pc tail
  have hback := prepared_to_counter gap head pc tail
  have hc := counter_walk_stop runs (head - 1) (false :: left)
    (false :: (List.replicate gap true ++ true :: tail))
  have hwhole := (hprep.trans rawSystem hback).trans rawSystem hc
  have hpush : counterPush runs (false :: (List.replicate gap true ++ true :: tail)) =
      true :: false :: (word ++ true :: false :: (List.replicate gap true ++ true :: tail)) := by
    have h := counter_push_reverse runs (false :: (List.replicate gap true ++ true :: tail))
    rw [hword, List.reverse_reverse] at h
    simpa only [List.cons_append, List.cons.injEq, true_and, List.nil_append] using h
  rw [hpush] at hwhole
  let h65 := head - 1 - (counterTime runs : Int) - 6
  have hstart : rawSystem.Block
      ⟨Selector.entryState r, head,
        ⟨pc, false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
      ((gap + 3) + (gap + 2) + (counterTime runs + 6))
      ⟨65, h65, ⟨left, List.replicate 7 false ++ true :: true :: false ::
        (word ++ true :: false :: (List.replicate gap true ++ true :: tail))⟩⟩ [] := by
    simpa [pc, h65, moveLeft, List.replicate_succ] using hwhole
  have hroot := root_reentry 7 false h65 left
    (word ++ true :: false :: (List.replicate gap true ++ true :: tail))
  have hh : h65 + ((7 : Nat) : Int) + 3 = head + 3 - (counterTime runs : Int) := by
    dsimp [h65]; omega
  have hb := hstart.trans rawSystem hroot
  rw [hh] at hb
  simpa [pc] using hb

/-- The return and redispatch theorem is lifted to both the 237-row source
machine and its exact 236-state quotient, retaining the full tape relation. -/
theorem physical_prepared_root (r : Fin 9) (gap : Nat) (runs : List (Fin 6))
    (word : List Bool) (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨Selector.entryState r, head,
      ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
        false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c
        ((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) finish [] ∧
      Related ⟨79, head + 3 - (counterTime runs : Int),
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          word ++ true :: false :: (List.replicate gap true ++ true :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) (mapConfig finish) [] ∧
      0 < (gap + 3) + (gap + 2) + (counterTime runs + 6) + 10 := by
  have hb := prepared_root r gap runs word hword head left tail
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨finish, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

/-- Once the filled-gap return reaches the grammar root, the same checked
named path is traversed again. The theorem includes the actual leaf action,
the entire tape, and an exact positive physical duration. -/
theorem prepared_redispatch (r : Fin 9) (gap : Nat) (runs : List (Fin 6))
    (word : List Bool) (write : Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) :
    ∃ pre bit, word = pre ++ [bit] ∧
      rawSystem.Block
        ⟨Selector.entryState r, head,
          ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
            false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
        (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
        ⟨Selector.entryState r,
          Move.right.apply (head + 3 - (counterTime runs : Int) + (pre.length : Int)),
          Grammar.finalTape pre bit write .right
            (false :: true :: true :: (List.replicate 7 false ++ left))
            (true :: false :: (List.replicate gap true ++ true :: tail))⟩ [] := by
  obtain ⟨pre, bit, hw, hb⟩ := Preparation.follow_named hpath rfl
    (head + 3 - (counterTime runs : Int))
    (false :: true :: true :: (List.replicate 7 false ++ left))
    (true :: false :: (List.replicate gap true ++ true :: tail))
  have hroot : Grammar.nodes[(157 : Fin 158)].state = 79 := by decide
  rw [hroot] at hb
  exact ⟨pre, bit, hw, by simpa using (prepared_root r gap runs word hword head left tail).trans rawSystem hb⟩

/-- The same redispatch segment is preserved on the actual quotient table. -/
theorem physical_prepared_redispatch (r : Fin 9) (gap : Nat) (runs : List (Fin 6))
    (word : List Bool) (write : Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨Selector.entryState r, head,
      ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
        false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ pre bit finish, word = pre ++ [bit] ∧
      (machineWordSystem raw rawLabels).Block c
        (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length) finish [] ∧
      Related ⟨Selector.entryState r,
        Move.right.apply (head + 3 - (counterTime runs : Int) + (pre.length : Int)),
        Grammar.finalTape pre bit write .right
          (false :: true :: true :: (List.replicate 7 false ++ left))
          (true :: false :: (List.replicate gap true ++ true :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
        (mapConfig finish) [] ∧
      0 < ((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length := by
  obtain ⟨pre, bit, hw, hb⟩ := prepared_redispatch r gap runs word write hword hpath head left tail
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨pre, bit, finish, hw, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

/-- Every specified named path has a checked counter encoding; starting from
that concrete reversed word gives quotient redispatch without a codec premise. -/
theorem physical_named_redispatch (r : Fin 9) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨Selector.entryState r, head,
      ⟨([true, true, false] ++ word).reverse ++ List.replicate 6 false ++ false :: left,
        false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ (runs : List (Fin 6)) (pre : List Bool) (bit : Bool) (finish : Config 237),
      counterWord runs = ([true, true, false] ++ word).reverse ∧ word = pre ++ [bit] ∧
      (machineWordSystem raw rawLabels).Block c
        (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length) finish [] ∧
      Related ⟨Selector.entryState r,
        Move.right.apply (head + 3 - (counterTime runs : Int) + (pre.length : Int)),
        Grammar.finalTape pre bit write .right
          (false :: true :: true :: (List.replicate 7 false ++ left))
          (true :: false :: (List.replicate gap true ++ true :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
        (mapConfig finish) [] ∧
      0 < ((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length := by
  obtain ⟨runs, hw⟩ := named_path_codec hpath
  rw [← hw] at hrel
  obtain ⟨pre, bit, finish, hp, hb, hr, hq, ht⟩ :=
    physical_prepared_redispatch r gap runs word write hw hpath head left tail c hrel
  exact ⟨runs, pre, bit, finish, hw, hp, hb, hr, hq, ht⟩

example : rawSystem.Block
    ⟨58, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, false, true]⟩⟩ 28
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [true, false, true, true, true]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨58, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, false, true]⟩⟩ 27
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [true, false, true, true, true]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨58, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, false, false, true]⟩⟩ 27 ≠
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [true, false, true, true, true]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.Redispatch
