import PASoundness.M236SelectorRoot
import PASoundness.M236GrammarWalk

/-! Literal zero-branch preparation for named increment entries. The clean
finite gap, its terminating anchor, and complete surrounding tape are explicit
hypotheses; no source or blank-start reachability is assumed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Preparation
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem replicate_shift (b : Bool) (n : Nat) (tail : List Bool) :
    List.replicate n b ++ (b :: tail) = b :: (List.replicate n b ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 5 fills any finite zero run while moving right. -/
theorem fill_zeros (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨5, head, ⟨left, List.replicate count false ++ true :: tail⟩⟩ count
      ⟨5, head + (count : Int), ⟨List.replicate count true ++ left, true :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨5, head, ⟨left, true :: tail⟩⟩
  | succ count ih =>
    have row : raw.table.row 5 false = ⟨true, .right, 5, false⟩ := by decide
    have ev : rawLabels.at 5 false = none := by decide
    have hs : rawSystem.step
        ⟨5, head, ⟨left, List.replicate (count + 1) false ++ true :: tail⟩⟩ =
        (⟨5, head + 1, ⟨true :: left, List.replicate count false ++ true :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
        Move.apply, moveRight, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem (ih (head + 1) (true :: left))
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- Any named zero-branch writes its marker, crosses the separator, fills the
finite gap and enters state 72 just left of the unchanged anchor. -/
theorem prepare_gap (r : Fin 9) (gap : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨Selector.entryState r, head,
        ⟨left, false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
      (gap + 3)
      ⟨72, head + ((gap + 1 : Nat) : Int),
        moveLeft ⟨List.replicate gap true ++ false :: true :: left, true :: tail⟩ true⟩ [] := by
  have e := Selector.unprepared_rows r
  have h0 : rawSystem.step ⟨Selector.entryState r, head,
      ⟨left, false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ =
      (⟨4, head + 1, ⟨true :: left, false :: (List.replicate gap false ++ true :: tail)⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, e.1, e.2,
      Move.apply, moveRight]
  have r4 : raw.table.row 4 false = ⟨false, .right, 5, false⟩ := by decide
  have e4 : rawLabels.at 4 false = none := by decide
  have h1 : rawSystem.step ⟨4, head + 1,
      ⟨true :: left, false :: (List.replicate gap false ++ true :: tail)⟩⟩ =
      (⟨5, head + 2, ⟨false :: true :: left, List.replicate gap false ++ true :: tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r4, e4,
      Move.apply, moveRight]
    omega
  have hfill := fill_zeros gap (head + 2) (false :: true :: left) tail
  have r5 : raw.table.row 5 true = ⟨true, .left, 72, false⟩ := by decide
  have e5 : rawLabels.at 5 true = none := by decide
  have h2 : rawSystem.step ⟨5, head + 2 + (gap : Int),
      ⟨List.replicate gap true ++ false :: true :: left, true :: tail⟩⟩ =
      (⟨72, head + ((gap + 1 : Nat) : Int),
        moveLeft ⟨List.replicate gap true ++ false :: true :: left, true :: tail⟩ true⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r5, e5, Move.apply]
    omega
  have hb := (((WordEventSystem.Block.single rawSystem h0).trans rawSystem
    (WordEventSystem.Block.single rawSystem h1)).trans rawSystem hfill).trans rawSystem
    (WordEventSystem.Block.single rawSystem h2)
  have ht : 1 + 1 + gap + 1 = gap + 3 := by omega
  simpa only [List.nil_append, ht] using hb

/-- Full raw and quotient executions of the finite preparation block. -/
theorem physical_prepare_gap (r : Fin 9) (gap : Nat) (head : Int)
    (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨Selector.entryState r, head,
      ⟨left, false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (gap + 3) finish [] ∧
      Related ⟨72, head + ((gap + 1 : Nat) : Int),
        moveLeft ⟨List.replicate gap true ++ false :: true :: left, true :: tail⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (gap + 3) (mapConfig finish) [] ∧
      0 < gap + 3 := by
  have hb := prepare_gap r gap head left tail
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨finish, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

/-- Record the exact terminal edge of a finite graph path. -/
inductive NamedPath (nodes : Vector Grammar.Node 158) : Fin 158 → List Bool →
    Grammar.Edge → Prop where
  | leaf (i : Fin 158) (b : Bool) (e : Grammar.Edge)
      (h : Grammar.edge nodes i b = e) (hleaf : ∃ name target write move event,
        e = .leaf name target write move event) : NamedPath nodes i [b] e
  | step (i j : Fin 158) (b : Bool) (tail : List Bool) (e : Grammar.Edge)
      (h : Grammar.edge nodes i b = .node j) (rest : NamedPath nodes j tail e) :
      NamedPath nodes i (b :: tail) e

/-- Literal execution of a path whose final edge is specified, preserving
its full final tape and optional event. -/
theorem follow_named {i : Fin 158} {word : List Bool}
    {name : String} {target : Fin 237} {write : Bool} {move : Move} {event : Option Bool}
    {e : Grammar.Edge} (h : NamedPath Grammar.nodes i word e)
    (heq : e = .leaf name target write move event)
    (head : Int) (left tail : List Bool) :
    ∃ pre bit, word = pre ++ [bit] ∧
      rawSystem.Block ⟨Grammar.nodes[i].state, head, ⟨left, word ++ tail⟩⟩ word.length
        ⟨target, move.apply (head + (pre.length : Int)),
          Grammar.finalTape pre bit write move left tail⟩ event.toList := by
  induction h generalizing head left with
  | leaf i bit e he hleaf =>
    rw [heq] at he
    have hr := Grammar.literal_rows i bit
    rw [he] at hr
    have hrow : raw.table.row Grammar.nodes[i].state bit = ⟨write, move, target, false⟩ := by
      simpa [Grammar.expected] using congrArg Prod.fst hr
    have hev : rawLabels.at Grammar.nodes[i].state bit = event := by
      simpa [Grammar.expected] using congrArg Prod.snd hr
    have hs : rawSystem.step ⟨Grammar.nodes[i].state, head, ⟨left, bit :: tail⟩⟩ =
        (⟨target, move.apply head, Grammar.finalTape [] bit write move left tail⟩, event.toList) := by
      cases move <;> simp only [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read,
        List.headD_cons, hrow, hev, Grammar.finalTape, List.reverse_nil, List.nil_append]
    exact ⟨[], bit, rfl, by simpa using WordEventSystem.Block.single rawSystem hs⟩
  | step i j bit path e he rest ih =>
    have hr := Grammar.literal_rows i bit
    rw [he] at hr
    have hrow : raw.table.row Grammar.nodes[i].state bit = ⟨bit, .right, Grammar.nodes[j].state, false⟩ := by
      simpa [Grammar.expected] using congrArg Prod.fst hr
    have hev : rawLabels.at Grammar.nodes[i].state bit = none := by
      simpa [Grammar.expected] using congrArg Prod.snd hr
    have hs : rawSystem.step ⟨Grammar.nodes[i].state, head, ⟨left, bit :: (path ++ tail)⟩⟩ =
        (⟨Grammar.nodes[j].state, head + 1, ⟨bit :: left, path ++ tail⟩⟩, []) := by
      simp only [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, List.headD_cons,
        hrow, hev, Move.apply, moveRight, Option.toList_none, List.drop_succ_cons, List.drop_zero]
    obtain ⟨pre, last, hp, hb⟩ := ih heq (head + 1) (bit :: left)
    have hwhole := (WordEventSystem.Block.single rawSystem hs).trans rawSystem hb
    refine ⟨bit :: pre, last, by simp [hp], ?_⟩
    have hh : head + 1 + (pre.length : Int) = head + ((bit :: pre).length : Int) := by
      simp only [List.length_cons]; omega
    simpa only [List.cons_append, List.length_cons, Nat.succ_eq_add_one, List.nil_append,
      hh, Grammar.finalTape, List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_comm] using hwhole

private theorem root_fin : Grammar.nodes[(157 : Fin 158)].state = 79 := by decide

/-- A checked root-to-named-increment grammar path followed by its clean-gap
preparation is an exact positive physical segment. The path bits and clean
finite gap are explicit tape preconditions; reachability is not assumed. -/
theorem physical_path_prepare (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨left, word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ pre bit middle finish,
      word = pre ++ [bit] ∧
      (machineWordSystem raw rawLabels).Block c word.length middle [] ∧
      (machineWordSystem raw rawLabels).Block c (word.length + (gap + 3)) finish [] ∧
      Related ⟨72, head + (word.length : Int) + ((gap + 1 : Nat) : Int),
        moveLeft ⟨List.replicate gap true ++ false :: true :: (write :: (pre.reverse ++ left)),
          true :: tail⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (word.length + (gap + 3))
        (mapConfig finish) [] ∧ 0 < word.length + (gap + 3) := by
  obtain ⟨pre, bit, hw, hb⟩ := follow_named hpath rfl head left
    (false :: false :: (List.replicate gap false ++ true :: tail))
  have hh : head + (pre.length : Int) + 1 = head + (word.length : Int) := by
    rw [hw]; simp; omega
  have hb' : rawSystem.Block ⟨79, head,
      ⟨left, word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ word.length
      ⟨Selector.entryState r, head + (word.length : Int),
        ⟨write :: (pre.reverse ++ left), false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ [] := by
    rw [root_fin] at hb
    simpa [Grammar.finalTape, moveRight, Move.apply, hh] using hb
  obtain ⟨middle, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb'
  obtain ⟨finish, hp', hr', hq', _⟩ := physical_prepare_gap r gap (head + (word.length : Int))
    (write :: (pre.reverse ++ left)) tail middle hr
  have hq := BootstrapScan.mapped_block hp
  refine ⟨pre, bit, middle, finish, hw, hp, ?_, hr', ?_, by omega⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp'
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq'

example : NamedPath Grammar.nodes 157 [false, false, false, true, true, false]
    (.leaf "3.scratch.copy.inc" 58 false .right none) := by
  apply NamedPath.step 157 141 false _ _ (by decide)
  apply NamedPath.step 141 31 false _ _ (by decide)
  apply NamedPath.step 31 2 false _ _ (by decide)
  apply NamedPath.step 2 1 true _ _ (by decide)
  apply NamedPath.step 1 0 true _ _ (by decide)
  exact NamedPath.leaf 0 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

example : rawSystem.Block
    ⟨79, 0, ⟨[], [false, false, false, true, true, false, false, false,
      false, false, true, false, true, false]⟩⟩ 11
    ⟨72, 9, ⟨[true, false, true, false, true, true, false, false, false],
      [true, true, false, true, false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[], [false, false, false, true, true, false, false, false,
      false, false, true, false, true, false]⟩⟩ 10
    ⟨72, 9, ⟨[true, false, true, false, true, true, false, false, false],
      [true, true, false, true, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨79, 0, ⟨[], [false, false, false, true, true, false, false, false,
        false, false, true, false, true, false]⟩⟩ 10 ≠
      ⟨72, 9, ⟨[true, false, true, false, true, true, false, false, false],
        [true, true, false, true, false]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.Preparation
