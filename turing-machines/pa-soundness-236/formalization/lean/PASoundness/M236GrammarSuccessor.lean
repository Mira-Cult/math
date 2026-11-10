import PASoundness.M236Sentinel
/-! Checked finite grammar successors and their physical traversal. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

/-- Consecutive leaf occurrences, wrapping at the outer sentinel. -/
def adjacentPaths : List (List Bool × List Bool) :=
  Grammar.completePaths.zip (Grammar.completePaths.drop 1 ++ [Grammar.completePaths.headD []])

def adjacentOK (pair : List Bool × List Bool) : Bool :=
  match decodeOne pair.1 with
  | none => false
  | some (_, tail) => decide (tail ++ List.replicate (pair.2.length - tail.length) false = pair.2 ∧
      pair.2.length - tail.length ≤ 5)

/-- Exhaustive reflection over the 760 literal grammar leaf occurrences. -/
theorem adjacent_checked : adjacentPaths.all adjacentOK = true := by decide

/-- Every adjacent occurrence has a decoded physical successor prefix whose
remaining path consists only of zeros. No source-program edge is asserted. -/
theorem adjacent_successor {word next : List Bool}
    (h : (word, next) ∈ adjacentPaths) :
    ∃ (bit : Bool) (tail : List Bool),
      decodeOne word = some (bit, tail) ∧
      tail ++ List.replicate (next.length - tail.length) false = next ∧
      next.length - tail.length ≤ 5 := by
  have hc := (List.all_eq_true.mp adjacent_checked) (word, next) h
  unfold adjacentOK at hc
  cases hd : decodeOne word with
  | none => simp [hd] at hc
  | some p =>
    rcases p with ⟨bit, tail⟩
    simp only [hd] at hc
    exact ⟨bit, tail, rfl, of_decide_eq_true hc⟩

/-- The occurrence list has exactly the 760 checked grammar leaves. -/
theorem adjacent_count : adjacentPaths.length = 760 := by decide

theorem adjacent_next_leaf {word next : List Bool} (h : (word, next) ∈ adjacentPaths) :
    Grammar.LeafPath Grammar.nodes 157 next := by
  have hm := (List.of_mem_zip h).2
  simp only [List.mem_append, List.mem_singleton] at hm
  have hn : next ∈ Grammar.completePaths := by
    rcases hm with hm | rfl
    · exact List.mem_of_mem_drop hm
    · cases he : Grammar.completePaths with
      | nil =>
        have hc := Grammar.leaf_count
        simp [he] at hc
      | cons first rest => simp
  exact (Grammar.leaf_path_iff_mem next).mpr hn

/-- If enough blank cells remain after a physical return, the exact adjacent
leaf path is present at the root and its literal transitions execute with
its own exact event word. The spacing premise is explicit. -/
theorem physical_adjacent_follow {word next : List Bool} (bit : Bool) (pcTail : List Bool)
    (hpair : (word, next) ∈ adjacentPaths) (hdecode : decodeOne word = some (bit, pcTail))
    (padding : Nat) (hspace : next.length - pcTail.length ≤ padding)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head, ⟨left, pcTail ++ (List.replicate padding false ++ tail)⟩⟩ c) :
    ∃ (pre : List Bool) (j : Fin 158) (last : Bool) (name : String)
      (target : Fin 237) (write : Bool) (move : Move) (event : Option Bool) (finish : Config 237),
      next = pre ++ [last] ∧ Grammar.edge Grammar.nodes j last = .leaf name target write move event ∧
      (machineWordSystem raw rawLabels).Block c next.length finish event.toList ∧
      Related ⟨target, move.apply (head + (pre.length : Int)),
        Grammar.finalTape pre last write move left
          (List.replicate (padding - (next.length - pcTail.length)) false ++ tail)⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) next.length
        (mapConfig finish) event.toList ∧ 0 < next.length := by
  obtain ⟨b, p, hd, he, hbound⟩ := adjacent_successor hpair
  rw [hdecode] at hd
  cases hd
  let need := next.length - pcTail.length
  have he' : pcTail ++ List.replicate need false = next := he
  have hn : need + (padding - need) = padding := by dsimp [need]; omega
  have htape : pcTail ++ (List.replicate padding false ++ tail) =
      next ++ (List.replicate (padding - (next.length - pcTail.length)) false ++ tail) := by
    change pcTail ++ (List.replicate padding false ++ tail) =
      next ++ (List.replicate (padding - need) false ++ tail)
    calc
      _ = pcTail ++ ((List.replicate need false ++ List.replicate (padding - need) false) ++ tail) := by
        rw [List.replicate_append_replicate, hn]
      _ = (pcTail ++ List.replicate need false) ++ (List.replicate (padding - need) false ++ tail) := by
        simp only [List.append_assoc]
      _ = next ++ (List.replicate (padding - need) false ++ tail) := by rw [he']
  rw [htape] at hrel
  have hroot : Related ⟨Grammar.nodes[157].state, head,
      ⟨left, next ++ (List.replicate (padding - (next.length - pcTail.length)) false ++ tail)⟩⟩ c := by
    simpa only [Grammar.root_state] using hrel
  exact Grammar.physical_follow_leaf (adjacent_next_leaf hpair) head left
    (List.replicate (padding - (next.length - pcTail.length)) false ++ tail) c hroot

/-- An increment followed by the next depth-first grammar leaf is a pair of
positive physical segments when the explicit finite blank-space bound holds.
The second segment retains its own exact event, if any. -/
theorem physical_increment_to_adjacent (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (hgap : 3 ≤ gap) (word next : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (hpair : (word, next) ∈ adjacentPaths) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail pre : List Bool)
      (j : Fin 158) (last : Bool) (name : String) (target : Fin 237) (write2 : Bool)
      (move : Move) (event : Option Bool) (mid finish : Config 237),
      decodeOne word = some (bit, pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time mid [] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish event.toList ∧
      next = pre ++ [last] ∧ Grammar.edge Grammar.nodes j last = .leaf name target write2 move event ∧
      Related ⟨target, move.apply (endHead + (pre.length : Int)),
        Grammar.finalTape pre last write2 move (false :: true :: true :: (List.replicate 7 false ++ left))
          (List.replicate ((gap + scratch + 2) - (next.length - pcTail.length)) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (time + next.length)
        (mapConfig finish) event.toList ∧ 0 < next.length := by
  obtain ⟨time, endHead, scratch, bit, pcTail, mid, hdecode, ht, hp, hr, hq, hd⟩ :=
    physical_root_increment_decoded registers r reserve gap word write hpath head left tail c hrel
  obtain ⟨bit', tail', hdec', he, hbound⟩ := adjacent_successor hpair
  rw [hdecode] at hdec'
  cases hdec'
  have hspace : next.length - pcTail.length ≤ gap + scratch + 2 := by omega
  obtain ⟨pre, j, last, name, target, write2, move, event, finish, hw, hedge, hp2, hr2, hq2, ht2⟩ :=
    physical_adjacent_follow bit pcTail hpair hdecode (gap + scratch + 2) hspace endHead
      (false :: true :: true :: (List.replicate 7 false ++ left))
      (true :: false :: (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)) mid hr
  refine ⟨time, endHead, scratch, bit, pcTail, pre, j, last, name, target, write2, move, event, mid, finish,
    hdecode, ht, hp, ?_, hw, hedge, hr2, ?_, ht2⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp2
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq2
/-- A positive decrement followed by the adjacent leaf preserves its exact event. -/
theorem physical_positive_to_adjacent (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat) (hgap : 3 ≤ gap) (word next : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hpair : (word, next) ∈ adjacentPaths) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail pre : List Bool)
      (j : Fin 158) (last : Bool) (name : String) (target : Fin 237) (write2 : Bool)
      (move : Move) (event : Option Bool) (mid finish : Config 237),
      decodeOne word = some (bit, pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time mid [] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish event.toList ∧
      next = pre ++ [last] ∧ Grammar.edge Grammar.nodes j last = .leaf name target write2 move event ∧
      Related ⟨target, move.apply (endHead + (pre.length : Int)),
        Grammar.finalTape pre last write2 move (false :: true :: true :: (List.replicate 7 false ++ left))
          (List.replicate ((gap + scratch + 2) - (next.length - pcTail.length)) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (time + next.length)
        (mapConfig finish) event.toList ∧ 0 < next.length := by
  obtain ⟨time, endHead, scratch, bit, pcTail, mid, hdecode, ht, hp, hr, hq, hd, hout⟩ :=
    physical_root_positive_decoded registers r value hvalue reserve gap word write hpath head left tail c hrel
  obtain ⟨bit', tail', hdec', he, hbound⟩ := adjacent_successor hpair
  rw [hdecode] at hdec'
  cases hdec'
  have hspace : next.length - pcTail.length ≤ gap + scratch + 2 := by omega
  obtain ⟨pre, j, last, name, target, write2, move, event, finish, hw, hedge, hp2, hr2, hq2, ht2⟩ :=
    physical_adjacent_follow bit pcTail hpair hdecode (gap + scratch + 2) hspace endHead
      (false :: true :: true :: (List.replicate 7 false ++ left))
      (true :: false :: (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail)) mid hr
  refine ⟨time, endHead, scratch, bit, pcTail, pre, j, last, name, target, write2, move, event, mid, finish,
    hdecode, ht, hp, ?_, hw, hedge, hr2, ?_, ht2⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp2
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq2

end PASoundness.M236.Control
