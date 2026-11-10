import PASoundness.M236GrammarSuccessor
/-! The checked adjacent ordering covers every literal grammar leaf. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

/-- The first projections of the checked 760 pairs are the full leaf list. -/
theorem adjacent_domain : adjacentPaths.map Prod.fst = Grammar.completePaths := by decide

/-- Every literal grammar leaf occurs as the first component of an adjacent pair. -/
theorem adjacent_exists (word : List Bool) (h : Grammar.LeafPath Grammar.nodes 157 word) :
    ∃ next, (word, next) ∈ adjacentPaths := by
  have hm : word ∈ adjacentPaths.map Prod.fst := by
    rw [adjacent_domain]
    exact Grammar.every_leaf_path word h
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hm
  rcases pair with ⟨a, next⟩
  simp only at he
  subst a
  exact ⟨next, hp⟩

/-- In particular every checked named leaf has an adjacent occurrence. -/
theorem named_adjacent_exists {word : List Bool} {edge : Grammar.Edge}
    (hpath : Preparation.NamedPath Grammar.nodes 157 word edge) :
    ∃ next, (word, next) ∈ adjacentPaths :=
  adjacent_exists word (Redispatch.named_leaf_path hpath)

/-- The named path determines an adjacent physical successor; no pair-membership premise is needed. -/
theorem physical_increment_to_next (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (hgap : 3 ≤ gap) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (next : List Bool), (word, next) ∈ adjacentPaths ∧ ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail pre : List Bool)
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
  obtain ⟨next, hpair⟩ := named_adjacent_exists hpath
  exact ⟨next, hpair, physical_increment_to_adjacent registers r reserve gap hgap word next write hpath hpair head left tail c hrel⟩

/-- The named path determines an adjacent physical successor; no pair-membership premise is needed. -/
theorem physical_positive_to_next (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap : Nat) (hgap : 3 ≤ gap) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (next : List Bool), (word, next) ∈ adjacentPaths ∧ ∃ (time : Nat) (endHead : Int) (scratch : Nat) (bit : Bool) (pcTail pre : List Bool)
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
  obtain ⟨next, hpair⟩ := named_adjacent_exists hpath
  exact ⟨next, hpair, physical_positive_to_adjacent registers r value hvalue reserve gap hgap word next write hpath hpair head left tail c hrel⟩

end PASoundness.M236.Control
