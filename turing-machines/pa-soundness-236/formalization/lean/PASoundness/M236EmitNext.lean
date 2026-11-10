import PASoundness.M236EmitSuccessor
/-! Marked output returns followed by their checked literal successor. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A prepared continue-style output returns and traverses its checked
successor leaf when the displayed two-zero gap is present. -/
theorem physical_continue_through_next (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [false])
      (.leaf (emitName b) 72 true .left (some b)))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [false]) ++ (List.replicate (2 + extra) false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      Break.successorPrefix 0 (pre ++ [false]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      next = nextPre ++ [nextLast] ∧
      Grammar.edge Grammar.nodes j nextLast = .leaf name target write move event ∧
      0 < time ∧ 0 < next.length ∧
      (machineWordSystem raw rawLabels).Block c time mid [b] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish (b :: event.toList) ∧
      Related ⟨target, move.apply (endHead + (nextPre.length : Int)),
        Grammar.finalTape nextPre nextLast write move
          (false :: true :: true :: (List.replicate 7 false ++ left))
          ((residual ++ List.replicate 2 false).drop next.length ++
            (List.replicate extra false ++ true :: false :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) (b :: event.toList) := by
  obtain ⟨time, endHead, residual, mid, first, runs, bit, hcan, ht, hp, hr, hq⟩ :=
    physical_covered_continue b pre hpath (2 + extra) head left tail c hrel
  obtain ⟨source, next, hsource, hnext1, hnext2, hprefix⟩ :=
    continue_destination b pre hpath first runs bit residual hcan
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := Continue.physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) (true :: false :: tail) mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

/-- A prepared cleanup-style output returns and traverses its checked
successor leaf when the displayed two-zero gap is present. -/
theorem physical_cleanup_through_next (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [true])
      (.leaf (emitName b) 68 false .left (some b)))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [true]) ++ (List.replicate (2 + extra) false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      Break.successorPrefix 0 (pre ++ [true]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      next = nextPre ++ [nextLast] ∧
      Grammar.edge Grammar.nodes j nextLast = .leaf name target write move event ∧
      0 < time ∧ 0 < next.length ∧
      (machineWordSystem raw rawLabels).Block c time mid [b] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish (b :: event.toList) ∧
      Related ⟨target, move.apply (endHead + (nextPre.length : Int)),
        Grammar.finalTape nextPre nextLast write move
          (false :: true :: true :: (List.replicate 7 false ++ left))
          ((residual ++ List.replicate 2 false).drop next.length ++
            (List.replicate extra false ++ true :: false :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) (b :: event.toList) := by
  obtain ⟨time, endHead, residual, mid, scratch, runs, bit, hcan, ht, hp, hr, hq⟩ :=
    physical_covered_cleanup b pre hpath (2 + extra) head left tail c hrel
  obtain ⟨source, next, hsource, hnext1, hnext2, hprefix⟩ :=
    cleanup_destination b pre hpath scratch runs bit residual hcan
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := Continue.physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) (true :: false :: tail) mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

end PASoundness.M236.Emit
