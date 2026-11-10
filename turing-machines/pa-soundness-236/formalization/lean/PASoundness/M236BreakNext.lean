import PASoundness.M236BreakAlignment
/-! Break returns followed by the checked destination leaf. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Break
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A prepared break.1 traverses its formal successor destination when
at least two zero cells precede the restored anchor. Both segments have
positive length and the second segment's exact event is retained. -/
theorem physical_break1_through_next (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + extra) false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      successorPrefix 1 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      next = nextPre ++ [nextLast] ∧
      Grammar.edge Grammar.nodes j nextLast = .leaf name target write move event ∧
      0 < time ∧ 0 < next.length ∧
      (machineWordSystem raw rawLabels).Block c time mid [] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish event.toList ∧
      Related ⟨target, move.apply (endHead + (nextPre.length : Int)),
        Grammar.finalTape nextPre nextLast write move
          (false :: true :: true :: (List.replicate 7 false ++ left))
          ((residual ++ List.replicate 2 false).drop next.length ++
            (List.replicate extra false ++ true :: false :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) event.toList := by
  obtain ⟨time, endHead, residual, source, next, mid, first, scratch, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := physical_successor_break1 pre last hpath (2 + extra) head left tail c hrel
  have hprefix := padding1_prefix pre last hpath first scratch runs bit residual next hcan hnext2
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := Continue.physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) (true :: false :: tail) mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

/-- A prepared break.3 traverses its formal successor destination when
at least two zero cells precede the restored anchor. Both segments have
positive length and the second segment's exact event is retained. -/
theorem physical_break3_through_next (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + extra) false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      successorPrefix 3 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      next = nextPre ++ [nextLast] ∧
      Grammar.edge Grammar.nodes j nextLast = .leaf name target write move event ∧
      0 < time ∧ 0 < next.length ∧
      (machineWordSystem raw rawLabels).Block c time mid [] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish event.toList ∧
      Related ⟨target, move.apply (endHead + (nextPre.length : Int)),
        Grammar.finalTape nextPre nextLast write move
          (false :: true :: true :: (List.replicate 7 false ++ left))
          ((residual ++ List.replicate 2 false).drop next.length ++
            (List.replicate extra false ++ true :: false :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) event.toList := by
  obtain ⟨time, endHead, residual, source, next, mid, first, second, third, scratch, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := physical_successor_break3 pre last hpath (2 + extra) head left tail c hrel
  have hprefix := padding3_prefix pre last hpath first second third scratch runs bit residual next hcan hnext2
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := Continue.physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) (true :: false :: tail) mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

end PASoundness.M236.Break
