import PASoundness.M236ContinuePadding
/-! Continue returns followed by the checked destination leaf. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A prepared continue.1 traverses its formal restart destination when
at least two blank cells follow the control word. Both segments have positive
length and the second segment's exact event is retained. -/
theorem physical_continue1_through_next (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + extra) false ++ tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      restartPrefix 1 (pre ++ [last]) = some source ∧
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
          ((residual ++ List.replicate 2 false).drop next.length ++ (List.replicate extra false ++ tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) event.toList := by
  obtain ⟨time, endHead, residual, source, next, mid, first, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := physical_restart_continue1 pre last hpath head left
      (List.replicate (2 + extra) false ++ tail) c hrel
  have hprefix := padding1_prefix pre last hpath first runs bit residual next hcan hnext2
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) tail mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

/-- A prepared continue.2 traverses its formal restart destination when
at least two blank cells follow the control word. Both segments have positive
length and the second segment's exact event is retained. -/
theorem physical_continue2_through_next (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + extra) false ++ tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      restartPrefix 2 (pre ++ [last]) = some source ∧
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
          ((residual ++ List.replicate 2 false).drop next.length ++ (List.replicate extra false ++ tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) event.toList := by
  obtain ⟨time, endHead, residual, source, next, mid, first, second, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := physical_restart_continue2 pre last hpath head left
      (List.replicate (2 + extra) false ++ tail) c hrel
  have hprefix := padding2_prefix pre last hpath first second runs bit residual next hcan hnext2
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) tail mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

/-- A prepared continue.3 traverses its formal restart destination when
at least two blank cells follow the control word. Both segments have positive
length and the second segment's exact event is retained. -/
theorem physical_continue3_through_next (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + extra) false ++ tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next nextPre : List Bool)
      (j : Fin 158) (nextLast : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      restartPrefix 3 (pre ++ [last]) = some source ∧
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
          ((residual ++ List.replicate 2 false).drop next.length ++ (List.replicate extra false ++ tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (time + next.length) (mapConfig finish) event.toList := by
  obtain ⟨time, endHead, residual, source, next, mid, first, second, third, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := physical_restart_continue3 pre last hpath head left
      (List.replicate (2 + extra) false ++ tail) c hrel
  have hprefix := padding3_prefix pre last hpath first second third runs bit residual next hcan hnext2
  obtain ⟨nextPre, j, nextLast, name, target, write, move, event, finish,
    hw, hedge, hp', hr', hq', ht'⟩ := physical_follow_padded residual next hnext2 hprefix extra endHead
      (false :: true :: true :: (List.replicate 7 false ++ left)) tail mid hr
  exact ⟨time, endHead, residual, source, next, nextPre, j, nextLast, name, target, write, move,
    event, mid, finish, hsource, hnext1, hnext2, hw, hedge, ht, ht', hp,
    by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq'⟩

end PASoundness.M236.Continue
