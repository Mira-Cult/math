import PASoundness.M236TransferResidual
/-! Literal transfer/output segments preserve the common control-space budget. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A named continue.1 physical return preserves the common spacing budget. -/
theorem physical_continue1_preserves_gap_budget (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [last]).length)
    (head : Int) (left suffix : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ false :: false :: (List.replicate gap false ++ suffix)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Continue.restartPrefix 1 (pre ++ [last]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [last]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ suffix)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + gap) false ++ suffix)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, source, next, finish, first, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := Continue.physical_restart_continue1 pre last hpath head left (List.replicate (2 + gap) false ++ suffix) c hinput
  have hres := residual_continue1 pre last hpath first runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [last]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (suffix)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

/-- A named continue.2 physical return preserves the common spacing budget. -/
theorem physical_continue2_preserves_gap_budget (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [last]).length)
    (head : Int) (left suffix : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ false :: false :: (List.replicate gap false ++ suffix)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Continue.restartPrefix 2 (pre ++ [last]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [last]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ suffix)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + gap) false ++ suffix)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, source, next, finish, first, second, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := Continue.physical_restart_continue2 pre last hpath head left (List.replicate (2 + gap) false ++ suffix) c hinput
  have hres := residual_continue2 pre last hpath first second runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [last]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (suffix)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

/-- A named continue.3 physical return preserves the common spacing budget. -/
theorem physical_continue3_preserves_gap_budget (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [last]).length)
    (head : Int) (left suffix : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ false :: false :: (List.replicate gap false ++ suffix)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Continue.restartPrefix 3 (pre ++ [last]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [last]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ suffix)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + gap) false ++ suffix)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, source, next, finish, first, second, third, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := Continue.physical_restart_continue3 pre last hpath head left (List.replicate (2 + gap) false ++ suffix) c hinput
  have hres := residual_continue3 pre last hpath first second third runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [last]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (suffix)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

/-- A named break.1 physical return preserves the common spacing budget. -/
theorem physical_break1_preserves_gap_budget (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [last]).length)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ false :: false :: (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Break.successorPrefix 1 (pre ++ [last]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [last]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + gap) false ++ true :: false :: tail)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, source, next, finish, first, scratch, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := Break.physical_successor_break1 pre last hpath (2 + gap) head left tail c hinput
  have hres := residual_break1 pre last hpath first scratch runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [last]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (true :: false :: tail)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

/-- A named break.3 physical return preserves the common spacing budget. -/
theorem physical_break3_preserves_gap_budget (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [last]).length)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ false :: false :: (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Break.successorPrefix 3 (pre ++ [last]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [last]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate (2 + gap) false ++ true :: false :: tail)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, source, next, finish, first, second, third, scratch, runs, bit, hcan, hsource, hnext1, hnext2,
    hleaf, ht, hp, hr, hq⟩ := Break.physical_successor_break3 pre last hpath (2 + gap) head left tail c hinput
  have hres := residual_break3 pre last hpath first second third scratch runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [last]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (true :: false :: tail)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

/-- A continue-style fused output preserves the common spacing budget and
emits exactly its marked bit. -/
theorem physical_emit_continue_preserves_gap_budget (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [false])
      (.leaf (Emit.emitName b) 72 true .left (some b)))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [false]).length)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [false]) ++ false :: false :: (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Break.successorPrefix 0 (pre ++ [false]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [false]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [b] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [b] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [false]) ++ (List.replicate (2 + gap) false ++ true :: false :: tail)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, finish, first, runs, bit, hcan, ht, hp, hr, hq⟩ :=
    Emit.physical_covered_continue b pre hpath (2 + gap) head left tail c hinput
  obtain ⟨source, next, hsource, hnext1, hnext2, hprefix⟩ :=
    Emit.continue_destination b pre hpath first runs bit residual hcan
  have hres := residual_emit_continue b pre hpath first runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [false]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (true :: false :: tail)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

/-- A cleanup-style fused output preserves the common spacing budget and
emits exactly its marked bit. -/
theorem physical_emit_cleanup_preserves_gap_budget (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [true])
      (.leaf (Emit.emitName b) 68 false .left (some b)))
    (gap : Nat) (hbudget : 25 ≤ gap + (pre ++ [true]).length)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [true]) ++ false :: false :: (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (next source : List Bool) (gap' time : Nat) (endHead : Int) (finish : Config 237),
      Break.successorPrefix 0 (pre ++ [true]) = some source ∧
      resolveZeros Grammar.nodes 158 157 source = some next ∧
      next.length + gap' = (pre ++ [true]).length + gap ∧ 25 ≤ next.length + gap' ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time finish [b] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          next ++ false :: false :: (List.replicate gap' false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [b] := by
  have hinput : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [true]) ++ (List.replicate (2 + gap) false ++ true :: false :: tail)⟩⟩ c := by
    simpa only [two_zeros] using hrel
  obtain ⟨time, endHead, residual, finish, scratch, runs, bit, hcan, ht, hp, hr, hq⟩ :=
    Emit.physical_covered_cleanup b pre hpath (2 + gap) head left tail c hinput
  obtain ⟨source, next, hsource, hnext1, hnext2, hprefix⟩ :=
    Emit.cleanup_destination b pre hpath scratch runs bit residual hcan
  have hres := residual_emit_cleanup b pre hpath scratch runs bit residual hcan
  obtain ⟨gap', hf, hc, hb⟩ := normalize_transfer_budget (pre ++ [true]) residual next gap
    (Redispatch.named_leaf_path hpath) hres hnext2 hbudget (true :: false :: tail)
  rw [hf] at hr
  exact ⟨next, source, gap', time, endHead, finish, hsource, hnext1, hc, hb, ht, hp, hr, hq⟩

end PASoundness.M236.Control
