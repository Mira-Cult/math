import PASoundness.M236BreakCoverage
import PASoundness.M236ContinuePadding
/-! Checked occurrence-level successor destinations for named breaks. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Break
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def popMany : Nat → List Bool → Option (List Bool)
  | 0, bits => some bits
  | n + 1, bits => do
      let (_, rest) ← Control.pop bits
      popMany n rest

/-- The finite successor rule, expressed as a root-relative prefix. -/
def successorPrefix (level : Nat) (word : List Bool) : Option (List Bool) := do
  let rest ← popMany (level + 1) ([true, true, false] ++ word).reverse
  match rest.reverse ++ [true] with
  | [true, true] => some []
  | true :: true :: true :: _ => some []
  | true :: true :: false :: tail => some tail
  | _ => none

def successorOK (word : List Bool) : Bool :=
  let pre := word.dropLast
  match Continue.pathName 157 word with
  | some "_break.1" =>
    match successorPrefix 1 word, candidate1 pre with
    | some source, some (_, _, _, _, residual) => Continue.sameResolved source residual
    | _, _ => false
  | some "_break.3" =>
    match successorPrefix 3 word, candidate3 pre with
    | some source, some (_, _, _, _, _, _, residual) => Continue.sameResolved source residual
    | _, _ => false
  | _ => true

def paddingOK (word : List Bool) : Bool :=
  let pre := word.dropLast
  match Continue.pathName 157 word with
  | some "_break.1" =>
    match candidate1 pre with
    | some (_, _, _, _, residual) => Continue.fitsPadding residual
    | none => false
  | some "_break.3" =>
    match candidate3 pre with
    | some (_, _, _, _, _, _, residual) => Continue.fitsPadding residual
    | none => false
  | _ => true

/-- All literal break occurrences agree with the finite successor rule. -/
theorem successor_checked : Grammar.completePaths.all successorOK = true := by decide

/-- Two zero cells suffice for the resolved literal break destination. -/
theorem padding_checked : Grammar.completePaths.all paddingOK = true := by decide

theorem successor1_destination (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (first scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : candidate1 pre = some (first, scratch, runs, bit, residual)) :
    ∃ source next, successorPrefix 1 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp successor_checked) (pre ++ [last]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  unfold successorOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  cases hs : successorPrefix 1 (pre ++ [last]) with
  | none => simp [hs] at hc
  | some source =>
    have hh : Continue.sameResolved source residual = true := by simpa [hs] using hc
    obtain ⟨next, h1, h2⟩ := Continue.sameResolved_sound source residual hh
    exact ⟨source, next, rfl, h1, h2⟩

theorem successor3_destination (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (first second third scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : candidate3 pre = some (first, second, third, scratch, runs, bit, residual)) :
    ∃ source next, successorPrefix 3 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp successor_checked) (pre ++ [last]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  unfold successorOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  cases hs : successorPrefix 3 (pre ++ [last]) with
  | none => simp [hs] at hc
  | some source =>
    have hh : Continue.sameResolved source residual = true := by simpa [hs] using hc
    obtain ⟨next, h1, h2⟩ := Continue.sameResolved_sound source residual hh
    exact ⟨source, next, rfl, h1, h2⟩

theorem padding1_prefix (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (first scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual next : List Bool)
    (hcan : candidate1 pre = some (first, scratch, runs, bit, residual))
    (hnext : Control.resolveZeros Grammar.nodes 158 157 residual = some next) :
    next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp padding_checked) (pre ++ [last]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  unfold paddingOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  unfold Continue.fitsPadding at hc
  rw [hnext] at hc
  exact of_decide_eq_true hc

theorem padding3_prefix (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (first second third scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual next : List Bool)
    (hcan : candidate3 pre = some (first, second, third, scratch, runs, bit, residual))
    (hnext : Control.resolveZeros Grammar.nodes 158 157 residual = some next) :
    next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp padding_checked) (pre ++ [last]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  unfold paddingOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  unfold Continue.fitsPadding at hc
  rw [hnext] at hc
  exact of_decide_eq_true hc
end PASoundness.M236.Break
