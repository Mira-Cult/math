import PASoundness.M236ContinueCoverage
/-! Checked occurrence-level restart destination comparison. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- Remove a specified finite number of nearest one markers. -/
def popMany : Nat → List Bool → Option (List Bool)
  | 0, bits => some bits
  | n + 1, bits => do
      let (_, rest) ← popOne bits
      popMany n rest

/-- The producer's occurrence-level restart convention, represented as a
root-relative prefix. Reaching either outer sentinel wraps to the root. -/
def restartPrefix (level : Nat) (word : List Bool) : Option (List Bool) := do
  let rest ← popMany (level + 1) ([true, true, false] ++ word).reverse
  match (true :: rest).reverse with
  | [true, true] => some []
  | true :: true :: true :: _ => some []
  | true :: true :: false :: tail => some tail
  | _ => none

def sameResolved (a b : List Bool) : Bool :=
  match Control.resolveZeros Grammar.nodes 158 157 a, Control.resolveZeros Grammar.nodes 158 157 b with
  | some x, some y => x == y
  | _, _ => false

def restartOK (word : List Bool) : Bool :=
  let pre := word.dropLast
  match pathName 157 word with
  | some "_continue.1" =>
    match restartPrefix 1 word, candidate1 pre with
    | some source, some (_, _, _, residual) => sameResolved source residual
    | _, _ => false
  | some "_continue.2" =>
    match restartPrefix 2 word, candidate2 pre with
    | some source, some (_, _, _, _, residual) => sameResolved source residual
    | _, _ => false
  | some "_continue.3" =>
    match restartPrefix 3 word, candidate3 pre with
    | some source, some (_, _, _, _, _, residual) => sameResolved source residual
    | _, _ => false
  | _ => true

/-- Every named continue occurrence has the same resolved literal destination
under the restart convention and its physically returned path. -/
theorem restart_checked : Grammar.completePaths.all restartOK = true := by decide
theorem sameResolved_sound (a b : List Bool) (h : sameResolved a b = true) :
    ∃ next, Control.resolveZeros Grammar.nodes 158 157 a = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 b = some next := by
  unfold sameResolved at h
  cases ha : Control.resolveZeros Grammar.nodes 158 157 a with
  | none => simp [ha] at h
  | some x =>
    cases hb : Control.resolveZeros Grammar.nodes 158 157 b with
    | none => simp [ha, hb] at h
    | some y =>
      simp only [ha, hb, beq_iff_eq] at h
      subst y
      exact ⟨x, rfl, rfl⟩

theorem restart1_destination (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : candidate1 pre = some (first, runs, bit, residual)) :
    ∃ source next, restartPrefix 1 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp restart_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold restartOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  cases hs : restartPrefix 1 (pre ++ [last]) with
  | none => simp [hs] at hc
  | some source =>
    have hh : sameResolved source residual = true := by simpa [hs] using hc
    obtain ⟨next, h1, h2⟩ := sameResolved_sound source residual hh
    exact ⟨source, next, rfl, h1, h2⟩

theorem restart2_destination (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (first second : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : candidate2 pre = some (first, second, runs, bit, residual)) :
    ∃ source next, restartPrefix 2 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp restart_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold restartOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  cases hs : restartPrefix 2 (pre ++ [last]) with
  | none => simp [hs] at hc
  | some source =>
    have hh : sameResolved source residual = true := by simpa [hs] using hc
    obtain ⟨next, h1, h2⟩ := sameResolved_sound source residual hh
    exact ⟨source, next, rfl, h1, h2⟩

theorem restart3_destination (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (first second third : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : candidate3 pre = some (first, second, third, runs, bit, residual)) :
    ∃ source next, restartPrefix 3 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp restart_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold restartOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  cases hs : restartPrefix 3 (pre ++ [last]) with
  | none => simp [hs] at hc
  | some source =>
    have hh : sameResolved source residual = true := by simpa [hs] using hc
    obtain ⟨next, h1, h2⟩ := sameResolved_sound source residual hh
    exact ⟨source, next, rfl, h1, h2⟩
end PASoundness.M236.Continue
