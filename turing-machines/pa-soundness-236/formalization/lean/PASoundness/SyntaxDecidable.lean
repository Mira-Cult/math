import PASoundness.FOL

namespace PASoundness.FOL

open FirstOrder FirstOrder.Language

variable {L : Language} {α : Type}
variable [DecidableEq α] [∀ n, DecidableEq (L.Functions n)]
  [∀ n, DecidableEq (L.Relations n)]

/-- Executable equality on mathlib's scoped formula syntax. -/
instance formulaDecidableEq : {n : Nat} → DecidableEq (L.BoundedFormula α n)
  | _, .falsum, .falsum => .isTrue rfl
  | _, .equal t u, .equal s v =>
      decidable_of_iff (t = s ∧ u = v) (by simp)
  | n, @BoundedFormula.rel _ _ _ l r ts, @BoundedFormula.rel _ _ _ k q us =>
      if h : l = k then
        decidable_of_iff (r = h ▸ q ∧ ∀ i : Fin l, ts i = us (Fin.cast h i)) (by
          subst h
          simp [funext_iff])
      else .isFalse (by simp [h])
  | n, .imp φ ψ, .imp χ θ =>
      letI : DecidableEq (L.BoundedFormula α n) := formulaDecidableEq
      decidable_of_iff (φ = χ ∧ ψ = θ) (by simp)
  | n, .all φ, .all ψ =>
      letI : DecidableEq (L.BoundedFormula α (n + 1)) := formulaDecidableEq
      decidable_of_iff (φ = ψ) (by simp)
  | _, .falsum, .equal _ _ | _, .falsum, .rel _ _ | _, .falsum, .imp _ _
  | _, .falsum, .all _ | _, .equal _ _, .falsum | _, .equal _ _, .rel _ _
  | _, .equal _ _, .imp _ _ | _, .equal _ _, .all _ | _, .rel _ _, .falsum
  | _, .rel _ _, .equal _ _ | _, .rel _ _, .imp _ _ | _, .rel _ _, .all _
  | _, .imp _ _, .falsum | _, .imp _ _, .equal _ _ | _, .imp _ _, .rel _ _
  | _, .imp _ _, .all _ | _, .all _, .falsum | _, .all _, .equal _ _
  | _, .all _, .rel _ _ | _, .all _, .imp _ _ => .isFalse (by simp)

end PASoundness.FOL
