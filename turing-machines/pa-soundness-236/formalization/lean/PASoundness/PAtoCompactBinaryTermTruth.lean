import PASoundness.PAtoCompactTermGraphTruth

/-! Conditional standard-HF truth steps for the generated binary term
graphs. The truth of each child under the displayed updated assignments is
an explicit hypothesis. No K witness-existence or full term-truth theorem is
asserted here. -/
namespace PASoundness.PAtoCompactBinaryTermTruth

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermRenamingSemantics PASoundness.PAtoCompactTermGraphTruth
open PASoundness.HFCoding
open PASoundness.CompactMatrix (Environment update)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The two existentially selected child results are ordinal codes because
each generated child graph carries its own candidate-domain guard. -/
theorem binary_graph_truth {α : Type} (varName : α → Nat)
    (left right : Peano.language.Term α) (out base n m k : Nat)
    (ρ : Environment) (op : Nat → Nat → Nat) (relation : CompactNamed.Formula)
    (hout : out < base) (hresult : ρ out = (ordinal k).code)
    (leftTruth : ∀ i j, (termGraph varName left base (base + 64)).Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ i = n)
    (rightTruth : ∀ i j, (termGraph varName right (base + 1)
      (base + 64 + termCost left)).Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ j = m)
    (relationTruth : ∀ i j, relation.Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ k = op i j) :
    (andF (domainAt base out) (.ex base (.ex (base + 1)
      (andF (termGraph varName left base (base + 64))
        (andF (termGraph varName right (base + 1) (base + 64 + termCost left))
          relation))))).Realize ρ ↔ k = op n m := by
  rw [andF_realize]
  have hd := domainAt_ordinal base out k (by omega) ρ hresult
  simp only [hd, true_and, CompactNamed.Formula.Realize]
  constructor
  · rintro ⟨u, v, h⟩
    have hl := ((andF_realize _ _ _).mp h).1
    have hr := ((andF_realize _ _ _).mp ((andF_realize _ _ _).mp h).2).1
    have hrel := ((andF_realize _ _ _).mp ((andF_realize _ _ _).mp h).2).2
    have hld := termGraph_has_domain varName left base (base + 64) _ hl
    obtain ⟨i, hi⟩ := (domainAt_iff (base + 64) base (by omega) _).mp hld
    have hu : u = (ordinal i).code := by simpa [update] using hi
    have hrd := termGraph_has_domain varName right (base + 1)
      (base + 64 + termCost left) _ hr
    obtain ⟨j, hj⟩ := (domainAt_iff (base + 64 + termCost left) (base + 1)
      (by omega) _).mp hrd
    have hv : v = (ordinal j).code := by simpa [update] using hj
    subst u
    subst v
    have hleft := (leftTruth i j).mp hl
    have hright := (rightTruth i j).mp hr
    have hop := (relationTruth i j).mp hrel
    simpa [hleft, hright] using hop
  · intro h
    refine ⟨(ordinal n).code, (ordinal m).code, ?_⟩
    apply (andF_realize _ _ _).mpr
    refine ⟨(leftTruth n m).mpr rfl, ?_⟩
    apply (andF_realize _ _ _).mpr
    exact ⟨(rightTruth n m).mpr rfl, (relationTruth n m).mpr h⟩

/-- Conditional truth step for an actual generated addition node. -/
theorem addition_graph_truth {α : Type} (varName : α → Nat)
    (left right : Peano.language.Term α) (out base n m k : Nat) (ρ : Environment)
    (hout : out < base) (hresult : ρ out = (ordinal k).code)
    (leftTruth : ∀ i j, (termGraph varName left base (base + 64)).Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ i = n)
    (rightTruth : ∀ i j, (termGraph varName right (base + 1)
      (base + 64 + termCost left)).Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ j = m) :
    (termGraph varName (.func .add ![left, right]) out base).Realize ρ ↔ k = n + m := by
  change (andF (domainAt base out) (.ex base (.ex (base + 1)
    (andF (termGraph varName left base (base + 64))
      (andF (termGraph varName right (base + 1) (base + 64 + termCost left))
        (addAt base base (base + 1) out)))))).Realize ρ ↔ _
  apply binary_graph_truth varName left right out base n m k ρ (· + ·) _ hout hresult leftTruth rightTruth
  intro i j
  apply addAt_ordinal base base (base + 1) out i j k (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  · simp [update]
  · simp [update]
  · simpa [update, show out ≠ base by omega, show out ≠ base + 1 by omega] using hresult

/-- Conditional truth step for an actual generated multiplication node. -/
theorem multiplication_graph_truth {α : Type} (varName : α → Nat)
    (left right : Peano.language.Term α) (out base n m k : Nat) (ρ : Environment)
    (hout : out < base) (hresult : ρ out = (ordinal k).code)
    (leftTruth : ∀ i j, (termGraph varName left base (base + 64)).Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ i = n)
    (rightTruth : ∀ i j, (termGraph varName right (base + 1)
      (base + 64 + termCost left)).Realize
      (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) ↔ j = m) :
    (termGraph varName (.func .mul ![left, right]) out base).Realize ρ ↔ k = n * m := by
  change (andF (domainAt base out) (.ex base (.ex (base + 1)
    (andF (termGraph varName left base (base + 64))
      (andF (termGraph varName right (base + 1) (base + 64 + termCost left))
        (mulAt base base (base + 1) out)))))).Realize ρ ↔ _
  apply binary_graph_truth varName left right out base n m k ρ (· * ·) _ hout hresult leftTruth rightTruth
  intro i j
  apply mulAt_ordinal base base (base + 1) out i j k (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  · simp [update]
  · simp [update]
  · simpa [update, show out ≠ base by omega, show out ≠ base + 1 by omega] using hresult

end PASoundness.PAtoCompactBinaryTermTruth
