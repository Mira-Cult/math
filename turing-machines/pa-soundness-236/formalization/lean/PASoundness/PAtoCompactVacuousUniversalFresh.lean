import PASoundness.PAtoCompactVacuousUniversal

/-! Select a shared fresh binder and high guard block for two generated
universals. Recursive alignment of their renamed children is an explicit
finite K proof obligation. -/
namespace PASoundness.PAtoCompactVacuousUniversalFresh

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousUniversal

/-- A name below a domain guard's private block is absent from all its names
unless it is the guard's free operand. -/
theorem low_name_not_domain_names (base x z : Nat) (hz : z < base + 2) (hne : z ≠ x) :
    z ∉ (domainAt base x).names := by
  intro h
  rw [domainAt, mapNames_names] at h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  by_cases hj0 : j = 0
  · simp [oneMap, hj0] at hj
    exact hne hj.symm
  · simp [oneMap, hj0] at hj
    omega

/-- For a rebased guard, child-name freshness suffices for freshness in the
whole guarded body when the new label lies below the private block. -/
theorem universalBodyAt_fresh {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat)
    (base z : Nat) (hz : z < base + 2) (hne : z ≠ universalName body bound)
    (hf : z ∉ (scopedFormula (n+1) body (Fin.snoc bound (universalName body bound))).names) :
    z ∉ (universalBodyAt body bound base).names := by
  simp only [universalBodyAt, Formula.names, Finset.mem_union, not_or]
  exact ⟨low_name_not_domain_names base (universalName body bound) z hz hne, hf⟩

/-- A single name larger than both outer binders and every name in both
translated children. -/
def commonName {n m : Nat}
    (a : Peano.language.BoundedFormula Nat (n+1)) (ab : Fin n → Nat)
    (b : Peano.language.BoundedFormula Nat (m+1)) (bb : Fin m → Nat) : Nat :=
  max (universalName a ab) (max (universalName b bb)
    (((scopedFormula (n+1) a (Fin.snoc ab (universalName a ab))).names ∪
      (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb))).names).sup id)) + 1

/-- Two generated universals have K implications both ways once their renamed
children do. The common binder and guard allocation are chosen internally;
no semantic equivalence of the children is assumed. -/
def universals_of_common_child_auto {n m : Nat}
    (a : Peano.language.BoundedFormula Nat (n+1)) (ab : Fin n → Nat)
    (b : Peano.language.BoundedFormula Nat (m+1)) (bb : Fin m → Nat)
    (hforward : let z := commonName a ab b bb
      KDerivation (imp
        (replace (universalName a ab) z
          (scopedFormula (n+1) a (Fin.snoc ab (universalName a ab)))).encode
        (replace (universalName b bb) z
          (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb)))).encode))
    (hbackward : let z := commonName a ab b bb
      KDerivation (imp
        (replace (universalName b bb) z
          (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb)))).encode
        (replace (universalName a ab) z
          (scopedFormula (n+1) a (Fin.snoc ab (universalName a ab)))).encode)) :
    KDerivation (imp (scopedFormula n (.all a) ab).encode
      (scopedFormula m (.all b) bb).encode) ×
    KDerivation (imp (scopedFormula m (.all b) bb).encode
      (scopedFormula n (.all a) ab).encode) := by
  let z := commonName a ab b bb
  let base := z + 1
  have hza : z ∉ (scopedFormula (n+1) a (Fin.snoc ab (universalName a ab))).names := by
    intro h
    have hl : z ≤ (((scopedFormula (n+1) a (Fin.snoc ab (universalName a ab))).names ∪
        (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb))).names).sup id) :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ h)
    dsimp [z, commonName] at hl
    omega
  have hzb : z ∉ (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb))).names := by
    intro h
    have hl : z ≤ (((scopedFormula (n+1) a (Fin.snoc ab (universalName a ab))).names ∪
        (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb))).names).sup id) :=
      Finset.le_sup (f := id) (Finset.mem_union_right _ h)
    dsimp [z, commonName] at hl
    omega
  have ha : universalName a ab < z := by dsimp [z, commonName]; omega
  have hb : universalName b bb < z := by dsimp [z, commonName]; omega
  apply universals_of_common_child a ab b bb base z (by dsimp [base]; omega)
    (by dsimp [base]; omega) (by omega) (by omega)
  · exact universalBodyAt_fresh a ab base z (by dsimp [base]; omega) (by omega) hza
  · exact universalBodyAt_fresh b bb base z (by dsimp [base]; omega) (by omega) hzb
  · exact hforward
  · exact hbackward

end PASoundness.PAtoCompactVacuousUniversalFresh

#print axioms PASoundness.PAtoCompactVacuousUniversalFresh.low_name_not_domain_names
#print axioms PASoundness.PAtoCompactVacuousUniversalFresh.universalBodyAt_fresh
#print axioms PASoundness.PAtoCompactVacuousUniversalFresh.universals_of_common_child_auto
