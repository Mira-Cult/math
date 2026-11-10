import PASoundness.PAtoCompactBinaryGraphFunctionalFromPoint
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactFreeVacuity

/-! Discharge the witness-vacuity conditions for a supplied graph-aware
binary point using the same freshness arguments as the existing binary lift. -/
namespace PASoundness.PAtoCompactBinaryGraphFunctionalFromPointFresh

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactBinaryGraphFunctionalFromPoint
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The original point remains an explicit finite K input. -/
noncomputable def binary_functionality_from_point_fresh {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (add : Bool) (b c p q f : Nat) (g : Formula)
    (hbc : b+1 < c) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (point : KDerivation (imp (andF (andF g (andF
      (termGraph v (binaryTerm add t u) p b) (termGraph v (binaryTerm add t u) q c)))
      (matrix v add t u b p)).encode
      (imp (matrix v add t u c q).encode (equivAt f p q).encode))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm add t u) p b).encode
        (imp (termGraph v (binaryTerm add t u) q c).encode (equivAt f p q).encode))) := by
  let A := termGraph v (binaryTerm add t u) p b
  let B := termGraph v (binaryTerm add t u) q c
  let M := matrix v add t u b p
  let H := andF g (andF A B)
  have hvars : ∀ a ∈ (binaryTerm add t u).varFinset, v a < b := by
    intro a ha
    cases add <;> simp only [binaryTerm, Bool.false_eq_true, ↓reduceIte, Term.varFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
    all_goals
      obtain ⟨i, hi⟩ := ha
      fin_cases i
      · exact ht a hi
      · exact hu a hi
  have graph_free (out base z : Nat) (hout : out < b) (hz : b ≤ z) :
      z ∉ (termGraph v (binaryTerm add t u) out base).free := by
    intro h
    have hh := termGraph_free_subset v (binaryTerm add t u) out base h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
    rcases hh with ⟨a, ha, he⟩ | he
    · have hv := hvars a ha; omega
    · omega
  have hH (z : Nat) (hz : b ≤ z) : z ∉ H.free := by
    intro h
    simp only [H, andF_free, Finset.mem_union] at h
    rcases h with h | h | h
    · have := hg z h; omega
    · exact graph_free p b z hp hz h
    · exact graph_free q c z hq hz h
  have hM (z : Nat) (hz : b+1 < z) : z ∉ M.free := by
    intro h
    simp only [M, matrix, andF_free, Finset.mem_union] at h
    rcases h with h | h | h
    · have hh := termGraph_free_subset v t b (b+64) h
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
      rcases hh with ⟨a, ha, he⟩ | he
      · have := ht a ha; omega
      · omega
    · have hh := termGraph_free_subset v u (b+1) (b+64+termCost t) h
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
      rcases hh with ⟨a, ha, he⟩ | he
      · have := hu a ha; omega
      · omega
    · cases add with
      | false =>
          have hh := mulAt_free b b (b+1) p (by simpa [binaryRel] using h)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hh
          omega
      | true =>
          have hh := addAt_free b b (b+1) p (by simpa [binaryRel] using h)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hh
          omega
  have hHM (z : Nat) (hz : b+1 < z) : z ∉ (andF H M).free := by
    simp only [andF_free, Finset.mem_union, not_or]
    exact ⟨hH z (by omega), hM z hz⟩
  have hE (z : Nat) (hz : b ≤ z) : z ∉ (equivAt f p q).free := by
    intro h
    have hh := equivAt_free f p q h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  exact binary_functionality_from_point v t u add b c p q f g point
    (free_vacuity b H (hH b (by omega)))
    (free_vacuity (b+1) H (hH (b+1) (by omega)))
    (free_vacuity c (andF H M) (hHM c (by omega)))
    (free_vacuity (c+1) (andF H M) (hHM (c+1) (by omega)))
    (free_vacuity b _ (hE b (by omega)))
    (free_vacuity (b+1) _ (hE (b+1) (by omega)))
    (free_vacuity c _ (hE c (by omega)))
    (free_vacuity (c+1) _ (hE (c+1) (by omega)))

end PASoundness.PAtoCompactBinaryGraphFunctionalFromPointFresh

#print axioms PASoundness.PAtoCompactBinaryGraphFunctionalFromPointFresh.binary_functionality_from_point_fresh
