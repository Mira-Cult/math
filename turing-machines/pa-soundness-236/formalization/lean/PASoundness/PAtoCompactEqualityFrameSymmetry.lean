import PASoundness.PAtoCompactEqualityMatrixSymmetry
import PASoundness.PAtoCompactEqualitySwapWitnesses

/-! Finite K symmetry of translated PA equalities. The proof swaps two value
witnesses; it requires neither graph functionality nor graph existence. -/
namespace PASoundness.PAtoCompactEqualityFrameSymmetry

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactEqualityMatrixSymmetry PASoundness.PAtoCompactEqualitySwapWitnesses
open PASoundness.PAtoCompactExistsCommute PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactEquivMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Equality-frame symmetry for a common allocation base above all source
term names. The two represented values can coincide. -/
noncomputable def frame_symmetry (t u : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b) :
    KDerivation (imp (equalityFrame id t u b).encode (equalityFrame id u t b).encode) := by
  let p := b+3
  let q := b+3+termCost u
  let r := b+3+termCost u+termCost t
  let p0 := b+2
  let q0 := b+2+termCost t
  let r0 := b+2+termCost t+termCost u
  have hm := matrix_swap id t u b (b+1) p0 q0 r0 p q r
    (by dsimp [p0]; omega) (by dsimp [q]; omega)
    (by dsimp [q0]; omega) (by dsimp [p]; omega)
    (by dsimp [r0]; omega) (by dsimp [r0]; omega)
    (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by intro a ha; simp only [id_eq]; have := ht a ha; dsimp [p0]; omega)
    (by intro a ha; simp only [id_eq]; have := ht a ha; dsimp [q]; omega)
    (by intro a ha; simp only [id_eq]; have := hu a ha; dsimp [q0]; omega)
    (by intro a ha; simp only [id_eq]; have := hu a ha; dsimp [p]; omega)
  have hs1 := existsCongr b (existsCongr (b+1) hm)
  have hs2 := exists_commute b (b+1) (matrix id u t (b+1) b p q r).encode
  have hs3 := (swap_matrix_witnesses id u t b p q r
    (by dsimp [p]; omega) (by dsimp [q]; omega) (by dsimp [r]; omega)
    (by intro a ha; simpa only [id_eq] using hu a ha)
    (by intro a ha; simpa only [id_eq] using ht a ha)).forward
  let p1 := b+2
  let q1 := b+2+termCost u
  let r1 := b+2+termCost u+termCost t
  have hU := (termGraph_base_transport id u p p1 b
    (by dsimp [p]; omega) (by dsimp [p1]; omega)
    (by intro a ha; simp only [id_eq]; have := hu a ha; dsimp [p]; omega)
    (by intro a ha; simp only [id_eq]; have := hu a ha; dsimp [p1]; omega)).1
  have hT := (termGraph_base_transport id t q q1 (b+1)
    (by dsimp [q]; omega) (by dsimp [q1]; omega)
    (by intro a ha; simp only [id_eq]; have := ht a ha; dsimp [q]; omega)
    (by intro a ha; simp only [id_eq]; have := ht a ha; dsimp [q1]; omega)).1
  have hE := (equivAt_base_alpha r r1 b (b+1)
    (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by dsimp [r1]; omega) (by dsimp [r1]; omega)).forward
  have hs4 := frame_private_forward id u t b (b+1) p q r p1 q1 r1 hU hT hE
  have h := compose hs1 (compose hs2 (compose hs3 hs4))
  simpa [equalityFrame, matrix, p0, q0, r0, p1, q1, r1, Formula.encode] using h

theorem scopeBase_equal_swapped (t u : Peano.Term) :
    scopeBase (t.equal u) Fin.elim0 = scopeBase (u.equal t) Fin.elim0 := by
  simp [scopeBase, eq_free, Finset.union_comm]

/-- The translation of any PA equality implies the translation with its
terms exchanged, by explicit finite K proof construction. -/
noncomputable def code_symmetry (t u : Peano.Term) :
    KDerivation (imp (code (t.equal u)) (code (u.equal t))) := by
  let b := scopeBase (t.equal u) Fin.elim0
  have ht : ∀ a ∈ t.varFinset, a < b := by
    intro a ha
    exact names_lt_original_base t u a (Finset.mem_union_left _ ha)
  have hu : ∀ a ∈ u.varFinset, a < b := by
    intro a ha
    exact names_lt_original_base t u a (Finset.mem_union_right _ ha)
  have h := frame_symmetry t u b ht hu
  simpa [code, original_shape, ← scopeBase_equal_swapped t u, b] using h

theorem code_symmetry_certificate (t u : Peano.Term) :
    theoremCode (certificate (code_symmetry t u)) = imp (code (t.equal u)) (code (u.equal t)) :=
  certificate_correct _

#print axioms frame_symmetry
#print axioms scopeBase_equal_swapped
#print axioms code_symmetry
#print axioms code_symmetry_certificate
end PASoundness.PAtoCompactEqualityFrameSymmetry
