import PASoundness.PAtoCompactAllElimTermEquality

/-! Conditional existential-frame lifting for reverse atomic substitution.
The retained guard and term graph are explicit; the pointwise finite K proof
of the matrix-to-frame implication remains an input. No graph functionality,
formula substitution theorem, or semantic soundness is assumed. -/
namespace PASoundness.PAtoCompactReverseTermAtomFrame

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAllElimTermEquality

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Lift a reverse equality-matrix derivation through both existential value
witnesses while retaining a named guard and an external graph. The pointwise
input is an actual K derivation and includes the guard and graph separately.
Only the guard's free names, the substituting term's variables and the graph
output need lie below b; no assumptions on the unchanged right term are used. -/
noncomputable def frame_of_pointwise (guard : Formula) (t s : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hg : ∀ a ∈ guard.free, a < b)
    (pointwise : KDerivation (imp guard.encode
      (imp (termGraph id t q (b+2)).encode
        (imp (matrix id t s b (b+1) (b+2) (b+2+termCost t)
          (b+2+termCost t+termCost s)).encode
          (equalityFrame id (.var q) s b).encode)))) :
    KDerivation (imp guard.encode (imp (termGraph id t q (b+2)).encode
      (imp (equalityFrame id t s b).encode (equalityFrame id (.var q) s b).encode))) := by
  let G := termGraph id t q (b+2)
  let K := andF guard G
  let S := equalityFrame id t s b
  let T := equalityFrame id (.var q) s b
  let M := matrix id t s b (b+1) (b+2) (b+2+termCost t)
    (b+2+termCost t+termCost s)
  have kg (a : Nat) (ha : b ≤ a) : a ∉ K.free := by
    intro h
    have hu : a ∈ guard.free ∪ G.free := by simpa [K, andF_free] using h
    rcases Finset.mem_union.mp hu with hguard | hgraph
    · have := hg a hguard
      omega
    · have hh := termGraph_free_subset id t q (b+2) hgraph
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
      rcases hh with ⟨v, hv, hv'⟩ | he
      · have := ht v hv
        simp only [id_eq] at hv'
        omega
      · omega
  have tf0 : b ∉ T.free := by simp [T, equalityFrame, Formula.free]
  have tf1 : b+1 ∉ T.free := by simp [T, equalityFrame, Formula.free]
  have vK0 := free_vacuity b K (kg b (by omega))
  have vK1 := free_vacuity (b+1) K (kg (b+1) (by omega))
  have vT0 := free_vacuity b T tf0
  have vT1 := free_vacuity (b+1) T tf1
  have hp : KDerivation (imp K.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode,K.encode]
    have hK : Context Γ K.encode := .hypothesis (by simp [Γ])
    have hM : Context Γ M.encode := Context.head _ _
    have hK' : Context Γ (both guard.encode G.encode) := by
      simpa [K, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hK
    exact .mp hM (.mp (Context.conjunctionRight hK')
      (.mp (Context.conjunctionLeft hK') (.closed pointwise)))
  have hlift := two_exists_left_guarded b (b+1) K.encode M.encode T.encode vK0 vK1 vT0 vT1 hp
  have hlift' : KDerivation (imp K.encode (imp S.encode T.encode)) := by
    simpa [S, M, equalityFrame, matrix, CompactNamed.Formula.encode] using hlift
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [S.encode,G.encode,guard.encode]
  have hs : Context Γ S.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ G.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have hK : Context Γ K.encode := by
    have h := Context.conjunctionIntro hg' hG
    simpa [K, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
  exact .mp hs (.mp hK (.closed hlift'))

theorem frame_of_pointwise_certificate (guard : Formula) (t s : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hg : ∀ a ∈ guard.free, a < b)
    (pointwise : KDerivation (imp guard.encode
      (imp (termGraph id t q (b+2)).encode
        (imp (matrix id t s b (b+1) (b+2) (b+2+termCost t)
          (b+2+termCost t+termCost s)).encode
          (equalityFrame id (.var q) s b).encode)))) :
    theoremCode (certificate (frame_of_pointwise guard t s q b hq ht hg pointwise)) =
      imp guard.encode (imp (termGraph id t q (b+2)).encode
        (imp (equalityFrame id t s b).encode (equalityFrame id (.var q) s b).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactReverseTermAtomFrame

#print axioms PASoundness.PAtoCompactReverseTermAtomFrame.frame_of_pointwise
#print axioms PASoundness.PAtoCompactReverseTermAtomFrame.frame_of_pointwise_certificate
