import PASoundness.PAtoCompactPAAddSuccNecessaryTFrame
import PASoundness.PAtoCompactPAAddSuccNecessaryTProjection
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Extract the first addition-child witness from the actual equality frame of
PA addition-successor. This is a finite K projection, not graph totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccNecessaryTLift
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactPAAddSuccNecessaryTFrame PASoundness.PAtoCompactPAAddSuccNecessaryTProjection

/-- The equality frame for (t+S(u))=S(t+u) entails the existence of the
actual left child's graph at its native witness name and base. -/
noncomputable def frame_to_t_native (t u : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b) :
    KDerivation (imp (equalityFrame id (Peano.add t (Peano.succ u))
      (Peano.succ (Peano.add t u)) b).encode
      (existsCode (b+2) (termGraph id t (b+2) (b+66)).encode)) := by
  let L := Peano.add t (Peano.succ u)
  let R := Peano.succ (Peano.add t u)
  let F := Formula.ex (b+2) (termGraph id t (b+2) (b+66))
  have hL : ∀ a ∈ L.varFinset, id a < b := by
    intro a ha
    have hh : a ∈ t.varFinset ∨ a ∈ u.varFinset := by
      simpa [L, Peano.add, Peano.succ, Term.varFinset] using ha
    rcases hh with hh | hh
    · exact ht a hh
    · exact hu a hh
  have hp := equality_frame_left_graph id L R b hL
  have hc : KDerivation (imp (termGraph id L b (b+2)).encode F.encode) := by
    have h := addition_left_child id t (Peano.succ u) b (b+2)
      (by intro a ha; have hh := ht a ha; simpa using (show a < b+2 by omega))
    simpa [L, F, Formula.encode, Peano.add] using h
  have hfree : b ∉ F.free := by
    intro hb
    have hb' : b ∈ (termGraph id t (b+2) (b+66)).free := by
      simpa [F, Formula.free] using hb
    have hs := termGraph_free_subset id t (b+2) (b+66) hb'
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hs
      have hh := ht a ha
      simp only [id_eq] at he
      omega
    · have he := Finset.mem_singleton.mp hs
      omega
  have helim : KDerivation (imp (existsCode b (termGraph id L b (b+2)).encode) F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (free_vacuity b F hfree) (.closed (.generalize b hc))
      (Context.head [] _)
  simpa [L, R, F, Formula.encode, existsCode] using compose hp helim

theorem frame_to_t_native_certificate (t u : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b) :
    theoremCode (certificate (frame_to_t_native t u b ht hu)) =
      imp (equalityFrame id (Peano.add t (Peano.succ u))
        (Peano.succ (Peano.add t u)) b).encode
        (existsCode (b+2) (termGraph id t (b+2) (b+66)).encode) := certificate_correct _

end PASoundness.PAtoCompactPAAddSuccNecessaryTLift
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryTLift.frame_to_t_native
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryTLift.frame_to_t_native_certificate
