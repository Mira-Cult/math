import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.CompactQuantifiers

/-! Introduce a translated equality frame using a supplied left value and
the unmodified right witness. All terms are arbitrary PA terms. -/
namespace PASoundness.PAtoCompactGeneralAtomFrameIntro

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactVariableTermTotality

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- From the concrete equality matrix introduce both value witnesses, using
`q` for the left value. Both terms' names and `q` lie below the frame base;
no distinctness of source names or represented values is required. -/
def target_frame_from_matrix (t s : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hs : ∀ a ∈ s.varFinset, a < b) :
    KDerivation (imp (matrix id t s q (b+1) (b+2)
      (b+2+termCost t) (b+2+termCost t+termCost s)).encode
      (equalityFrame id t s b).encode) := by
  let p := b+2
  let r := b+2+termCost t
  let e := b+2+termCost t+termCost s
  let N := matrix id t s b (b+1) p r e
  let M := matrix id t s q (b+1) p r e
  have hNb : b ∉ N.binders := matrix_below_not_binder id t s b (b+1) p r e b
    (by dsimp [p]; omega) (by dsimp [r]; omega) (by dsimp [e]; omega)
  have hNq : q ∉ N.binders := matrix_below_not_binder id t s b (b+1) p r e q
    (by dsimp [p]; omega) (by dsimp [r]; omega) (by dsimp [e]; omega)
  have hMb : b+1 ∉ M.binders := matrix_below_not_binder id t s q (b+1) p r e (b+1)
    (by dsimp [p]; omega) (by dsimp [r]; omega) (by dsimp [e]; omega)
  have hrepl : replace b q N = M := by
    dsimp [N, M]
    rw [matrix_replace_fresh_source id t s b (b+1) p r e b q
      (by dsimp [p]; omega) (by dsimp [r]; omega) (by dsimp [e]; omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
      (by intro a ha; have := hs a ha; simp only [id_eq]; omega)]
    simp [rename]
  have hi := existsIntroduce (b+1) M hMb
  have ho := exists_from_instance b q (.ex (b+1) N) (by omega)
    (by simpa [Formula.binders] using hNb)
    (by simpa [Formula.binders, show q ≠ b+1 by omega] using hNq)
  have ho' : KDerivation (imp (existsCode (b+1) M.encode)
      (equalityFrame id t s b).encode) := by
    change KDerivation (imp (existsCode (b+1) (replace b q N).encode)
      (equalityFrame id t s b).encode) at ho
    rw [hrepl] at ho
    exact ho
  exact compose hi ho'

theorem target_frame_from_matrix_certificate (t s : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hs : ∀ a ∈ s.varFinset, a < b) :
    theoremCode (certificate (target_frame_from_matrix t s q b hq ht hs)) =
      imp (matrix id t s q (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost s)).encode (equalityFrame id t s b).encode :=
  certificate_correct _

end PASoundness.PAtoCompactGeneralAtomFrameIntro

#print axioms PASoundness.PAtoCompactGeneralAtomFrameIntro.target_frame_from_matrix
#print axioms PASoundness.PAtoCompactGeneralAtomFrameIntro.target_frame_from_matrix_certificate
