import PASoundness.PAtoCompactGuardedArbitraryTermFrames
import PASoundness.PAtoCompactVariableTermTotality

/-! Capture-safe witness introduction for an arithmetic equality frame. Given
an explicit equality matrix at two names below a fresh allocation base, it
constructs a finite K derivation of the equality frame. It does not construct
term graphs, quotient equality, or successor cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInjectivityFrameWitnessIntro
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactTermGraphBinderRange
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

/-- Introduce both equality value witnesses. The witness names may coincide
with each other or source variable names; each is strictly below the fresh
frame base. Source-variable names are also strictly below that base. -/
def frame_from_matrix (t u : Peano.Term) (b a c : Nat)
    (ha : a < b) (hc : c < b)
    (ht : ∀ x ∈ t.varFinset, x < b) (hu : ∀ x ∈ u.varFinset, x < b) :
    let M := matrix id t u a c (b+2) (b+2+termCost t) (b+2+termCost t+termCost u)
    KDerivation (imp M.encode (equalityFrame id t u b).encode) := by
  dsimp only
  let M := matrix id t u b (b+1) (b+2) (b+2+termCost t) (b+2+termCost t+termCost u)
  have hB : b ∉ M.binders := matrix_below_not_binder id t u b (b+1)
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost u) b (by omega) (by omega) (by omega)
  have hB1 : b+1 ∉ M.binders := matrix_below_not_binder id t u b (b+1)
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost u) (b+1) (by omega) (by omega) (by omega)
  have haM : a ∉ M.binders := matrix_below_not_binder id t u b (b+1)
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost u) a (by omega) (by omega) (by omega)
  have hcM : c ∉ M.binders := matrix_below_not_binder id t u b (b+1)
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost u) c (by omega) (by omega) (by omega)
  have hinner := exists_from_instance (b+1) c (replace b a M) (by omega)
    (by simpa [replace_binders] using hB1) (by simpa [replace_binders] using hcM)
  have houter := exists_from_instance b a (.ex (b+1) M) (by omega)
    (by simp [Formula.binders, hB]) (by simp [Formula.binders, haM, show a ≠ b+1 by omega])
  have hreplace := matrix_replace_two_witnesses id t u b (b+1) a c
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost u)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro x hx; simp only [id_eq]; have := ht x hx; omega)
    (by intro x hx; simp only [id_eq]; have := hu x hx; omega)
    (by intro x hx; simp only [id_eq]; have := ht x hx; omega)
    (by intro x hx; simp only [id_eq]; have := hu x hx; omega)
    (by omega) (by omega)
  have houter' : KDerivation (imp (existsCode (b+1) (replace b a M).encode)
      (equalityFrame id t u b).encode) := by
    simpa only [equalityFrame, Formula.encode, replace, if_neg (show b ≠ b+1 by omega), M, matrix] using houter
  rw [hreplace] at hinner
  exact compose hinner houter'


theorem frame_from_matrix_certificate (t u : Peano.Term) (b a c : Nat)
    (ha : a < b) (hc : c < b)
    (ht : ∀ x ∈ t.varFinset, x < b) (hu : ∀ x ∈ u.varFinset, x < b) :
    let M := matrix id t u a c (b+2) (b+2+termCost t) (b+2+termCost t+termCost u)
    theoremCode (certificate (frame_from_matrix t u b a c ha hc ht hu)) =
      imp M.encode (equalityFrame id t u b).encode := certificate_correct _

end PASoundness.PAtoCompactInjectivityFrameWitnessIntro

#print axioms PASoundness.PAtoCompactInjectivityFrameWitnessIntro.frame_from_matrix
#print axioms PASoundness.PAtoCompactInjectivityFrameWitnessIntro.frame_from_matrix_certificate
