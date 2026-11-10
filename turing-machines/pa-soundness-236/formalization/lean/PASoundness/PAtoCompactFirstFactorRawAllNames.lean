import PASoundness.PAtoCompactFirstFactorHighInputFrame
import PASoundness.PAtoCompactFirstFactorFrameFinalize

/-! A first-factor successor shared-output frame at arbitrary bounded input
labels. The source uses a freshly chosen raw-successor test binder; the
quotient-successor and guarded PA axiom wrappers are separate obligations. -/
namespace PASoundness.PAtoCompactFirstFactorRawAllNames

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFirstFactorRenameSyntax PASoundness.PAtoCompactFirstFactorHighInputFrame
open PASoundness.PAtoCompactFirstFactorFrameFinalize

set_option maxRecDepth 262144
set_option maxHeartbeats 0

/-- A single test name strictly above the four inputs and desired output.
This is a syntactic binder name, not a numeric bound on their values. -/
def freshTest (x y p s out : Nat) : Nat :=
  max 208 (max x (max y (max p (max s out)))) + 1

/-- The raw successor test does not bind either of its two operand labels. -/
theorem freshTest_avoids_successor (x y p s out : Nat) :
    x ≠ freshTest x y p s out ∧ s ≠ freshTest x y p s out := by
  unfold freshTest
  omega

/-- Construct a finite K proof of the shared-output frame at arbitrary
bounded labels. The input labels x,y,p,s may coincide. The bound output name
must differ from the inputs occurring in its four-part body (p,y,s), while
all represented values may coincide. The raw successor antecedent uses the
fresh test name above; it is not a quotient-successor or PA axiom theorem. -/
noncomputable def raw_frame (b x y p s out : Nat)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hs : s < b+2) (ho : out < b+2)
    (hop : out ≠ p) (hoy : out ≠ y) (hos : out ≠ s) :
    KDerivation (assignedFrame b out (freshTest x y p s out) x y p s).encode := by
  let r := freshTest x y p s out
  let high := max b r + 300
  have hr : 208 < r := by dsimp [r, freshTest]; omega
  have hxr : x < r := by dsimp [r, freshTest]; omega
  have hyr : y < r := by dsimp [r, freshTest]; omega
  have hpr : p < r := by dsimp [r, freshTest]; omega
  have hsr : s < r := by dsimp [r, freshTest]; omega
  have hor : out < r := by dsimp [r, freshTest]; omega
  have hh : 205 < high := by dsimp [high]; omega
  have hrh : r < high := by dsimp [high]; omega
  have hhigh : KDerivation (assignedFrame high r r x y p s).encode :=
    high_frame high r r x y p s hh hr hrh (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  have hfinal := finalize high b r out r x y p s hrh (by omega)
    (by omega) (by omega) (by omega) hop hoy hos
    (by omega) (by omega) (by omega) (by omega)
    hx hy hp hs ho hhigh
  simpa [r] using hfinal

theorem raw_frame_certificate (b x y p s out : Nat)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hs : s < b+2) (ho : out < b+2)
    (hop : out ≠ p) (hoy : out ≠ y) (hos : out ≠ s) :
    theoremCode (certificate (raw_frame b x y p s out hx hy hp hs ho hop hoy hos)) =
      (assignedFrame b out (freshTest x y p s out) x y p s).encode := certificate_correct _

end PASoundness.PAtoCompactFirstFactorRawAllNames

#print axioms PASoundness.PAtoCompactFirstFactorRawAllNames.freshTest
#print axioms PASoundness.PAtoCompactFirstFactorRawAllNames.freshTest_avoids_successor
#print axioms PASoundness.PAtoCompactFirstFactorRawAllNames.raw_frame
#print axioms PASoundness.PAtoCompactFirstFactorRawAllNames.raw_frame_certificate
