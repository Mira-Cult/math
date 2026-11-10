import PASoundness.PAtoCompactProductOutputActualPoint
import PASoundness.PAtoCompactProductOutputImageRelation
import PASoundness.PAtoCompactScopedActiveReplace

/-! Pointwise uniqueness of two target outputs at the same factor pair for a
supplied guarded output graph. Both graph triples and endpoint memberships
remain explicit; no graph or product-matrix existence is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputForwardUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputImageRelation
open PASoundness.PAtoCompactProductOutputActualPoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalPoint : Formula := replace 33 51 selectedPoint
def rivalPath : Formula := replace 33 51 actualPath
def rivalGuard : Formula := replace 33 51 selectedGuard
def rivalTriple : Formula := tripleAt 58 30 31 51
def forwardGuard : Formula := namedBoth actualInvariant (namedBoth (.member 43 30)
  (namedBoth (.member 44 31) (namedBoth (.member 42 33) (namedBoth (.member 42 51)
    (namedBoth selectedTriple rivalTriple)))))

theorem rival_point_shape : rivalPoint = .imp rivalGuard
    (namedBoth (.imp rivalTriple rivalPath) (.imp rivalPath rivalTriple)) := by decide
theorem rival_guard_shape : rivalGuard = namedBoth (.member 43 30)
    (namedBoth (.member 44 31) (.member 42 51)) := by decide

def rival_instance : KDerivation (imp actualInvariant.encode rivalPoint.encode) := by
  let F : Formula := .imp actualInvariant selectedPoint
  have h0 : KDerivation F.encode := by simpa [F, CompactNamed.Formula.encode] using actual_instance
  have h1 := replace_derivation 33 51 F (by decide) (by decide) h0
  have hs : replace 33 51 F = .imp actualInvariant rivalPoint := by decide
  rw [hs] at h1
  simpa [CompactNamed.Formula.encode] using h1

def actual_path_to_image : KDerivation (imp actualPath.encode imagePath.encode) := by
  have hp : KDerivation (imp actualBody.encode pairedBody.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [actualBody.encode]
    have hb : Context Γ actualBody.encode := .head _ _
    have hb' : Context Γ (both (member 0 32) pairedBody.encode) := by
      simpa [actualBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hb
    exact Context.conjunctionRight hb'
  simpa [actualPath, imagePath, CompactNamed.Formula.encode] using existsCongr 32 hp

def rival_path_to_image : KDerivation (imp rivalPath.encode rivalInput.encode) := by
  let F : Formula := .imp actualPath imagePath
  have h0 : KDerivation F.encode := by simpa [F, CompactNamed.Formula.encode] using actual_path_to_image
  have h1 := replace_derivation 33 51 F (by decide) (by decide) h0
  have hs : replace 33 51 F = .imp rivalPath rivalInput := by decide
  rw [hs] at h1
  simpa only [CompactNamed.Formula.encode] using h1

/-- The queried rival target 51 equals the selected target 33. -/
def forward_unique : KDerivation (imp forwardGuard.encode (equal 51 33)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [forwardGuard.encode]
  have hg : Context Γ forwardGuard.encode := .head _ _
  have hg' : Context Γ (both actualInvariant.encode (both (member 43 30)
      (both (member 44 31) (both (member 42 33) (both (member 42 51)
        (both selectedTriple.encode rivalTriple.encode)))))) := by
    simpa [forwardGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hi := Context.conjunctionLeft hg'
  have hx := Context.conjunctionLeft (Context.conjunctionRight hg')
  have hy := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have ht := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have ht' := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))
  have hedge := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))))
  have hedge' := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))))
  have hguard : Context Γ selectedGuard.encode := by
    simpa [selectedGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx (Context.conjunctionIntro hy ht)
  have hguard' : Context Γ rivalGuard.encode := by
    simpa [rival_guard_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx (Context.conjunctionIntro hy ht')
  have hs := Context.mp hguard (Context.mp hi (.closed actual_instance))
  have hs' : Context Γ (both (imp selectedTriple.encode actualPath.encode)
      (imp actualPath.encode selectedTriple.encode)) := by
    simpa [selectedPoint, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hs
  have hr0 : Context Γ rivalPoint.encode := .mp hi (.closed rival_instance)
  rw [rival_point_shape] at hr0
  have hr : Context Γ (namedBoth (.imp rivalTriple rivalPath) (.imp rivalPath rivalTriple)).encode :=
    .mp hguard' hr0
  have hr' : Context Γ (both (imp rivalTriple.encode rivalPath.encode)
      (imp rivalPath.encode rivalTriple.encode)) := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hr
  have hp := Context.mp hedge (Context.conjunctionLeft hs')
  have hp' := Context.mp hedge' (Context.conjunctionLeft hr')
  have himage := Context.mp hp (.closed actual_path_to_image)
  have himage' := Context.mp hp' (.closed rival_path_to_image)
  exact .mp himage' (.mp himage (.closed image_path_unique))

theorem forward_unique_certificate : theoremCode (certificate forward_unique) =
    imp forwardGuard.encode (equal 51 33) := certificate_correct _

end PASoundness.PAtoCompactProductOutputForwardUnique

#print axioms PASoundness.PAtoCompactProductOutputForwardUnique.rival_instance
#print axioms PASoundness.PAtoCompactProductOutputForwardUnique.actual_path_to_image
#print axioms PASoundness.PAtoCompactProductOutputForwardUnique.rival_path_to_image
#print axioms PASoundness.PAtoCompactProductOutputForwardUnique.forward_unique
#print axioms PASoundness.PAtoCompactProductOutputForwardUnique.forward_unique_certificate
