import PASoundness.PAtoCompactSeededSpanPointOrder
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactFreeVacuity

/-! Derive the seed-edge endpoint conditions from a supplied clean seed graph.
The second source point is 26, which is also an internal binder of the clean
graph predicate. We first prove its endpoint rule at fresh label 28 under the
fixed clean-graph context, generalize 28 there, then instantiate only the point
formula at 26. This avoids capture of the clean predicate's bound name. -/
namespace PASoundness.PAtoCompactSeededSpanCleanEndpoints

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSeededSpanPointOrder
open PASoundness.PAtoCompactSeededSpanOrderCases

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def seedClean : Formula := .all 19 (.imp (.member 14 19) (edgePredicate 19 40 41))
private def originalClean : Formula := PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.suffixClean
private def pairFormulaAt (u v : Nat) : Formula := namedBoth (.member 31 u) (.member 40 v)
private def frame (u v : Nat) : Formula := .imp originalClean
  (.imp (graphFormula 6 u v) (pairFormulaAt u v))
private def at45 (u v : Nat) : Formula := replace 31 45 (frame u v)
private def at41 (u v : Nat) : Formula := replace 40 41 (at45 u v)
private def at40 (u v : Nat) : Formula := replace 45 40 (at41 u v)
private def point (u v : Nat) : Formula := .imp (graphFormula 14 u v)
  (namedBoth (.member 40 u) (.member 41 v))

private def endpoints23 : KDerivation (imp seedClean.encode (point 2 3).encode) := by
  have hbase : KDerivation (frame 2 3).encode := by
    simpa only [frame,originalClean,pairFormulaAt,Formula.encode,namedBoth,CompactProof.both,CompactProof.neg] using
      PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.clean_endpoints 2 3 (by decide)
  have h45 := replace_derivation 31 45 (frame 2 3) (by decide) (by decide) hbase
  have h41 := replace_derivation 40 41 (at45 2 3) (by decide) (by decide) (by simpa only [at45] using h45)
  have h40 := replace_derivation 45 40 (at41 2 3) (by decide) (by decide) (by simpa only [at41] using h41)
  have h14 := replace_derivation 6 14 (at40 2 3) (by decide) (by decide) (by simpa only [at40] using h40)
  have ha : replace 6 14 (at40 2 3) = .imp seedClean (point 2 3) := by decide
  rw [ha] at h14
  exact h14

private def endpoints2827 : KDerivation (imp seedClean.encode (point 28 27).encode) := by
  have hbase : KDerivation (frame 28 27).encode := by
    simpa only [frame,originalClean,pairFormulaAt,Formula.encode,namedBoth,CompactProof.both,CompactProof.neg] using
      PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.clean_endpoints 28 27 (by decide)
  have h45 := replace_derivation 31 45 (frame 28 27) (by decide) (by decide) hbase
  have h41 := replace_derivation 40 41 (at45 28 27) (by decide) (by decide) (by simpa only [at45] using h45)
  have h40 := replace_derivation 45 40 (at41 28 27) (by decide) (by decide) (by simpa only [at41] using h41)
  have h14 := replace_derivation 6 14 (at40 28 27) (by decide) (by decide) (by simpa only [at40] using h40)
  have ha : replace 6 14 (at40 28 27) = .imp seedClean (point 28 27) := by decide
  rw [ha] at h14
  exact h14

/-- Stored-pair cleanliness supplies conditional cut membership for both
actual seed edges, including the source point whose label is 26. -/
def seed_endpoints_from_clean : KDerivation (imp seedClean.encode seedEndpoints) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [seedClean.encode]
  have hc : Context Γ seedClean.encode := .head _ _
  have hfirst : Context Γ (imp firstSeed (both (member 40 2) (member 41 3))) := by
    have hp : Context Γ (point 2 3).encode := .mp hc (.closed endpoints23)
    exact hp
  have h28 : Context Γ (point 28 27).encode := .mp hc (.closed endpoints2827)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 28 h)) := by
    intro h hh
    have he : h = seedClean.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 28 seedClean (by decide)
  have hall : Context Γ (allCode 28 (point 28 27).encode) := Context.generalize 28 hv h28
  have hi := universalInstance 28 26 (point 28 27) (by decide) (by decide) (by decide)
  have ha : replace 28 26 (point 28 27) = point 26 27 := by decide
  rw [ha] at hi
  have hsecond : Context Γ (imp secondSeed (both (member 40 26) (member 41 27))) := by
    have hp : Context Γ (point 26 27).encode := .mp hall (.closed hi)
    exact hp
  exact Context.conjunctionIntro hfirst hsecond

theorem seed_endpoints_from_clean_certificate : theoremCode (certificate seed_endpoints_from_clean) =
    imp seedClean.encode seedEndpoints := certificate_correct seed_endpoints_from_clean

end PASoundness.PAtoCompactSeededSpanCleanEndpoints

#print axioms PASoundness.PAtoCompactSeededSpanCleanEndpoints.seedClean
#print axioms PASoundness.PAtoCompactSeededSpanCleanEndpoints.seed_endpoints_from_clean
#print axioms PASoundness.PAtoCompactSeededSpanCleanEndpoints.seed_endpoints_from_clean_certificate
