import PASoundness.PAtoCompactMultiplicationCleanMapUnique70
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Conditional K transfer from top-row map-edge recovery to the literal
product-output uniqueness clause. All projections and the recovery proof are
explicit K proof inputs under retained hypothesis H. This does not establish
recovery, construct a product graph, or prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopUniqueConditional
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationCleanMapUnique41
open PASoundness.PAtoCompactMultiplicationCleanMapUnique70
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- An actual triple in graph 64, with fixed major coordinate 30, minor
coordinate 3, and displayed output. -/
def topTriple (v : Nat) : Formula := replace 6 64 (tripleFormula 30 3 v)
/-- The exact uniqueness clause for an output named 5 in result 45. -/
def topUnique : Formula := .all 9 (.imp
  (namedBoth (.member 45 9) (topTriple 9)) (.equal 9 5))
private def point70 : Formula := .imp
  (namedBoth (.member 45 70) (topTriple 70)) (.equal 70 5)

/-- If H yields the displayed clean map, source membership, selected map
edge, and recovery of the map edge of any queried top triple, K derives the
full target-guarded uniqueness clause. H's K vacuity and all projections
are explicit inputs. No graph-recovery proof is assumed implicitly. -/
def unique_from_recovery (H : Formula)
    (hv : KDerivation (imp H.encode (allCode 70 H.encode)))
    (hclean : KDerivation (imp H.encode suffixClean.encode))
    (hmap : KDerivation (imp H.encode mapBijection40.encode))
    (hsrc : KDerivation (imp H.encode (member 31 3)))
    (hchosen : KDerivation (imp H.encode (graphFormula 6 3 5).encode))
    (hrecover : KDerivation (imp H.encode
      (imp (topTriple 70).encode (graphFormula 6 3 70).encode))) :
    KDerivation (imp H.encode topUnique.encode) := by
  let Γ := [H.encode]
  have hh : Context Γ H.encode := .head _ _
  have hp : Context Γ point70.encode := by
    apply Context.deduction
    let Δ := [(namedBoth (.member 45 70) (topTriple 70)).encode,H.encode]
    have hp' : Context Δ (both (member 45 70) (topTriple 70).encode) := by
      have hh' : Context Δ (namedBoth (.member 45 70) (topTriple 70)).encode := .head _ _
      simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hh'
    have ht : Context Δ (topTriple 70).encode := Context.conjunctionRight hp'
    have hH : Context Δ H.encode := .under hh _
    have hc : Context Δ suffixClean.encode := .mp hH (.closed hclean)
    have hb : Context Δ mapBijection40.encode := .mp hH (.closed hmap)
    have hm : Context Δ (member 31 3) := .mp hH (.closed hsrc)
    have he5 : Context Δ (graphFormula 6 3 5).encode := .mp hH (.closed hchosen)
    have he70 : Context Δ (graphFormula 6 3 70).encode := .mp ht (.mp hH (.closed hrecover))
    exact .mp he70 (.mp he5 (.mp hm (.mp hb (.mp hc (.closed clean_unique_70)))))
  have hvΓ : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 70 h)) := by
    intro h hm
    have he : h = H.encode := by simpa [Γ] using hm
    subst h
    exact hv
  have hall := Context.generalize 70 hvΓ hp
  have hα := (universalAlpha 70 9 point70 (by decide) (by decide) (by decide)).1
  have hs : replace 70 9 point70 = .imp
      (namedBoth (.member 45 9) (topTriple 9)) (.equal 9 5) := by decide
  rw [hs] at hα
  have hα' : KDerivation (imp (allCode 70 point70.encode) topUnique.encode) := by
    simpa [topUnique,Formula.encode] using hα
  apply Context.closeEmpty
  apply Context.deduction
  exact .mp hall (.closed hα')

theorem unique_from_recovery_certificate (H : Formula)
    (hv : KDerivation (imp H.encode (allCode 70 H.encode)))
    (hclean : KDerivation (imp H.encode suffixClean.encode))
    (hmap : KDerivation (imp H.encode mapBijection40.encode))
    (hsrc : KDerivation (imp H.encode (member 31 3)))
    (hchosen : KDerivation (imp H.encode (graphFormula 6 3 5).encode))
    (hrecover : KDerivation (imp H.encode
      (imp (topTriple 70).encode (graphFormula 6 3 70).encode))) :
    theoremCode (certificate (unique_from_recovery H hv hclean hmap hsrc hchosen hrecover)) =
      imp H.encode topUnique.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationTopUniqueConditional
#print axioms PASoundness.PAtoCompactMultiplicationTopUniqueConditional.unique_from_recovery
#print axioms PASoundness.PAtoCompactMultiplicationTopUniqueConditional.unique_from_recovery_certificate
