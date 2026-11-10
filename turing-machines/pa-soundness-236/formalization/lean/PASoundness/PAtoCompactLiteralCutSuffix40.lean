import PASoundness.PAtoCompactLiteralCutOriginalAllocated
import PASoundness.PAtoCompactFilterInstantiation

/-! Capture-safe extraction of the literal cut and suffix witness used by the
multiplication successor graph. This transports a supplied K relation; it
does not establish a product matrix or multiplication totality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutSuffix40
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutAdditionDefinition PASoundness.PAtoCompactLiteralCutOriginalAllocated
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactFilteredSubset
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- One suffix at 40, retaining its literal cut and isomorphism facts. -/
def rawBody : Formula := namedBoth (namedEither (.equal 32 45) (.member 45 32))
  (namedBoth (.all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not))
    (PAtoCompactOrdinalAddition.equivAt 31 40))

/-- The exact compact code retains the cut alternative, filter graph, and
suffix equivalence on the same named witness. -/
theorem rawBody_code : rawBody.encode =
    both (either (equal 32 45) (member 45 32))
      (both (filterGraph 45 40 35 (neg (member 32 35)))
        (PAtoCompactOrdinalAddition.equivAt 31 40).encode) := by rfl

private def statement : Formula := .imp (literalCutAt 100 30 31 32) literalCut
private def moved1 : Formula := replace 32 45 statement
private def moved2 : Formula := replace 30 32 moved1
private def body34 : Formula := namedBoth (namedEither (.equal 32 45) (.member 45 32))
  (namedBoth (.all 35 (namedFilterBody 45 34 35 (Formula.member 32 35).not))
    (PAtoCompactOrdinalAddition.equivAt 31 34))

/-- An allocated literal-cut relation supplies one suffix with all three
stated properties. Output 45 and the first input/cut 32 remain distinct
syntactic labels; no distinctness of their denoted objects is assumed. -/
def literal_cut_suffix40 : KDerivation
    (imp (literalCutAt 100 32 31 45).encode (existsCode 40 rawBody.encode)) := by
  have h0 : KDerivation statement.encode := by
    exact (original_allocated_alpha 100 (by decide)).backward
  have h1 := KDerivation.mp (.generalize 32 h0)
    (universalInstance 32 45 statement (by decide) (by decide) (by decide))
  have h2 := KDerivation.mp (.generalize 30 h1)
    (universalInstance 30 32 moved1 (by decide) (by decide) (by decide))
  have hshape : moved2 = .imp (literalCutAt 100 32 31 45) (.ex 34 body34) := by decide
  change KDerivation moved2.encode at h2
  rw [hshape] at h2
  have ha := (existentialAlpha 34 40 body34 (by decide) (by decide) (by decide)).1
  have halpha : replace 34 40 body34 = rawBody := by decide
  rw [halpha] at ha
  exact compose h2 ha

theorem literal_cut_suffix40_certificate : theoremCode (certificate literal_cut_suffix40) =
    imp (literalCutAt 100 32 31 45).encode (existsCode 40 rawBody.encode) := certificate_correct _
end PASoundness.PAtoCompactLiteralCutSuffix40
#print axioms PASoundness.PAtoCompactLiteralCutSuffix40.rawBody
#print axioms PASoundness.PAtoCompactLiteralCutSuffix40.rawBody_code
#print axioms PASoundness.PAtoCompactLiteralCutSuffix40.literal_cut_suffix40
#print axioms PASoundness.PAtoCompactLiteralCutSuffix40.literal_cut_suffix40_certificate
