import PASoundness.PAtoCompactProductMatchSourceForwardWitness
import PASoundness.PAtoCompactProductMatchPointUnique
import PASoundness.PAtoCompactScopedActiveReplace

/-! If the two source coordinate pairs agree, their guarded source product
outputs agree. The product matrix and both displayed triples stay explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchSourceOutputUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchPointUnique PASoundness.PAtoCompactProductMatchSourceForwardWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceGuard : Formula := namedBoth productMatrix (namedBoth (.member 0 30) (namedBoth (.member 1 31)
  (namedBoth (.member 2 32) (namedBoth (.member 2 52)
    (namedBoth (tripleFormula 30 31 32) (namedBoth (tripleFormula 50 51 52)
      (namedBoth (.equal 30 50) (.equal 31 51))))))))
def rivalCompetitor : Formula := replace 35 52 forwardCompetitor
def uniqueFrame : Formula := .imp selectedForwardBody (.imp forwardCompetitor (.equal 35 32))
def rivalFrame : Formula := .imp selectedForwardBody (.imp rivalCompetitor (.equal 52 32))

theorem rival_competitor_shape : rivalCompetitor = namedBoth (.member 2 52) (tripleFormula 30 31 52) := by decide
theorem rival_frame_shape : replace 35 52 uniqueFrame = rivalFrame := by decide

def rival_output_unique : KDerivation (imp selectedForwardBody.encode
    (imp rivalCompetitor.encode (equal 52 32))) := by
  have h0 : KDerivation uniqueFrame.encode := by simpa [uniqueFrame, Formula.encode] using forward_output_unique
  have h1 := replace_derivation 35 52 uniqueFrame (by decide) (by decide) h0
  rw [rival_frame_shape] at h1
  simpa [rivalFrame, Formula.encode] using h1

def source_outputs_equal : KDerivation (imp sourceGuard.encode (equal 32 52)) := by
  have he₁ := (equalityReplace 50 30 (tripleFormula 50 51 52) (by decide) (by decide)).1
  have hs₁ : replace 50 30 (tripleFormula 50 51 52) = tripleFormula 30 51 52 := by decide
  rw [hs₁] at he₁
  have he₂ := (equalityReplace 51 31 (tripleFormula 30 51 52) (by decide) (by decide)).1
  have hs₂ : replace 51 31 (tripleFormula 30 51 52) = tripleFormula 30 31 52 := by decide
  rw [hs₂] at he₂
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [sourceGuard.encode]
  have hg : Context Γ sourceGuard.encode := .head _ _
  have hg' : Context Γ (both productMatrix.encode (both (member 0 30) (both (member 1 31)
      (both (member 2 32) (both (member 2 52)
        (both (tripleFormula 30 31 32).encode (both (tripleFormula 50 51 52).encode
          (both (equal 30 50) (equal 31 51))))))))) := by
    simpa [sourceGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hm := Context.conjunctionLeft hg'
  have h₁ := Context.conjunctionRight hg'
  have hx := Context.conjunctionLeft h₁
  have h₂ := Context.conjunctionRight h₁
  have hy := Context.conjunctionLeft h₂
  have h₃ := Context.conjunctionRight h₂
  have hz := Context.conjunctionLeft h₃
  have h₄ := Context.conjunctionRight h₃
  have hw := Context.conjunctionLeft h₄
  have h₅ := Context.conjunctionRight h₄
  have ht := Context.conjunctionLeft h₅
  have h₆ := Context.conjunctionRight h₅
  have hu := Context.conjunctionLeft h₆
  have h₇ := Context.conjunctionRight h₆
  have hxy := Context.conjunctionLeft h₇
  have hzw := Context.conjunctionRight h₇
  have hsel := Context.mp ht (Context.mp hz (Context.mp hy (Context.mp hx
    (Context.mp hm (.closed source_forward_witness)))))
  have hu' := Context.mp hu (Context.mp (Context.eqSymm hxy) (.closed he₁))
  have hu'' := Context.mp hu' (Context.mp (Context.eqSymm hzw) (.closed he₂))
  have hc : Context Γ rivalCompetitor.encode := by
    have h := Context.conjunctionIntro hw hu''
    simpa [rival_competitor_shape, namedBoth, Formula.not, Formula.encode, both, neg] using h
  simpa [Γ] using Context.eqSymm (Context.mp hc (Context.mp hsel (.closed rival_output_unique)))

theorem source_outputs_equal_certificate : theoremCode (certificate source_outputs_equal) =
    imp sourceGuard.encode (equal 32 52) := certificate_correct _

end PASoundness.PAtoCompactProductMatchSourceOutputUnique

#print axioms PASoundness.PAtoCompactProductMatchSourceOutputUnique.rival_output_unique
#print axioms PASoundness.PAtoCompactProductMatchSourceOutputUnique.source_outputs_equal
#print axioms PASoundness.PAtoCompactProductMatchSourceOutputUnique.source_outputs_equal_certificate
