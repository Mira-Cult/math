import PASoundness.PAtoCompactProductMatchSourceWitness
import PASoundness.PAtoCompactProductMatchPointUnique
import PASoundness.PAtoCompactScopedActiveReplace

/-! Pointwise uniqueness of two complete source-to-target product matches.
Both paths retain the same supplied product and factor-bijection graph labels.
No represented graph of matches or reverse-totality theorem is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPathUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchPointUnique
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchBothImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchTargetWitness
open PASoundness.PAtoCompactProductMatchSourceWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalReverse : Formula := replace 31 51 (replace 30 50 selectedReverseBody)
def rivalFirst : Formula := replace 33 53 (replace 30 50 firstImage)
def rivalSecond : Formula := replace 34 54 (replace 31 51 secondImage)
def rivalTarget : Formula := replace 35 55 (replace 34 54 (replace 33 53 targetOutputBody))
def rivalMatchBody : Formula := namedBoth rivalReverse
  (namedBoth (namedBoth rivalFirst rivalSecond) rivalTarget)

def rivalReverseCompetitor : Formula := namedBoth (.member 0 50)
  (namedBoth (.member 1 51) (tripleFormula 50 51 32))

theorem rival_reverse_shape : rivalReverse = namedBoth (.member 0 50)
    (namedBoth (.member 1 51) (namedBoth (tripleFormula 50 51 32)
      (.all 7 (.all 8 (replace 31 51 (replace 30 50 reverseUnique)))))) := by decide

theorem rival_first_shape : rivalFirst = namedBoth (.member 42 53)
    (namedBoth (graphFormula 40 50 53) (.all 4
      (.imp (namedBoth (.member 42 4) (graphFormula 40 50 4)) (.equal 4 53)))) := by decide

theorem rival_second_shape : rivalSecond = namedBoth (.member 43 54)
    (namedBoth (graphFormula 41 51 54) (.all 4
      (.imp (namedBoth (.member 43 4) (graphFormula 41 51 4)) (.equal 4 54)))) := by decide

theorem rival_target_shape : rivalTarget = namedBoth (.member 44 55)
    (namedBoth (targetTriple 53 54 55) (.all 9
      (.imp (namedBoth (.member 44 9) (targetTriple 53 54 9)) (.equal 9 55)))) := by decide

/-- For one shared source output, two full matching paths have equal target
outputs. All retained clauses are literal K antecedents; names and values
need not be pairwise distinct. -/
def matched_output_unique : KDerivation
    (imp retainedMatchBody.encode (imp rivalMatchBody.encode (equal 55 35))) := by
  let U : Formula := .all 8 reverseUnique
  have h7 := universalInstance 7 50 U (by decide) (by decide) (by decide)
  have hs7 : replace 7 50 U = .all 8 (replace 7 50 reverseUnique) := by decide
  rw [hs7] at h7
  have h8 := universalInstance 8 51 (replace 7 50 reverseUnique)
    (by decide) (by decide) (by decide)
  have hs8 : replace 8 51 (replace 7 50 reverseUnique) =
      .imp rivalReverseCompetitor (namedBoth (.equal 50 30) (.equal 51 31)) := by decide
  rw [hs8] at h8
  let F : Formula := .imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 33)
  let S : Formula := .imp (namedBoth (.member 43 4) (graphFormula 41 31 4)) (.equal 4 34)
  let T : Formula := .imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 35)
  have hf := universalInstance 4 53 F (by decide) (by decide) (by decide)
  have hfshape : replace 4 53 F =
      .imp (namedBoth (.member 42 53) (graphFormula 40 30 53)) (.equal 53 33) := by decide
  rw [hfshape] at hf
  have hs := universalInstance 4 54 S (by decide) (by decide) (by decide)
  have hsshape : replace 4 54 S =
      .imp (namedBoth (.member 43 54) (graphFormula 41 31 54)) (.equal 54 34) := by decide
  rw [hsshape] at hs
  have ht := universalInstance 9 55 T (by decide) (by decide) (by decide)
  have htshape : replace 9 55 T =
      .imp (namedBoth (.member 44 55) (targetTriple 33 34 55)) (.equal 55 35) := by decide
  rw [htshape] at ht
  have hfg := (equalityReplace 50 30 (graphFormula 40 50 53) (by decide) (by decide)).1
  have hfgshape : replace 50 30 (graphFormula 40 50 53) = graphFormula 40 30 53 := by decide
  rw [hfgshape] at hfg
  have hsg := (equalityReplace 51 31 (graphFormula 41 51 54) (by decide) (by decide)).1
  have hsgshape : replace 51 31 (graphFormula 41 51 54) = graphFormula 41 31 54 := by decide
  rw [hsgshape] at hsg
  have htg₁ := (equalityReplace 53 33 (targetTriple 53 54 55) (by decide) (by decide)).1
  have htg₁shape : replace 53 33 (targetTriple 53 54 55) = targetTriple 33 54 55 := by decide
  rw [htg₁shape] at htg₁
  have htg₂ := (equalityReplace 54 34 (targetTriple 33 54 55) (by decide) (by decide)).1
  have htg₂shape : replace 54 34 (targetTriple 33 54 55) = targetTriple 33 34 55 := by decide
  rw [htg₂shape] at htg₂
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rivalMatchBody.encode,retainedMatchBody.encode]
  have hrival : Context Γ rivalMatchBody.encode := .head _ _
  have hmain : Context Γ retainedMatchBody.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (both selectedReverseBody.encode
      (both (both firstImage.encode secondImage.encode) targetOutputBody.encode)) := by
    simpa [retainedMatchBody, matchBody, bothImages, namedBoth, Formula.not, Formula.encode, both, neg] using hmain
  have hm' : Context Γ (both rivalReverse.encode
      (both (both rivalFirst.encode rivalSecond.encode) rivalTarget.encode)) := by
    simpa [rivalMatchBody, namedBoth, Formula.not, Formula.encode, both, neg] using hrival
  have hr := Context.conjunctionLeft hm
  have hf₁ := Context.conjunctionLeft (Context.conjunctionLeft (Context.conjunctionRight hm))
  have hs₁ := Context.conjunctionRight (Context.conjunctionLeft (Context.conjunctionRight hm))
  have ht₁ := Context.conjunctionRight (Context.conjunctionRight hm)
  have hr' := Context.conjunctionLeft hm'
  have hf₂ := Context.conjunctionLeft (Context.conjunctionLeft (Context.conjunctionRight hm'))
  have hs₂ := Context.conjunctionRight (Context.conjunctionLeft (Context.conjunctionRight hm'))
  have ht₂ := Context.conjunctionRight (Context.conjunctionRight hm')
  have hr₁ : Context Γ (both (member 0 30) (both (member 1 31)
      (both (tripleFormula 30 31 32).encode (allCode 7 (allCode 8 reverseUnique.encode))))) := by
    simpa [reverse_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hr₂ : Context Γ (both (member 0 50) (both (member 1 51)
      (both (tripleFormula 50 51 32).encode
        (Formula.all 7 (.all 8 (replace 31 51 (replace 30 50 reverseUnique)))).encode))) := by
    simpa [rival_reverse_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr'
  have hc : Context Γ rivalReverseCompetitor.encode := by
    have h := Context.conjunctionIntro (Context.conjunctionLeft hr₂)
      (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hr₂))
        (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr₂))))
    simpa [rivalReverseCompetitor, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hru := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr₁))
  have hcoords' := Context.mp hc (Context.mp (Context.mp hru (.closed h7)) (.closed h8))
  have hcoords : Context Γ (both (equal 50 30) (equal 51 31)) := by
    simpa [namedBoth, Formula.not, Formula.encode, both, neg] using hcoords'
  have he₁ := Context.conjunctionLeft hcoords
  have he₂ := Context.conjunctionRight hcoords
  have hfirst : Context Γ (both (member 42 33)
      (both (graphFormula 40 30 33).encode (allCode 4 F.encode))) := by
    simpa [firstImage, F, namedBoth, Formula.not, Formula.encode, both, neg] using hf₁
  have hrfirst : Context Γ (both (member 42 53) (both (graphFormula 40 50 53).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 50 4)) (.equal 4 53))).encode)) := by
    simpa [rival_first_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hf₂
  have hedge₁ := Context.conjunctionLeft (Context.conjunctionRight hrfirst)
  have hedge₁' := Context.mp hedge₁ (Context.mp he₁ (.closed hfg))
  have hcomp₁ : Context Γ (both (member 42 53) (graphFormula 40 30 53).encode) :=
    Context.conjunctionIntro (Context.conjunctionLeft hrfirst) hedge₁'
  have he₃ : Context Γ (equal 53 33) := by
    have h := Context.mp hcomp₁ (Context.mp (Context.conjunctionRight (Context.conjunctionRight hfirst)) (.closed hf))
    simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hsecond : Context Γ (both (member 43 34)
      (both (graphFormula 41 31 34).encode (allCode 4 S.encode))) := by
    simpa [secondImage, S, namedBoth, Formula.not, Formula.encode, both, neg] using hs₁
  have hrsecond : Context Γ (both (member 43 54) (both (graphFormula 41 51 54).encode
      (Formula.all 4 (.imp (namedBoth (.member 43 4) (graphFormula 41 51 4)) (.equal 4 54))).encode)) := by
    simpa [rival_second_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hs₂
  have hedge₂ := Context.conjunctionLeft (Context.conjunctionRight hrsecond)
  have hedge₂' := Context.mp hedge₂ (Context.mp he₂ (.closed hsg))
  have hcomp₂ : Context Γ (both (member 43 54) (graphFormula 41 31 54).encode) :=
    Context.conjunctionIntro (Context.conjunctionLeft hrsecond) hedge₂'
  have he₄ : Context Γ (equal 54 34) := by
    have h := Context.mp hcomp₂ (Context.mp (Context.conjunctionRight (Context.conjunctionRight hsecond)) (.closed hs))
    simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
  have htarget : Context Γ (both (member 44 35)
      (both (targetTriple 33 34 35).encode (allCode 9 T.encode))) := by
    simpa [targetOutputBody, T, namedBoth, Formula.not, Formula.encode, both, neg] using ht₁
  have hrtarget : Context Γ (both (member 44 55) (both (targetTriple 53 54 55).encode
      (Formula.all 9 (.imp (namedBoth (.member 44 9) (targetTriple 53 54 9)) (.equal 9 55))).encode)) := by
    simpa [rival_target_shape, namedBoth, Formula.not, Formula.encode, both, neg] using ht₂
  have htriple := Context.conjunctionLeft (Context.conjunctionRight hrtarget)
  have htriple' := Context.mp htriple (Context.mp he₃ (.closed htg₁))
  have htriple'' := Context.mp htriple' (Context.mp he₄ (.closed htg₂))
  have hcomp₃ : Context Γ (both (member 44 55) (targetTriple 33 34 55).encode) :=
    Context.conjunctionIntro (Context.conjunctionLeft hrtarget) htriple''
  have h := Context.mp hcomp₃ (Context.mp (Context.conjunctionRight (Context.conjunctionRight htarget)) (.closed ht))
  simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h

theorem matched_output_unique_certificate : theoremCode (certificate matched_output_unique) =
    imp retainedMatchBody.encode (imp rivalMatchBody.encode (equal 55 35)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchPathUnique

#print axioms PASoundness.PAtoCompactProductMatchPathUnique.matched_output_unique
#print axioms PASoundness.PAtoCompactProductMatchPathUnique.matched_output_unique_certificate
