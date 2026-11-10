import PASoundness.PAtoCompactLiteralCutOriginalAllocated
import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactCandidateReflexivity
import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.PAtoCompactFreeVacuity

/-! A literal cut is an ordinary addition cut: use the first input itself as
its cut witness and preserve the already supplied suffix. Candidate-relative
reflexivity supplies the one extra isomorphism. This is a fixed-label proof,
not addition existence, multiplication successor, or arithmetic soundness. -/
namespace PASoundness.PAtoCompactLiteralCutToAdditionFixed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateReflexivity PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport
open PASoundness.PAtoCompactLiteralCutAdditionDefinition PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def cutCondition : Formula := namedEither (.equal 30 32) (.member 32 30)
private def tailCondition : Formula := replace 33 30 suffixFormula
private def suffixEquiv : Formula := PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34
private def selfEquiv : Formula := PASoundness.PAtoCompactOrdinalAddition.equivAt 30 30
private def literalBody : Formula := namedBoth cutCondition (namedBoth tailCondition suffixEquiv)
private def additionBody : Formula := namedBoth cutCondition
  (namedBoth selfEquiv (namedBoth tailCondition suffixEquiv))
private def chosenCut : Formula := .ex 34 additionBody
private def outerBody : Formula := .ex 34
  (namedBoth (namedEither (.equal 33 32) (.member 32 33))
    (namedBoth (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33)
      (namedBoth suffixFormula (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34))))

private theorem source_shape : literalCut = .ex 34 literalBody := by rfl
private theorem target_shape : additionFormula = .ex 33 outerBody := by rfl
private theorem chosen_shape : replace 33 30 outerBody = chosenCut := by decide
private theorem self_shape : selfEquiv = reflexive30 := by rfl

/-- One supplied literal-cut witness yields an ordinary addition witness,
under the candidate guard on the first input. The suffix witness is retained. -/
def raw_fixed : KDerivation (imp (domainAt 100 30).encode
    (imp literalCut.encode additionFormula.encode)) := by
  have hSelf : KDerivation (imp (domainAt 100 30).encode selfEquiv.encode) := by
    simpa only [self_shape] using compose guard_to_input_candidate candidate_reflexive
  have hIntro := exists_from_instance 33 30 outerBody (by decide) (by decide) (by decide)
  rw [chosen_shape] at hIntro
  have hSuffix := existsIntroduce 34 additionBody (by decide)
  have hChosenVac := free_vacuity 34 chosenCut (by decide)
  have hGuardVac := free_vacuity 34 (domainAt 100 30) (by decide)
  have hLitVac := free_vacuity 34 literalCut (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [literalCut.encode, (domainAt 100 30).encode]
  have hlit : Context Γ literalCut.encode := .head _ _
  have hguard : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hrefl : Context Γ selfEquiv.encode := .mp hguard (.closed hSelf)
  have hpoint : Context Γ (imp literalBody.encode chosenCut.encode) := by
    apply Context.deduction
    let Δ := literalBody.encode :: Γ
    have hm : Context Δ literalBody.encode := .head _ _
    have hcut := Context.conjunctionLeft hm
    have htail := Context.conjunctionRight hm
    have hr : Context Δ selfEquiv.encode := Context.under hrefl _
    have hn : Context Δ additionBody.encode := by
      have h := Context.conjunctionIntro hcut
        (Context.conjunctionIntro hr htail)
      simpa [additionBody, literalBody, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have hf := Context.mp hn (.closed hSuffix)
    simpa [chosenCut, Formula.encode, existsCode] using hf
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 34 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = literalCut.encode
    · subst h; exact hLitVac
    · have he' : h = (domainAt 100 30).encode := hh.resolve_left he
      subst h; exact hGuardVac
  have hall := Context.generalize 34 hv hpoint
  have hex : Context Γ (existsCode 34 literalBody.encode) := by
    simpa [source_shape, Formula.encode, existsCode] using hlit
  have hchosen : Context Γ chosenCut.encode := Context.existsElim hChosenVac hall hex
  have hadd := Context.mp hchosen (.closed hIntro)
  simpa [target_shape, Formula.encode, existsCode] using hadd

/-- The same fixed-label implication using the selected private allocator
block; 30, 31 and 32 remain free parameter names. -/
def allocated_fixed (b : Nat) (hb : 38 ≤ b) : KDerivation
    (imp (domainAt 100 30).encode
      (imp (literalCutAt b 30 31 32).encode (addAt b 30 31 32).encode)) := by
  have hL := (PASoundness.PAtoCompactLiteralCutOriginalAllocated.original_allocated_alpha b hb).backward
  have hA := (PASoundness.PAtoCompactAdditionZeroAllocated.original_allocated_alpha b hb).forward
  have hshape : PASoundness.PAtoCompactAddBaseInventory.addTemplate = additionFormula := by decide
  rw [hshape] at hA
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(literalCutAt b 30 31 32).encode, (domainAt 100 30).encode]
  have hl : Context Γ (literalCutAt b 30 31 32).encode := .head _ _
  have hd : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hraw : Context Γ literalCut.encode := .mp hl (.closed hL)
  have ha : Context Γ additionFormula.encode := .mp hraw (.mp hd (.closed raw_fixed))
  exact .mp ha (.closed hA)

theorem allocated_fixed_certificate (b : Nat) (hb : 38 ≤ b) :
    theoremCode (certificate (allocated_fixed b hb)) =
      imp (domainAt 100 30).encode
        (imp (literalCutAt b 30 31 32).encode (addAt b 30 31 32).encode) := certificate_correct _

end PASoundness.PAtoCompactLiteralCutToAdditionFixed

#print axioms PASoundness.PAtoCompactLiteralCutToAdditionFixed.raw_fixed
#print axioms PASoundness.PAtoCompactLiteralCutToAdditionFixed.allocated_fixed
#print axioms PASoundness.PAtoCompactLiteralCutToAdditionFixed.allocated_fixed_certificate
