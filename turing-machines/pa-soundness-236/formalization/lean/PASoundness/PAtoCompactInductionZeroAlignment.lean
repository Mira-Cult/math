import PASoundness.PAtoCompactZeroTermTotality
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactUniformBase
import PASoundness.PAtoCompactGuardedBridge

/-! The zero-base portion of the guarded PA-induction bridge, conditional on
an explicit reverse substitution alignment for the displayed PA predicate.
This is finite K proof data; the alignment is not constructed here, and no
PA induction axiom is proved. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionZeroAlignment

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyDomain
open PASoundness.PAtoCompactZeroTermTotality PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactGuardedBridge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Any explicit zero, not just an existentially chosen zero, supplies the
literal zero term graph at that name. The name bound avoids every private
binder in the zero and candidate templates. -/
def zero_implies_term_graph (m base : Nat) (hm : m < base + 3) :
    KDerivation (imp (zeroCode m (base+3))
      (termGraph id Peano.zero m base).encode) := by
  have hf : [m,base+3,base+32,base+33,base+34,base+35,
      base+36,base+37,base+38,base+39].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega
  have hc := zero_candidate m (base+3) (base+32) (base+33) (base+34)
    (base+35) (base+36) (base+37) (base+38) (base+39) hf
  have hd : KDerivation (imp (zeroCode m (base+3)) (domainAt base m).encode) := by
    simpa only [domainAt_code, PASoundness.PAtoCompactCandidateExact.candidateCode] using hc
  change KDerivation (imp (zeroCode m (base+3))
    (andF (domainAt base m) (zeroAt base m)).encode)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [zeroCode m (base+3)]
  have hz : Context Γ (zeroCode m (base+3)) := Context.head [] _
  have hdom : Context Γ (domainAt base m).encode := .mp hz (.closed hd)
  have hz' : Context Γ (zeroAt base m).encode := by simpa only [zeroAt_encode] using hz
  simpa [andF, Formula.encode, CompactNamed.Formula.not, both, neg] using
    (Context.conjunctionIntro hdom hz')

/-- Conditional reduction for the actual translated PA zero antecedent. The
input `align` is the still-open reverse substitution compatibility: under the
induction axiom's guard, the translated φ[0/x] and an explicit zero term graph
imply the selected named predicate instance. The remaining conditions require
the quantified witness name to be absent from the guard and translated base.
The predicate `f` and its relation to φ remain explicit. -/
def uniform_base_of_zero_alignment (φ : Peano.Formula) (x t m base : Nat)
    (f : CompactNamed.Formula) (hm : m < base + 3)
    (hg : m ∉ (guardFormula (Peano.inductionAxiom φ x)).free)
    (ha : m ∉ (formula (FOL.substAt φ x Peano.zero)).free)
    (align : KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (termGraph id Peano.zero m base).encode
          (replace t m f).encode)))) :
    KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero)) (uniformBaseCode t m (base+3) f))) := by
  let G := (guardFormula (Peano.inductionAxiom φ x)).encode
  let A := code (FOL.substAt φ x Peano.zero)
  let Z := zeroCode m (base+3)
  let F := (replace t m f).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [A,G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hA : Context Γ A := Context.head [_] _
  have hpoint : Context Γ (imp Z F) := by
    apply Context.deduction
    have hZ : Context (Z :: Γ) Z := Context.head Γ Z
    have hgraph : Context (Z :: Γ) (termGraph id Peano.zero m base).encode :=
      .mp hZ (.closed (zero_implies_term_graph m base hm))
    exact .mp hgraph (.mp (Context.under hA Z) (.mp (Context.under hG Z) (.closed align)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode m h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = A
    · subst h
      exact free_vacuity m (formula (FOL.substAt φ x Peano.zero)) ha
    · have he' : h = G := hh.resolve_left he
      subst h
      exact free_vacuity m (guardFormula (Peano.inductionAxiom φ x)) hg
  exact Context.generalize m hv hpoint

theorem uniform_base_of_zero_alignment_certificate (φ : Peano.Formula) (x t m base : Nat)
    (f : CompactNamed.Formula) (hm : m < base + 3)
    (hg : m ∉ (guardFormula (Peano.inductionAxiom φ x)).free)
    (ha : m ∉ (formula (FOL.substAt φ x Peano.zero)).free)
    (align : KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (termGraph id Peano.zero m base).encode
          (replace t m f).encode)))) :
    theoremCode (certificate (uniform_base_of_zero_alignment φ x t m base f hm hg ha align)) =
      imp (guardFormula (Peano.inductionAxiom φ x)).encode
        (imp (code (FOL.substAt φ x Peano.zero)) (uniformBaseCode t m (base+3) f)) :=
  certificate_correct _
end PASoundness.PAtoCompactInductionZeroAlignment

#print axioms PASoundness.PAtoCompactInductionZeroAlignment.zero_implies_term_graph
#print axioms PASoundness.PAtoCompactInductionZeroAlignment.uniform_base_of_zero_alignment
#print axioms PASoundness.PAtoCompactInductionZeroAlignment.uniform_base_of_zero_alignment_certificate
