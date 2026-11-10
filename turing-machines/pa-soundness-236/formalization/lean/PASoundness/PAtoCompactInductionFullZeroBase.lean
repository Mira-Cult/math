import PASoundness.PAtoCompactInductionZeroAlignment
import PASoundness.PAtoCompactScopedZeroComplete
import PASoundness.PAtoCompactAllElimVariableFull

/-! The zero-base schema for PA induction for arbitrary formulas. This
constructs finite K proof data, including quantified predicates, and does not
prove the step schema or full PA induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionFullZeroBase

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactScopedZeroComplete PASoundness.PAtoCompactTermSubstZeroInduction
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactInductionZeroAlignment
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactAllElimVariableFull
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactScopedBindVariable
open PASoundness.PAtoCompactUniformBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The substituted base has no more free variables than its full induction
axiom, whose parameter guard is used by the construction. -/
theorem base_free_subset (φ : Peano.Formula) (x : Nat) :
    (FOL.substAt φ x Peano.zero).freeVarFinset ⊆
      (Peano.inductionAxiom φ x).freeVarFinset := by
  intro y hy
  simp [Peano.inductionAxiom, BoundedFormula.freeVarFinset] at hy ⊢
  exact Or.inl hy

/-- For every PA formula, including those with nested quantifiers, the
translated PA base entails the uniform zero-base schema. The predicate is
represented by its scope at the fresh instance binder. No finite K proof-data
input is required. -/
noncomputable def full_zero_uniform_base (φ : Peano.Formula) (x m base : Nat)
    (hm : m < base)
    (hfresh : m ∉ (Peano.inductionAxiom φ x).freeVarFinset) :
    let t := instanceBinder φ x m
    KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (uniformBaseCode t m (base+3) (scopeAt φ x t)))) := by
  dsimp only
  let I := Peano.inductionAxiom φ x
  let t := instanceBinder φ x m
  have hg : m ∉ (guardFormula I).free := fun h => hfresh (guardFormula_free_subset I h)
  have ha : m ∉ (formula (FOL.substAt φ x Peano.zero)).free :=
    fun h => hfresh (base_free_subset φ x (formula_free_subset _ h))
  have hr := (formula_zero_substitution (guardFormula I) x m base hm φ).2
  have hs := (formula_bind_variable φ x m).1
  have hv := (variable_scope_alignment φ x m).2
  have halign : KDerivation (imp (guardFormula I).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (termGraph id Peano.zero m base).encode
          (replace t m (scopeAt φ x t)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let G := (guardFormula I).encode
    let A := code (FOL.substAt φ x Peano.zero)
    let Z := (termGraph id Peano.zero m base).encode
    let Γ := [Z,A,G]
    have hg' : Context Γ G := .hypothesis (by simp [Γ])
    have ha' : Context Γ A := .hypothesis (by simp [Γ])
    have hz : Context Γ Z := Context.head _ _
    have hboth : Context Γ (andF (guardFormula I) (termGraph id Peano.zero m base)).encode := by
      simpa [andF, Formula.encode, CompactNamed.Formula.not, both, neg] using Context.conjunctionIntro hg' hz
    have hi : Context Γ (code (FOL.substAt φ x (.var m))) := .mp ha' (.mp hboth (.closed hr))
    have hscope : Context Γ (scopeAt φ x m).encode := .mp hi (.closed hs)
    exact .mp hscope (.closed hv)
  exact uniform_base_of_zero_alignment φ x t m base (scopeAt φ x t) (by omega) hg ha halign

theorem full_zero_uniform_base_certificate (φ : Peano.Formula) (x m base : Nat)
    (hm : m < base)
    (hfresh : m ∉ (Peano.inductionAxiom φ x).freeVarFinset) :
    let t := instanceBinder φ x m
    theoremCode (certificate (full_zero_uniform_base φ x m base hm hfresh)) =
      imp (guardFormula (Peano.inductionAxiom φ x)).encode
        (imp (code (FOL.substAt φ x Peano.zero))
          (uniformBaseCode t m (base+3) (scopeAt φ x t))) :=
  certificate_correct _

end PASoundness.PAtoCompactInductionFullZeroBase

#print axioms PASoundness.PAtoCompactInductionFullZeroBase.base_free_subset
#print axioms PASoundness.PAtoCompactInductionFullZeroBase.full_zero_uniform_base
#print axioms PASoundness.PAtoCompactInductionFullZeroBase.full_zero_uniform_base_certificate
