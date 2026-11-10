import PASoundness.PeanoBetaUniformPairs

/-! Reformulate the uniform beta-modulus inverse witnesses for arbitrary
ordered endpoints. The results do not construct simultaneous beta rows. -/
namespace PASoundness.PeanoBetaEndpointPairs
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaPairDivisible PeanoBetaUniformPairs

def targetBody (u v : Peano.Term) : Peano.Formula :=
  (mul (modulus (.var 1) (.var 0)) u).equal
    (add (succ zero) (mul v (modulus (.var 1) (.var 5))))

def target : Peano.Formula :=
  FOL.existsAt 3 (FOL.existsAt 4 (targetBody (.var 3) (.var 4)))

private theorem target_subst_gap : FOL.substAt target 5 (add (.var 0) (succ (.var 2))) = inverseTemplate := by
  simp [FOL.substAt, target, targetBody, inverseTemplate, inverseBody, FOL.existsAt, FOL.allAt,
    modulus, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private theorem target_subst_self : FOL.substAt target 5 (.var 5) = target := by
  unfold FOL.substAt
  have h : (fun y : Nat => if y = 5 then (FirstOrder.Language.Term.var 5 : Peano.Term) else .var y) = Term.var := by
    funext y
    by_cases hy : y = 5 <;> simp [hy]
  rw [h]
  exact SyntaxTransport.formula_subst_var _

/-- PA transports the inverse target along a literal index equality. -/
theorem inverse_transport : FormulaProves
    (((.var 5 : Peano.Term).equal (add (.var 0) (succ (.var 2)))).imp
      (inverseTemplate.imp target)) := by
  let E : Peano.Formula := (.var 5 : Peano.Term).equal (add (.var 0) (succ (.var 2)))
  have hs := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst target 5 (add (.var 0) (succ (.var 2))) (.var 5))
  rw [target_subst_gap, target_subst_self] at hs
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [inverseTemplate,E] E :=
    FOL.Context.under (FOL.Context.head [] E) inverseTemplate
  exact .mp (.mp (.closed hs) (FOL.Context.eqSymm he))
    (FOL.Context.head [E] inverseTemplate)

/-- Eliminate the index-gap witness once both its equation and the inverse
formula are available at that witness. -/
theorem eliminate_gap_inverse : FormulaProves
    ((FOL.existsAt 2 (((.var 5 : Peano.Term).equal
      (add (.var 0) (succ (.var 2)))) ⊓ inverseTemplate)).imp target) := by
  let E : Peano.Formula := (.var 5 : Peano.Term).equal (add (.var 0) (succ (.var 2)))
  let B : Peano.Formula := E ⊓ inverseTemplate
  have hbody : FormulaProves (B.imp target) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hb : FOL.Context Peano.Axiom [B] B := FOL.Context.head [] B
    exact .mp (.mp (.closed inverse_transport) (FOL.Context.conjunctionLeft hb))
      (FOL.Context.conjunctionRight hb)
  have hf : 2 ∉ target.freeVarFinset := by decide
  exact PeanoBitPositionReduction.exists_elim 2 hf hbody

private theorem less_endpoint_syntax : less (.var 0) (.var 5) =
    FOL.existsAt 2 ((add (.var 0) (succ (.var 2))).equal (.var 5)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.existsAt, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- The uniform gap-indexed inverse assertion, with its original bound N=7
and parameter C=1. -/
def gapUniform : Peano.Formula := FOL.allAt 0 (FOL.allAt 2
  ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate))

/-- Internal PA composition: assuming the gap-indexed inverse assertion,
ordered endpoints i<j≤N have inverse witnesses. The endpoint j is name 5. -/
theorem endpoint_inverse :
    FormulaProves (gapUniform.imp ((less (.var 0) (.var 5)).imp
      ((less (.var 5) (succ (.var 7))).imp target))) := by
  let U := gapUniform
  let E : Peano.Formula := (add (.var 0) (succ (.var 2))).equal (.var 5)
  let L := less (.var 5) (succ (.var 7))
  have hrow : FormulaProves (E.imp (U.imp (L.imp target))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [L,U,E] E :=
      FOL.Context.under (FOL.Context.under (FOL.Context.head [] E) U) L
    have hu : FOL.Context Peano.Axiom [L,U,E] U :=
      FOL.Context.under (FOL.Context.head [E] U) L
    have hl : FOL.Context Peano.Axiom [L,U,E] L := FOL.Context.head _ _
    have hu0 : FOL.Context Peano.Axiom [L,U,E] (FOL.allAt 2
        ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate)) :=
      FOL.Context.allSelf hu
    have huk : FOL.Context Peano.Axiom [L,U,E]
        ((less (add (.var 0) (succ (.var 2))) (succ (.var 7))).imp inverseTemplate) :=
      FOL.Context.allSelf hu0
    have hb : FOL.Context Peano.Axiom [L,U,E]
        (less (add (.var 0) (succ (.var 2))) (succ (.var 7))) :=
      .mp (.mp (.closed (PeanoQuotientGap.less_left_congr (.var 5)
        (add (.var 0) (succ (.var 2))) (succ (.var 7)))) (FOL.Context.eqSymm he)) hl
    have hi : FOL.Context Peano.Axiom [L,U,E] inverseTemplate := .mp huk hb
    exact .mp (.mp (.closed inverse_transport) (FOL.Context.eqSymm he)) hi
  have hf : 2 ∉ (U.imp (L.imp target)).freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 2 hf hrow
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hu : FOL.Context Peano.Axiom [L,less (.var 0) (.var 5),U] U :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] U) (less (.var 0) (.var 5))) L
  have hg : FOL.Context Peano.Axiom [L,less (.var 0) (.var 5),U]
      (FOL.existsAt 2 E) := by
    simpa only [less_endpoint_syntax, E] using
      (FOL.Context.under (FOL.Context.head [U] (less (.var 0) (.var 5))) L)
  have hl : FOL.Context Peano.Axiom [L,less (.var 0) (.var 5),U] L := FOL.Context.head _ _
  exact .mp (.mp (.mp (.closed h) hg) hu) hl

/-- For arbitrary ordered endpoint names i=0 and j=5, derive the uniform
endpoint formulation from the gap-indexed one. -/
theorem endpoint_inverse_uniform :
    FormulaProves (gapUniform.imp (FOL.allAt 0 (FOL.allAt 5
      ((less (.var 0) (.var 5)).imp ((less (.var 5) (succ (.var 7))).imp target))))) := by
  let U := gapUniform
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 0
  · intro φ hφ
    have he : φ = U := by simpa using hφ
    subst φ
    decide
  apply FOL.Context.generalize 5
  · intro φ hφ
    have he : φ = U := by simpa using hφ
    subst φ
    decide
  exact .mp (.closed endpoint_inverse) (FOL.Context.head [] U)

/-- Ordered endpoint condition: i=0, j=5, C=1 and N=7. -/
def endpointUniform : Peano.Formula := FOL.allAt 0 (FOL.allAt 5
  ((less (.var 0) (.var 5)).imp ((less (.var 5) (succ (.var 7))).imp target)))

/-- Keep the exact previously established parameter matrix while adding its
arbitrary ordered-endpoint reformulation. -/
def endpointPairExists : Peano.Formula := FOL.existsAt 1 (uniformPairBody ⊓ endpointUniform)

/-- PA constructs a parameter above R that retains the original common-divisor
and gap-indexed inverse matrix and also supplies inverse witnesses for every
ordered i<j≤N. No simultaneous beta rows or CRT conclusion are asserted. -/
theorem endpoint_pair_parameter_exists_vars : FormulaProves endpointPairExists := by
  let B := uniformPairBody
  have hbody : FormulaProves (B.imp endpointPairExists) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hb : FOL.Context Peano.Axiom [B] B := FOL.Context.head [] B
    have hu : FOL.Context Peano.Axiom [B] gapUniform :=
      FOL.Context.conjunctionRight (FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hb))
    have he : FOL.Context Peano.Axiom [B] endpointUniform :=
      .mp (.closed endpoint_inverse_uniform) hu
    have hboth : FOL.Context Peano.Axiom [B] (B ⊓ endpointUniform) :=
      FOL.Context.conjunctionIntro hb he
    have hi : FormulaProves ((B ⊓ endpointUniform).imp endpointPairExists) := by
      simpa only [endpointPairExists, B, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (uniformPairBody ⊓ endpointUniform) 1 (.var 1))
    exact .mp (.closed hi) hboth
  have hf : 1 ∉ endpointPairExists.freeVarFinset := by decide
  have hex := PeanoBitPositionReduction.exists_elim 1 hf hbody
  exact .mp hex uniform_pair_parameter_exists_vars

/-- Universally closed ordered-endpoint common-parameter theorem. -/
theorem endpoint_pair_parameter_exists :
    FormulaProves (FOL.allAt 7 (FOL.allAt 8 endpointPairExists)) :=
  .generalize 7 (.generalize 8 endpoint_pair_parameter_exists_vars)

end PASoundness.PeanoBetaEndpointPairs
