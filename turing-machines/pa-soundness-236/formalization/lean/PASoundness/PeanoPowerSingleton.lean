import PASoundness.PeanoEmptyBitSet

/-! An object-level nonempty bit-code construction toward comprehension. -/
namespace PASoundness.PeanoPowerSingleton
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication PeanoAdditionAssociative CompactArithmetic

/-- The exact quotient-zero/remainder-zero bit-row equation, derived in PA
for an arbitrary proposed power term. -/
theorem zero_row_equation (p : Peano.Term) :
    FormulaProves (p.equal (add (add (mul zero (add p p)) p) zero)) := by
  have h₁ := FOL.Derivation.axiom (Peano.Axiom.add_zero (add (mul zero (add p p)) p))
  have h₂ := FOL.Derivation.mp (add_left_congr p (mul zero (add p p)) zero)
    (PeanoMultiplication.zero_mul (add p p))
  have h₃ := zero_add p
  exact FOL.Derivation.eqSymm (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃)

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

private def matrix (p q r : Peano.Term) : Peano.Formula :=
  ((.var 0 : Peano.Term).equal (add (add (mul q (add p p)) p) r)) ⊓ less r p

private def outer : Peano.Formula :=
  (pow2 (.var 1) (.var 2)) ⊓ (FOL.existsAt 3 (FOL.existsAt 4 (matrix (.var 2) (.var 3) (.var 4))))

private theorem bit_template_syntax : bitTemplate = FOL.existsAt 2 outer := by rfl

private theorem matrix_subst (p q r : Peano.Term) (σ : Nat → Peano.Term) :
    (matrix p q r).subst σ =
      (((σ 0).equal (add (add (mul (q.subst σ) (add (p.subst σ) (p.subst σ)))
        (p.subst σ)) (r.subst σ))) ⊓ (less (r.subst σ) (p.subst σ))) := by
  simp only [matrix, subst_and, FOL.equality_subst, add_subst, mul_subst, less_subst,
    FirstOrder.Language.Term.subst]

private theorem outer_p_syntax :
    FOL.substAt outer 2 (.var 0) =
      (pow2 (.var 1) (.var 0)) ⊓
        (FOL.existsAt 3 (FOL.existsAt 4 (matrix (.var 0) (.var 3) (.var 4)))) := by
  let σ : Nat → Peano.Term := fun y => if y = 2 then .var 0 else .var y
  have hp : (pow2 (.var 1) (.var 2)).subst σ = pow2 (.var 1) (.var 0) := by
    simp [pow2_subst, σ, FirstOrder.Language.Term.subst]
  have hs : (FOL.existsAt 3 (FOL.existsAt 4 (matrix (.var 2) (.var 3) (.var 4)))).subst σ =
      FOL.existsAt 3 (FOL.existsAt 4 (matrix (.var 0) (.var 3) (.var 4))) := by
    simp [σ, matrix, FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v,
      Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
      FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  change (pow2 (.var 1) (.var 2) ⊓
    FOL.existsAt 3 (FOL.existsAt 4 (matrix (.var 2) (.var 3) (.var 4)))).subst σ = _
  rw [subst_and, hp, hs]

private theorem scope_q_syntax :
    FOL.substAt (FOL.existsAt 4 (matrix (.var 0) (.var 3) (.var 4))) 3 zero =
      FOL.existsAt 4 (matrix (.var 0) zero (.var 4)) := by
  simp [FOL.substAt, matrix, FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v,
    Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private theorem matrix_r_syntax : FOL.substAt (matrix (.var 0) zero (.var 4)) 4 zero =
    (((.var 0 : Peano.Term).equal
      (add (add (mul zero (add (.var 0) (.var 0))) (.var 0)) zero)) ⊓ less zero (.var 0)) := by
  simp [FOL.substAt, matrix_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]

private theorem bit_intro_vars : FormulaProves
    ((pow2 (.var 1) (.var 0)).imp ((less zero (.var 0)).imp bitTemplate)) := by
  let P : Peano.Formula := pow2 (.var 1) (.var 0)
  let H : Peano.Formula := less zero (.var 0)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom [H, P] P := FOL.Context.under (FOL.Context.head [] P) H
  have hpos : FOL.Context Peano.Axiom [H, P] H := FOL.Context.head _ _
  have hmatrix : FOL.Context Peano.Axiom [H, P]
      (FOL.substAt (matrix (.var 0) zero (.var 4)) 4 zero) := by
    rw [matrix_r_syntax]
    exact FOL.Context.conjunctionIntro (.closed (zero_row_equation (.var 0))) hpos
  have hr : FOL.Context Peano.Axiom [H, P] (FOL.existsAt 4 (matrix (.var 0) zero (.var 4))) :=
    .mp (.closed (FOL.Derivation.existsIntro (matrix (.var 0) zero (.var 4)) 4 zero)) hmatrix
  have hq : FOL.Context Peano.Axiom [H, P]
      (FOL.existsAt 3 (FOL.existsAt 4 (matrix (.var 0) (.var 3) (.var 4)))) := by
    apply FOL.Context.mp (.closed
      (FOL.Derivation.existsIntro (FOL.existsAt 4 (matrix (.var 0) (.var 3) (.var 4))) 3 zero))
    rw [scope_q_syntax]
    exact hr
  have houter : FOL.Context Peano.Axiom [H, P] (FOL.substAt outer 2 (.var 0)) := by
    rw [outer_p_syntax]
    exact FOL.Context.conjunctionIntro hp hq
  have hbit : FOL.Context Peano.Axiom [H, P] (FOL.existsAt 2 outer) :=
    .mp (.closed (FOL.Derivation.existsIntro outer 2 (.var 0))) houter
  rw [bit_template_syntax]
  exact hbit

private theorem template_as_bit : bitFormula (.var 0) (.var 1) = bitTemplate := by
  unfold bitFormula
  calc
    bitTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        bitTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [bitTemplate_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = bitTemplate := SyntaxTransport.formula_subst_var _

private def ownBitRelation (n p : Peano.Term) : Peano.Formula :=
  (pow2 n p).imp ((less zero p).imp (bitFormula p n))

private theorem specialize (n p : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (ownBitRelation n p)) : FormulaProves (ownBitRelation
      (n.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (ownBitRelation n p) name t))
    (.generalize name h)
  simpa only [FOL.substAt, ownBitRelation, subst_imp, pow2_subst, less_subst, bitFormula_subst,
    PeanoArithmetic.zero_subst] using h₁

/-- Given a literal power trace and an explicit object-level positivity
proof, PA derives that the power code has its own index bit set. The three
existential witnesses are the power term, zero quotient, and zero remainder.
This is not a singleton nonmembership or power-existence theorem. -/
theorem power_has_own_bit (n p : Peano.Term) :
    FormulaProves ((pow2 n p).imp ((less zero p).imp (bitFormula p n))) := by
  let support := n.varFinset ∪ p.varFinset
  let k := support.sup id + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have fresh (j : Nat) (hj : k ≤ j) : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at hj
    omega
  have hn : k+1 ∉ n.varFinset := by
    intro h
    apply fresh (k+1) (by omega)
    simp [support, h]
  have hv : FormulaProves (ownBitRelation (.var 1) (.var 0)) := by
    simpa only [ownBitRelation, template_as_bit] using bit_intro_vars
  have h1 := specialize _ _ 1 (.var k) hv
  have h1' : FormulaProves (ownBitRelation (.var k) (.var 0)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 0 (.var (k+1)) h1'
  have h2' : FormulaProves (ownBitRelation (.var k) (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 0 by omega] using h2
  have h3 := specialize _ _ k n h2'
  have h3' : FormulaProves (ownBitRelation n (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega] using h3
  have h4 := specialize _ _ (k+1) p h3'
  simpa [ownBitRelation, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+1) p hn] using h4

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ := .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- Every endpoint of a literal power trace is positive in PA. -/
theorem power_positive (n p : Peano.Term) : FormulaProves ((pow2 n p).imp (less zero p)) := by
  let P : Peano.Formula := pow2 n p
  let E : Peano.Formula := zero.equal n
  let L : Peano.Formula := less zero n
  let G : Peano.Formula := less n zero
  let T : Peano.Formula := less zero p
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hnp : FOL.Context Peano.Axiom [P] (less n p) :=
    .mp (.closed (PeanoPowerGrowth.power_growth n p)) (FOL.Context.head [] P)
  have he : FOL.Context Peano.Axiom [P] (E.imp T) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.closed (PeanoQuotientGap.less_left_congr n zero p))
      (FOL.Context.eqSymm (FOL.Context.head [P] E))) (FOL.Context.under hnp E)
  have hl : FOL.Context Peano.Axiom [P] (L.imp T) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all zero n p))
      (FOL.Context.head [P] L)) (FOL.Context.under hnp L)
  have hg : FOL.Context Peano.Axiom [P] (G.imp T) := by
    apply FOL.Context.deduction
    exact FOL.Context.explode T (.mp (.closed (PeanoEmptyBitSet.no_less_zero n)) (FOL.Context.head [P] G))
  have hinner : FOL.Context Peano.Axiom [P] ((E ⊔ L).imp T) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head _ (E ⊔ L)) (FOL.Context.under he _) (FOL.Context.under hl _)
  exact or_elim (.closed (PeanoOrderTotality.trichotomy_all zero n)) hinner hg

/-- Every claimed power trace supplies a code with its indexed bit set. This
does not assert the existence of the trace or exclude bits at other indices. -/
theorem power_trace_sets_bit (n p : Peano.Term) :
    FormulaProves ((pow2 n p).imp (bitFormula p n)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom [pow2 n p] (pow2 n p) := FOL.Context.head [] _
  exact .mp (.mp (.closed (power_has_own_bit n p)) hp) (.mp (.closed (power_positive n p)) hp)

end PASoundness.PeanoPowerSingleton
