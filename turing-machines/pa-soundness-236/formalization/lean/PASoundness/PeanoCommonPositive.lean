import PASoundness.PeanoCommonMultiple

/-! For arbitrary arithmetic terms N,R, PA constructs C>R, C>0, divisible
by every positive d≤N. This uses the earlier successor-indexed common multiple,
a PA predecessor witness, and explicit order and equality transports. Standard
meaning is established separately. -/

/-! Actual PA predecessor witness for positive terms. -/
namespace PASoundness.PeanoCommonPositive.Predecessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- The literal formula asserting a predecessor for free name zero. -/
def predecessorTemplate : Peano.Formula :=
  FOL.existsAt 3 ((.var 0 : Peano.Term).equal (succ (.var 3)))

/-- Capture-safe application of the predecessor template to an arbitrary term. -/
def hasPredecessor (d : Peano.Term) : Peano.Formula :=
  predecessorTemplate.subst (fun y => if y = 0 then d else zero)

/-- Standard meaning, proved separately from the PA derivation. -/
theorem hasPredecessor_realize (d : Peano.Term) (ρ : Nat → Nat) :
    (hasPredecessor d).Realize ρ ↔ ∃ j : Nat, d.realize ρ = j + 1 := by
  classical
  simp [hasPredecessor, predecessorTemplate, FOL.existsAt, FOL.realize_allAt,
    FOL.realize_subst, Classical.not_forall, Peano.realize_succ]

/-- Capture-safe predecessor formula for divisor name 4 and witness name 3. -/
theorem predecessor_four_syntax : hasPredecessor (.var 4) =
    FOL.existsAt 3 ((.var 4 : Peano.Term).equal (succ (.var 3))) := by
  simp [hasPredecessor, predecessorTemplate, FOL.existsAt, FOL.allAt,
    Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  rfl

private theorem positive_syntax : less zero (.var 0) =
    FOL.existsAt 3 ((add zero (succ (.var 3))).equal (.var 0)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.existsAt, FOL.allAt, Peano.add, Peano.succ, Peano.zero,
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

/-- Derive an actual predecessor witness from the positive-order witness. -/
theorem predecessor_vars : FormulaProves ((less zero (.var 0)).imp predecessorTemplate) := by
  let row : Peano.Formula := (add zero (succ (.var 3))).equal (.var 0)
  have hrow : FormulaProves (row.imp predecessorTemplate) := by
    have he : FormulaProves (((.var 0 : Peano.Term).equal (succ (.var 3))).imp predecessorTemplate) := by
      simpa only [predecessorTemplate, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom)
          ((.var 0 : Peano.Term).equal (succ (.var 3))) 3 (.var 3))
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hs : FOL.Context Peano.Axiom [row]
        ((.var 0 : Peano.Term).equal (succ (.var 3))) :=
      FOL.Context.eqTrans (FOL.Context.eqSymm (FOL.Context.head [] row))
        (.closed (zero_add (succ (.var 3))))
    exact .mp (.closed he) hs
  have hfresh : 3 ∉ predecessorTemplate.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 3 hfresh hrow
  simpa only [positive_syntax, row] using h

private theorem template_freeVars : predecessorTemplate.freeVarFinset = {0} := by decide

private theorem template_as_hasPredecessor : hasPredecessor (.var 0) = predecessorTemplate := by
  unfold hasPredecessor
  calc
    predecessorTemplate.subst (fun y => if y = 0 then .var 0 else zero) =
        predecessorTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_freeVars, Finset.mem_singleton] at hy
      subst y
      rfl
    _ = predecessorTemplate := SyntaxTransport.formula_subst_var _

private theorem hasPredecessor_subst (d : Peano.Term) (σ : Nat → Peano.Term) :
    (hasPredecessor d).subst σ = hasPredecessor (d.subst σ) := by
  unfold hasPredecessor
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> simp [h0]

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- For any arithmetic term, PA proves that positivity supplies a predecessor. -/
theorem positive_has_predecessor (d : Peano.Term) :
    FormulaProves ((less zero d).imp (hasPredecessor d)) := by
  let φ : Peano.Formula := (less zero (.var 0)).imp (hasPredecessor (.var 0))
  have hvars : FormulaProves φ := by
    simpa only [φ, template_as_hasPredecessor] using predecessor_vars
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ 0 d))
    (.generalize 0 hvars)
  simpa [FOL.substAt, φ, subst_imp, less_subst, hasPredecessor_subst,
    PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst] using h

end PASoundness.PeanoCommonPositive.Predecessor

/-! An arbitrary-positive-divisor interface for the PA common multiple. -/
namespace PASoundness.PeanoCommonPositive
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoCommonMultiple PeanoCommonPositive.Predecessor

/-- Fixed-name matrix: the selected multiple exceeds the requested bound,
is positive, and is divisible by each positive d≤n. -/
def positiveBody (n r c : Peano.Term) : Peano.Formula :=
  (less r c) ⊓ ((less zero c) ⊓ FOL.allAt 4
    ((less zero (.var 4)).imp ((less (.var 4) (succ n)).imp (divides (.var 4) c))))

def positiveTemplate : Peano.Formula := FOL.existsAt 2
  (positiveBody (.var 0) (.var 1) (.var 2))

/-- Capture-safe application of the positive common-multiple formula. -/
def positiveCommon (n r : Peano.Term) : Peano.Formula :=
  positiveTemplate.subst (fun y => if y = 0 then n else if y = 1 then r else zero)

/-- Standard meaning, separate from the PA derivation. -/
theorem positiveCommon_realize (n r : Peano.Term) (ρ : Nat → Nat) :
    (positiveCommon n r).Realize ρ ↔
      ∃ c : Nat, r.realize ρ < c ∧ 0 < c ∧
        ∀ d : Nat, 0 < d → d ≤ n.realize ρ → ∃ q : Nat, c = q*d := by
  classical
  simp [positiveCommon, positiveTemplate, positiveBody, FOL.existsAt, FOL.realize_allAt,
    FOL.realize_subst, Classical.not_forall, Peano.realize_succ, divides_realize, Nat.lt_succ_iff]

/-- With N=0, C=2, j=3 and d=4, a represented predecessor and the explicit
bound d<S N permit a single instantiation of the old bounded divisor clause. -/
theorem bounded_predecessor_divides :
    FormulaProves ((FOL.allAt 3 ((less (.var 3) (.var 0)).imp
        (divides (succ (.var 3)) (.var 2)))).imp
      (((.var 4 : Peano.Term).equal (succ (.var 3))).imp
        ((less (.var 4) (succ (.var 0))).imp (divides (.var 4) (.var 2))))) := by
  let N : Peano.Term := .var 0
  let C : Peano.Term := .var 2
  let J : Peano.Term := .var 3
  let D : Peano.Term := .var 4
  let O : Peano.Formula := FOL.allAt 3 ((less J N).imp (divides (succ J) C))
  let E : Peano.Formula := D.equal (succ J)
  let L : Peano.Formula := less D (succ N)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ho : FOL.Context Peano.Axiom [L, E, O] O :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] O) E) L
  have he : FOL.Context Peano.Axiom [L, E, O] E :=
    FOL.Context.under (FOL.Context.head [O] E) L
  have hl : FOL.Context Peano.Axiom [L, E, O] L := FOL.Context.head _ _
  have hs : FOL.Context Peano.Axiom [L, E, O] (less (succ J) (succ N)) :=
    .mp (.mp (.closed (PeanoQuotientGap.less_left_congr D (succ J) (succ N))) he) hl
  have hj : FOL.Context Peano.Axiom [L, E, O] (less J N) :=
    .mp (.closed (PeanoOrderSuccessor.less_succ_iff J N).2) hs
  have hi : FOL.Context Peano.Axiom [L, E, O] ((less J N).imp (divides (succ J) C)) :=
    FOL.Context.allSelf ho
  have hd : FOL.Context Peano.Axiom [L, E, O] (divides (succ J) C) := .mp hi hj
  exact .mp (.mp (.closed (PeanoCommonMultiple.DivisibilityBoundary.divisor_congr (succ J) D C))
    (FOL.Context.eqSymm he)) hd


/-- PA proves that `S R < C` implies both `R < C` and `0 < C`. -/
theorem strengthen_bound (R C : Peano.Term) :
    FormulaProves ((less (succ R) C).imp ((less R C) ⊓ (less zero C))) := by
  let H := less (succ R) C
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have h : FOL.Context Peano.Axiom [H] H := FOL.Context.head [] H
  have hR : FOL.Context Peano.Axiom [H] (less R C) :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all R (succ R) C))
      (.closed (PeanoPowerTransition.self_less_succ R))) h
  have h0 : FOL.Context Peano.Axiom [H] (less zero C) :=
    .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all zero (succ R) C))
      (.closed (PeanoOrderTotality.zero_less_succ R))) h
  exact FOL.Context.conjunctionIntro hR h0


/-- Derive an arbitrary positive bounded divisor from the original
successor-indexed common-divisor clause. -/
theorem bounded_positive_divides :
    FormulaProves ((FOL.allAt 3 ((less (.var 3) (.var 0)).imp
        (divides (succ (.var 3)) (.var 2)))).imp
      ((less zero (.var 4)).imp
        ((less (.var 4) (succ (.var 0))).imp (divides (.var 4) (.var 2))))) := by
  let O := FOL.allAt 3 ((less (.var 3) (.var 0)).imp (divides (succ (.var 3)) (.var 2)))
  let E := (.var 4 : Peano.Term).equal (succ (.var 3))
  let P := less zero (.var 4)
  let L := less (.var 4) (succ (.var 0))
  let D := divides (.var 4) (.var 2)
  have hrow : FormulaProves (E.imp (O.imp (L.imp D))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have he : FOL.Context Peano.Axiom [L, O, E] E :=
      FOL.Context.under (FOL.Context.under (FOL.Context.head [] E) O) L
    have ho : FOL.Context Peano.Axiom [L, O, E] O :=
      FOL.Context.under (FOL.Context.head [E] O) L
    have hl : FOL.Context Peano.Axiom [L, O, E] L := FOL.Context.head _ _
    exact .mp (.mp (.mp (.closed bounded_predecessor_divides) ho) he) hl
  have hf : 3 ∉ (O.imp (L.imp D)).freeVarFinset := by decide
  have hex := PeanoBitPositionReduction.exists_elim 3 hf hrow
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ho : FOL.Context Peano.Axiom [L, P, O] O :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] O) P) L
  have hp : FOL.Context Peano.Axiom [L, P, O] P :=
    FOL.Context.under (FOL.Context.head [O] P) L
  have hl : FOL.Context Peano.Axiom [L, P, O] L := FOL.Context.head _ _
  have hpred : FOL.Context Peano.Axiom [L, P, O] (FOL.existsAt 3 E) := by
    have hp' := FOL.Context.mp (.closed (positive_has_predecessor (.var 4))) hp
    simpa only [predecessor_four_syntax, E] using hp'
  exact .mp (.mp (.mp (.closed hex) hpred) ho) hl

/-- Upgrade the fixed common-multiple matrix by demanding a successor of
its requested lower bound and converting its bounded divisor clause. -/
theorem body_upgrade : FormulaProves
    ((PeanoCommonMultiple.body (.var 0) (succ (.var 1)) (.var 2)).imp
      (positiveBody (.var 0) (.var 1) (.var 2))) := by
  let B := PeanoCommonMultiple.body (.var 0) (succ (.var 1)) (.var 2)
  let O := FOL.allAt 3 ((less (.var 3) (.var 0)).imp (divides (succ (.var 3)) (.var 2)))
  let P := less zero (.var 4)
  let L := less (.var 4) (succ (.var 0))
  let D := divides (.var 4) (.var 2)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hb : FOL.Context Peano.Axiom [B] B := FOL.Context.head [] B
  have hbound : FOL.Context Peano.Axiom [B] (less (succ (.var 1)) (.var 2)) :=
    FOL.Context.conjunctionLeft hb
  have hold : FOL.Context Peano.Axiom [B] O := FOL.Context.conjunctionRight hb
  have hnewbound : FOL.Context Peano.Axiom [B]
      ((less (.var 1) (.var 2)) ⊓ (less zero (.var 2))) :=
    .mp (.closed (strengthen_bound (.var 1) (.var 2))) hbound
  have hnew : FOL.Context Peano.Axiom [B] (FOL.allAt 4 (P.imp (L.imp D))) := by
    apply FOL.Context.generalize 4
    · intro ψ hψ
      have he : ψ = B := by simpa only [List.mem_singleton] using hψ
      subst ψ
      decide
    · exact .mp (.closed bounded_positive_divides) hold
  exact FOL.Context.conjunctionIntro (FOL.Context.conjunctionLeft hnewbound)
    (FOL.Context.conjunctionIntro (FOL.Context.conjunctionRight hnewbound) hnew)

private theorem common_succ_bound_syntax :
    commonMultiple (.var 0) (succ (.var 1)) = common (.var 0) (succ (.var 1)) := by
  simp [commonMultiple, commonTemplate, common, PeanoCommonMultiple.body, divides, dividesTemplate,
    FOL.existsAt, FOL.allAt, less, lessTemplate, exAt, v,
    Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- Construct the full fixed-name positive common multiple from the stronger
lower-bound instance of the already-proved PA common multiple. -/
theorem positive_common_vars : FormulaProves positiveTemplate := by
  let B := PeanoCommonMultiple.body (.var 0) (succ (.var 1)) (.var 2)
  let T := positiveTemplate
  have hi : FormulaProves ((positiveBody (.var 0) (.var 1) (.var 2)).imp T) := by
    simpa only [T, positiveTemplate, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom)
        (positiveBody (.var 0) (.var 1) (.var 2)) 2 (.var 2))
  have hbody : FormulaProves (B.imp T) := FOL.Derivation.compose body_upgrade hi
  have hf : 2 ∉ T.freeVarFinset := by decide
  have hex := PeanoBitPositionReduction.exists_elim 2 hf hbody
  have hcommon : FormulaProves (common (.var 0) (succ (.var 1))) := by
    have h := common_multiple_exists (.var 0) (succ (.var 1))
    rwa [common_succ_bound_syntax] at h
  exact .mp hex hcommon

private theorem positiveCommon_subst (n r : Peano.Term) (σ : Nat → Peano.Term) :
    (positiveCommon n r).subst σ = positiveCommon (n.subst σ) (r.subst σ) := by
  unfold positiveCommon
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1]

private theorem template_freeVars : positiveTemplate.freeVarFinset = {0,1} := by decide

private theorem template_as_positiveCommon : positiveCommon (.var 0) (.var 1) = positiveTemplate := by
  unfold positiveCommon
  calc
    positiveTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        positiveTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = positiveTemplate := SyntaxTransport.formula_subst_var _

private theorem specialize (n r : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (positiveCommon n r)) : FormulaProves (positiveCommon
      (n.subst (fun y => if y = name then t else .var y))
      (r.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (positiveCommon n r) name t))
    (.generalize name h)
  simpa only [FOL.substAt, positiveCommon_subst] using h₁

private theorem from_variables
    (hvar : FormulaProves (positiveCommon (.var 0) (.var 1))) (n r : Peano.Term) :
    FormulaProves (positiveCommon n r) := by
  let support := n.varFinset ∪ r.varFinset
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
  have h1 := specialize _ _ 0 (.var k) hvar
  have h1' : FormulaProves (positiveCommon (.var k) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (k+1)) h1'
  have h2' : FormulaProves (positiveCommon (.var k) (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 1 by omega] using h2
  have h3 := specialize _ _ k n h2'
  have h3' : FormulaProves (positiveCommon n (.var (k+1))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega] using h3
  have h4 := specialize _ _ (k+1) r h3'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+1) r hn] using h4

/-- For arbitrary terms N,R, PA proves that a positive C>R is divisible by
every positive d≤N. All term substitution is capture-safe. -/
theorem positive_common_exists (n r : Peano.Term) : FormulaProves (positiveCommon n r) := by
  have hvar : FormulaProves (positiveCommon (.var 0) (.var 1)) := by
    simpa only [template_as_positiveCommon] using positive_common_vars
  exact from_variables hvar n r

end PASoundness.PeanoCommonPositive
