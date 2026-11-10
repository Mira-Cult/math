import PASoundness.PeanoBetaUnique
import PASoundness.PeanoAddition

/-! Exact beta-trace transition extraction in the genuine PA calculus. -/
namespace PASoundness.PeanoPowerTransition
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- The literal two adjacent beta rows and their doubling equation. -/
def transitionBody (b c k : Peano.Term) (r s : Nat) : Peano.Formula :=
  (beta b c k (.var r)) ⊓
    ((beta b c (succ k) (.var s)) ⊓
      ((.var s : Peano.Term).equal (add (.var r) (.var r))))

/-- The two witnesses in a finite instance of the power-template's step. -/
def transition (b c k : Peano.Term) (r s : Nat) : Peano.Formula :=
  FOL.existsAt r (FOL.existsAt s (transitionBody b c k r s))

/-- A predecessor row whose doubled value is the specified endpoint. -/
def predecessor (b c k p : Peano.Term) (r : Nat) : Peano.Formula :=
  FOL.existsAt r ((beta b c k (.var r)) ⊓
    (p.equal (add (.var r) (.var r))))

/-- From an actual adjacent beta transition and an independently supplied
successor endpoint row, PA derives a predecessor row and equality with its
double. The displayed freshness conditions are syntactic eigenvariable
conditions on the exact conclusion, not semantic trace assumptions. -/
theorem transition_endpoint (b c k p : Peano.Term) (r s : Nat)
    (hfr : r ∉ ((beta b c (succ k) p).imp (predecessor b c k p r)).freeVarFinset)
    (hfs : s ∉ ((beta b c (succ k) p).imp (predecessor b c k p r)).freeVarFinset) :
    FormulaProves ((transition b c k r s).imp
      ((beta b c (succ k) p).imp (predecessor b c k p r))) := by
  let endpoint : Peano.Formula := beta b c (succ k) p
  let prior : Peano.Formula := predecessor b c k p r
  let step : Peano.Formula := transitionBody b c k r s
  have hrow : FormulaProves (step.imp (endpoint.imp prior)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hstep : FOL.Context Peano.Axiom [endpoint, step] step :=
      FOL.Context.under (FOL.Context.head [] step) endpoint
    have hend : FOL.Context Peano.Axiom [endpoint, step] endpoint := FOL.Context.head _ _
    have hprev : FOL.Context Peano.Axiom [endpoint, step] (beta b c k (.var r)) :=
      FOL.Context.conjunctionLeft hstep
    have hnext : FOL.Context Peano.Axiom [endpoint, step] (beta b c (succ k) (.var s)) :=
      FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hstep)
    have hdouble : FOL.Context Peano.Axiom [endpoint, step]
        ((.var s : Peano.Term).equal (add (.var r) (.var r))) :=
      FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hstep)
    have heq : FOL.Context Peano.Axiom [endpoint, step] (p.equal (.var s)) :=
      .mp (.mp (.closed (PeanoBetaUnique.beta_unique b c (succ k) p (.var s))) hend) hnext
    have hout : FOL.Context Peano.Axiom [endpoint, step]
        ((beta b c k (.var r)) ⊓ (p.equal (add (.var r) (.var r)))) :=
      FOL.Context.conjunctionIntro hprev (FOL.Context.eqTrans heq hdouble)
    have introPrior := FOL.Derivation.existsIntro (A := Peano.Axiom)
      ((beta b c k (.var r)) ⊓ (p.equal (add (.var r) (.var r)))) r (.var r)
    have hintro : FormulaProves
        (((beta b c k (.var r)) ⊓ (p.equal (add (.var r) (.var r)))).imp prior) := by
      simpa only [SyntaxTransport.substAt_self, prior, predecessor] using introPrior
    exact .mp (.closed hintro) hout
  have hₛ := PeanoBitPositionReduction.exists_elim s hfs hrow
  exact PeanoBitPositionReduction.exists_elim r hfr hₛ

/-- The literal power-template instance: code witnesses are variables 2 and 3,
the predecessor index is variable 0, the endpoint is variable 1, and the
transition witnesses are variables 5 and 6. -/
theorem transition_endpoint_literal :
    FormulaProves ((transition (.var 2) (.var 3) (.var 0) 5 6).imp
      ((beta (.var 2) (.var 3) (succ (.var 0)) (.var 1)).imp
        (predecessor (.var 2) (.var 3) (.var 0) (.var 1) 5))) := by
  apply transition_endpoint
  · decide
  · decide

private theorem self_less_succ_var_syntax :
    less (.var 0) (succ (.var 0)) =
      FOL.existsAt 5 ((add (.var 0) (succ (.var 5))).equal (succ (.var 0))) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.existsAt, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · congr 1
    funext i
    fin_cases i
    · rfl
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext j
      fin_cases j
      rfl
  · rfl

private theorem self_less_succ_var : FormulaProves (less (.var 0) (succ (.var 0))) := by
  rw [self_less_succ_var_syntax]
  let body : Peano.Formula := (add (.var 0) (succ (.var 5))).equal (succ (.var 0))
  have hs : FOL.substAt body 5 zero = (add (.var 0) (succ zero)).equal (succ (.var 0)) := by
    simp [FOL.substAt, body, FOL.equality_subst, add_subst, succ_subst,
      FirstOrder.Language.Term.subst]
  have h := FOL.Derivation.existsIntro (A := Peano.Axiom) body 5 zero
  rw [hs] at h
  exact .mp h (PeanoArithmetic.add_one (.var 0))

/-- PA derives the bound needed to select predecessor index `n` from the
literal trace of a claimed power at `S n`. -/
theorem self_less_succ (n : Peano.Term) : FormulaProves (less n (succ n)) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (less (.var 0) (succ (.var 0))) 0 n))
    (.generalize 0 self_less_succ_var)
  simpa [FOL.substAt, less_subst, succ_subst, FirstOrder.Language.Term.subst] using h

def boundedBody : Peano.Formula :=
  (less (.var 4) (succ (.var 0))).imp (transition (.var 2) (.var 3) (.var 4) 5 6)

theorem bounded_subst : FOL.substAt boundedBody 4 (.var 0) =
    ((less (.var 0) (succ (.var 0))).imp (transition (.var 2) (.var 3) (.var 0) 5 6)) := by
  simp [FOL.substAt, boundedBody, transition, transitionBody, FOL.existsAt, FOL.allAt,
    beta, betaTemplate, less, lessTemplate, modulus, exAt, v, Peano.add, Peano.mul, Peano.succ,
    Peano.zero, FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  all_goals try
    (congr 1; funext i; fin_cases i; congr 1; funext j; fin_cases j <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext k; fin_cases k; rfl))
  congr 1
  funext i
  fin_cases i
  congr 1
  funext j
  fin_cases j
  · simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  · rfl

/-- The exact bounded transition trace at upper index `S n` yields the
transition at index `n`. This uses PA's `n < S n` proof, not a semantic
evaluation of the bound. -/
theorem bounded_trace_transition :
    FormulaProves ((FOL.allAt 4 boundedBody).imp (transition (.var 2) (.var 3) (.var 0) 5 6)) := by
  have h₁ := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.allElim boundedBody 4 (.var 0))
  rw [bounded_subst] at h₁
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h₁) (FOL.Context.head [] _)) (.closed (self_less_succ (.var 0)))

/-- The exact bounded transition trace and successor endpoint beta row
produce a beta-coded predecessor whose double equals the endpoint. -/
theorem bounded_trace_endpoint :
    FormulaProves ((FOL.allAt 4 boundedBody).imp
      ((beta (.var 2) (.var 3) (succ (.var 0)) (.var 1)).imp
        (predecessor (.var 2) (.var 3) (.var 0) (.var 1) 5))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have htrace : FOL.Context Peano.Axiom
      [beta (.var 2) (.var 3) (succ (.var 0)) (.var 1), FOL.allAt 4 boundedBody]
      (transition (.var 2) (.var 3) (.var 0) 5 6) :=
    .mp (.closed bounded_trace_transition) (FOL.Context.under (FOL.Context.head [] _) _)
  exact .mp (.mp (.closed transition_endpoint_literal) htrace) (FOL.Context.head _ _)

def successorBody : Peano.Formula :=
  (beta (.var 2) (.var 3) zero (succ zero)) ⊓
    ((beta (.var 2) (.var 3) (succ (.var 0)) (.var 1)) ⊓ FOL.allAt 4 boundedBody)

def preservedBody : Peano.Formula :=
  (beta (.var 2) (.var 3) zero (succ zero)) ⊓
    ((predecessor (.var 2) (.var 3) (.var 0) (.var 1) 5) ⊓ FOL.allAt 4 boundedBody)

/-- Exact source-code witnesses, initial beta row, bounded trace, and an
existential doubled predecessor are all retained. -/
def positivePredecessor : Peano.Formula := FOL.existsAt 2 (FOL.existsAt 3 preservedBody)

private theorem successor_body_extract : FormulaProves (successorBody.imp positivePredecessor) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hbody : FOL.Context Peano.Axiom [successorBody] successorBody := FOL.Context.head [] _
  have hzero : FOL.Context Peano.Axiom [successorBody]
      (beta (.var 2) (.var 3) zero (succ zero)) := FOL.Context.conjunctionLeft hbody
  have htail := FOL.Context.conjunctionRight hbody
  have hend : FOL.Context Peano.Axiom [successorBody]
      (beta (.var 2) (.var 3) (succ (.var 0)) (.var 1)) := FOL.Context.conjunctionLeft htail
  have htrace : FOL.Context Peano.Axiom [successorBody] (FOL.allAt 4 boundedBody) :=
    FOL.Context.conjunctionRight htail
  have hprev : FOL.Context Peano.Axiom [successorBody]
      (predecessor (.var 2) (.var 3) (.var 0) (.var 1) 5) :=
    .mp (.mp (.closed bounded_trace_endpoint) htrace) hend
  have hpreserved : FOL.Context Peano.Axiom [successorBody] preservedBody :=
    FOL.Context.conjunctionIntro hzero (FOL.Context.conjunctionIntro hprev htrace)
  have intro₃ : FormulaProves (preservedBody.imp (FOL.existsAt 3 preservedBody)) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) preservedBody 3 (.var 3))
  have h₃ : FOL.Context Peano.Axiom [successorBody] (FOL.existsAt 3 preservedBody) :=
    .mp (.closed intro₃) hpreserved
  have intro₂ : FormulaProves ((FOL.existsAt 3 preservedBody).imp positivePredecessor) := by
    simpa only [SyntaxTransport.substAt_self, positivePredecessor] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 3 preservedBody) 2 (.var 2))
  exact .mp (.closed intro₂) h₃

theorem pow2_successor_syntax :
    pow2 (succ (.var 0)) (.var 1) = FOL.existsAt 2 (FOL.existsAt 3 successorBody) := by
  simp [pow2, pow2Template, successorBody, boundedBody, transition, transitionBody,
    FOL.existsAt, FOL.allAt, beta, betaTemplate, less, lessTemplate, modulus, exAt, v,
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
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  all_goals try
    (congr 1; funext i; fin_cases i; congr 1; funext j; fin_cases j <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext k; fin_cases k; rfl))
  all_goals try (congr 1; funext i; exact Fin.elim0 i)
  all_goals
    congr 1
    funext i
    fin_cases i
    congr 1
    funext j
    fin_cases j
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext k
      fin_cases k
      simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      all_goals
        congr 1
        funext z
        exact Fin.elim0 z
    · simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]

/-- From the literal beta-coded `pow2 (S n) p` formula, PA extracts beta-code
witnesses, the initial row, the entire original `k<S n` bounded trace, and an
existential row at `n` whose value doubles to `p`. The trace has not yet been
restricted from `k<S n` to `k<n`, so this theorem does not claim `pow2 n r`. -/
theorem power_successor_predecessor :
    FormulaProves ((pow2 (succ (.var 0)) (.var 1)).imp positivePredecessor) := by
  have hfresh3 : 3 ∉ positivePredecessor.freeVarFinset := by decide
  have h₃ := PeanoBitPositionReduction.exists_elim 3 hfresh3 successor_body_extract
  have hfresh2 : 2 ∉ positivePredecessor.freeVarFinset := by decide
  have h₂ := PeanoBitPositionReduction.exists_elim 2 hfresh2 h₃
  rw [pow2_successor_syntax]
  exact h₂

end PASoundness.PeanoPowerTransition
