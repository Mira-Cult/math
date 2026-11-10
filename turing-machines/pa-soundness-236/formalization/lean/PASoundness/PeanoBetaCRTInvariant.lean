import PASoundness.PeanoBetaCRTBaseExists

/-! A fixed-name bounded CRT invariant in the PA calculus. It is compatible
with the existential zero-prefix base. The conditional transition wrapper
requires the three code/product updates as separate PA derivations; it does not
prove those updates, their simultaneous existence, or bounded CRT. -/
namespace PASoundness.PeanoBetaCRTInvariant
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility

/-- Processed-row condition. Index 2 and value 3 are bound together, so the
same value satisfies φ and the beta row. Parameter C is name 1. -/
def rowsAt (φ : Peano.Formula) (k : Peano.Term) (b : Nat) : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) k).imp
    (FOL.existsAt 3 (φ ⊓ beta (.var b) (.var 1) (.var 2) (.var 3))))

/-- Every processed modulus divides product P. -/
def factorsAt (k : Peano.Term) (p : Nat) : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) k).imp (divides (modulus (.var 1) (.var 2)) (.var p)))

/-- Every index j with k≤j<N has an inverse certificate for product P.
The non-strict lower bound is encoded as ¬(j<k); N is free name 8. -/
def futureAt (k : Peano.Term) (p : Nat) : Peano.Formula :=
  FOL.allAt 2 ((((less (.var 2) k).not) ⊓ less (.var 2) (.var 8)).imp
    (FOL.existsAt 3 (FOL.existsAt 4
      ((mul (.var p) (.var 3)).equal
        (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))))

def matrixAt (φ : Peano.Formula) (k : Peano.Term) (b p : Nat) : Peano.Formula :=
  (rowsAt φ k b ⊓ factorsAt k p) ⊓ futureAt k p

/-- Existential code/product invariant parameterized by its two witness names.
Callers must choose names fresh in φ and outside the fixed parameter, index and
inverse-witness names. In this module the bound k is only 0, name 7, or S(name
7), so the fixed inner binders 2,3,4 do not capture it. -/
def invariantWith (φ : Peano.Formula) (k : Peano.Term) (b p : Nat) : Peano.Formula :=
  FOL.existsAt p (FOL.existsAt b (matrixAt φ k b p))

/-- The current invariant uses B=9, P=10, k=7, N=8 and C=1. -/
def invariantAt (φ : Peano.Formula) (k : Peano.Term) : Peano.Formula :=
  invariantWith φ k 9 10

def currentMatrix (φ : Peano.Formula) : Peano.Formula := matrixAt φ (.var 7) 9 10

def currentInvariant (φ : Peano.Formula) : Peano.Formula := invariantAt φ (.var 7)

/-- Updated witness names 11 and 12 are fresh relative to all fixed binders.
No particular update terms are assumed by this definition. -/
def nextRows (φ : Peano.Formula) : Peano.Formula := rowsAt φ (succ (.var 7)) 11
def nextFactors : Peano.Formula := factorsAt (succ (.var 7)) 12
def nextFuture : Peano.Formula := futureAt (succ (.var 7)) 12

def nextMatrix (φ : Peano.Formula) : Peano.Formula :=
  (nextRows φ ⊓ nextFactors) ⊓ nextFuture

def nextInvariant (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 12 (FOL.existsAt 11 (nextMatrix φ))

/-- The next invariant is the same parameterized schema with fresh witness
names. Equality with the current 9/10 naming is a separate alpha-renaming
obligation, not used as an induction shortcut. -/
theorem next_invariant_schema (φ : Peano.Formula) :
    nextInvariant φ = invariantWith φ (succ (.var 7)) 11 12 := rfl

/-- The unguarded future inverse family at the literal zero-prefix base
implies the guarded family for any outer bound N. -/
theorem base_future_weaken : FormulaProves
    (PeanoBetaCRTBaseExists.futureClause.imp (futureAt zero 10)) := by
  let A := PeanoBetaCRTBaseExists.futureClause
  let G := ((less (.var 2) zero).not) ⊓ less (.var 2) (.var 8)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have he : ψ = A := by simpa using hψ
    subst ψ
    simp [A, PeanoBetaCRTBaseExists.futureClause, SyntaxTransport.allAt_freeVars]
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom [G,A] A :=
    FOL.Context.under (FOL.Context.head [] A) G
  have h := FOL.Context.allSelf (show FOL.Context Peano.Axiom [G,A]
    (FOL.allAt 2 (FOL.existsAt 3 (FOL.existsAt 4
      ((mul (.var 10) (.var 3)).equal
        (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))))))) from ha)
  exact h

/-- The reviewed existential zero-prefix base entails this invariant at zero.
No equality between `invariantAt φ 0` and a substitution into the induction
template is asserted here. -/
theorem base_to_zero_invariant (φ : Peano.Formula) : FormulaProves
    ((PeanoBetaCRTBaseExists.baseExists φ).imp (invariantAt φ zero)) := by
  let B := PeanoBetaCRTBaseExists.baseMatrix φ
  let T := invariantAt φ zero
  have hbody : FormulaProves (B.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hb : FOL.Context Peano.Axiom [B] B := FOL.Context.head [] B
    have hcomponents := FOL.Context.conjunctionRight hb
    have hrow := FOL.Context.conjunctionLeft (FOL.Context.conjunctionLeft hcomponents)
    have hdiv := FOL.Context.conjunctionRight (FOL.Context.conjunctionLeft hcomponents)
    have hbase := FOL.Context.conjunctionRight hcomponents
    have hfuture : FOL.Context Peano.Axiom [B] (futureAt zero 10) :=
      .mp (.closed base_future_weaken) hbase
    have hm : FOL.Context Peano.Axiom [B] (matrixAt φ zero 9 10) :=
      FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro hrow hdiv) hfuture
    have hi9 : FormulaProves ((matrixAt φ zero 9 10).imp
        (FOL.existsAt 9 (matrixAt φ zero 9 10))) := by
      simpa only [SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (matrixAt φ zero 9 10) 9 (.var 9))
    have hi10 : FormulaProves ((FOL.existsAt 9 (matrixAt φ zero 9 10)).imp T) := by
      simpa only [T, invariantAt, invariantWith, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom)
          (FOL.existsAt 9 (matrixAt φ zero 9 10)) 10 (.var 10))
    exact .mp (.closed hi10) (.mp (.closed hi9) hm)
  have hf9 : 9 ∉ T.freeVarFinset := by
    simp [T, invariantAt, invariantWith, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset]
  have hf10 : 10 ∉ T.freeVarFinset := by
    simp [T, invariantAt, invariantWith, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset]
  have h9 := PeanoBitPositionReduction.exists_elim 9 hf9 hbody
  have h10 := PeanoBitPositionReduction.exists_elim 10 hf10 h9
  simpa only [PeanoBetaCRTBaseExists.baseExists, B] using h10

/-- Closed PA zero-prefix invariant, retaining the relation's parameters.
Names 7,9,10 are excluded from φ for later induction and existential binding. -/
theorem zero_invariant (φ : Peano.Formula)
    (_hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) : FormulaProves (invariantAt φ zero) :=
  .mp (base_to_zero_invariant φ)
    (PeanoBetaCRTBaseExists.base_exists φ hφ9 hφ10)

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

/-- Introduce both proposed output witnesses, allowing the second witness to
mention the first output name. The PA derivation of the fully substituted new
invariant is supplied explicitly. -/
theorem introduce_pair (current next : Peano.Formula) (newB newP : Nat)
    (b p : Peano.Term)
    (hUpdate : FormulaProves (current.imp
      (FOL.substAt (FOL.substAt next newP p) newB b))) :
    FormulaProves (current.imp (FOL.existsAt newB (FOL.existsAt newP next))) := by
  let A := FOL.substAt next newP p
  let T := FOL.existsAt newP next
  have hi : FormulaProves (A.imp T) := FOL.Derivation.existsIntro next newP p
  have hs := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (A.imp T) newB b))
    (.generalize newB hi)
  have hiB : FormulaProves ((FOL.substAt A newB b).imp (FOL.substAt T newB b)) := by
    simpa only [FOL.substAt, subst_imp] using hs
  have hTarget : FormulaProves ((FOL.substAt T newB b).imp (FOL.existsAt newB T)) :=
    FOL.Derivation.existsIntro T newB b
  exact FOL.Derivation.compose (FOL.Derivation.compose hUpdate hiB) hTarget

/-- A proof of an update for explicitly named current witnesses yields a
transformation from existence of the current pair to existence of a new pair.
Freshness excludes the current witness names from the final existential target;
all update obligations are retained in the supplied PA derivation. -/
theorem exists_pair_update (current next : Peano.Formula)
    (oldB oldP newB newP : Nat) (b p : Peano.Term)
    (hfB : oldB ∉ (FOL.existsAt newB (FOL.existsAt newP next)).freeVarFinset)
    (hfP : oldP ∉ (FOL.existsAt newB (FOL.existsAt newP next)).freeVarFinset)
    (hUpdate : FormulaProves (current.imp
      (FOL.substAt (FOL.substAt next newP p) newB b))) :
    FormulaProves ((FOL.existsAt oldB (FOL.existsAt oldP current)).imp
      (FOL.existsAt newB (FOL.existsAt newP next))) := by
  have hi := introduce_pair current next newB newP b p hUpdate
  have heP := PeanoBitPositionReduction.exists_elim oldP hfP hi
  exact PeanoBitPositionReduction.exists_elim oldB hfB heP


/-- A contextual version retains an object-level PA side condition outside
the existential update. The old witness names must be fresh in the side
condition and in the target; the full update remains a supplied PA proof. -/
theorem exists_pair_update_under (assumptions current next : Peano.Formula)
    (oldB oldP newB newP : Nat) (b p : Peano.Term)
    (haB : oldB ∉ assumptions.freeVarFinset)
    (haP : oldP ∉ assumptions.freeVarFinset)
    (hfB : oldB ∉ (FOL.existsAt newB (FOL.existsAt newP next)).freeVarFinset)
    (hfP : oldP ∉ (FOL.existsAt newB (FOL.existsAt newP next)).freeVarFinset)
    (hUpdate : FormulaProves (assumptions.imp (current.imp
      (FOL.substAt (FOL.substAt next newP p) newB b)))) :
    FormulaProves (assumptions.imp ((FOL.existsAt oldB (FOL.existsAt oldP current)).imp
      (FOL.existsAt newB (FOL.existsAt newP next)))) := by
  let T := FOL.existsAt newB (FOL.existsAt newP next)
  have hc : FormulaProves ((assumptions ⊓ current).imp
      (FOL.substAt (FOL.substAt next newP p) newB b)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have h : FOL.Context Peano.Axiom [assumptions ⊓ current] (assumptions ⊓ current) :=
      FOL.Context.head [] _
    exact .mp (.mp (.closed hUpdate) (FOL.Context.conjunctionLeft h)) (FOL.Context.conjunctionRight h)
  have hi := introduce_pair (assumptions ⊓ current) next newB newP b p hc
  have hswap : FormulaProves (current.imp (assumptions.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hc : FOL.Context Peano.Axiom [assumptions,current] current :=
      FOL.Context.under (FOL.Context.head [] current) assumptions
    have ha : FOL.Context Peano.Axiom [assumptions,current] assumptions := FOL.Context.head _ _
    exact .mp (.closed hi) (FOL.Context.conjunctionIntro ha hc)
  have hfrB : oldB ∉ (assumptions.imp T).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset, T] using And.intro haB hfB
  have hfrP : oldP ∉ (assumptions.imp T).freeVarFinset := by
    simpa [FirstOrder.Language.BoundedFormula.freeVarFinset, T] using And.intro haP hfP
  have heP := PeanoBitPositionReduction.exists_elim oldP hfrP hswap
  have heB := PeanoBitPositionReduction.exists_elim oldB hfrB heP
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Q := FOL.existsAt oldB (FOL.existsAt oldP current)
  have ha : FOL.Context Peano.Axiom [Q,assumptions] assumptions :=
    FOL.Context.under (FOL.Context.head [] assumptions) Q
  have hq : FOL.Context Peano.Axiom [Q,assumptions] Q := FOL.Context.head _ _
  exact .mp (.mp (.closed heB) hq) ha


private theorem substAt_both (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t ⊓ FOL.substAt ψ x t) := by
  rfl

/-- Logical packaging for three independently proved next-invariant components.
The new formula is exactly `((rows ⊓ divisors) ⊓ future)`. It introduces
P first, then B, matching substitution of B and then P. Each object-level
update is a separate explicit PA-derivation premise; nothing in this wrapper
establishes those updates, bounded CRT, or the induction step by itself. -/
theorem exists_pair_update_components (assumptions current rows divisors future : Peano.Formula)
    (oldB oldP newB newP : Nat) (b p : Peano.Term)
    (haB : oldB ∉ assumptions.freeVarFinset)
    (haP : oldP ∉ assumptions.freeVarFinset)
    (hfB : oldB ∉ (FOL.existsAt newP (FOL.existsAt newB ((rows ⊓ divisors) ⊓ future))).freeVarFinset)
    (hfP : oldP ∉ (FOL.existsAt newP (FOL.existsAt newB ((rows ⊓ divisors) ⊓ future))).freeVarFinset)
    (hRows : FormulaProves (assumptions.imp (current.imp
      (FOL.substAt (FOL.substAt rows newB b) newP p))))
    (hDivisors : FormulaProves (assumptions.imp (current.imp
      (FOL.substAt (FOL.substAt divisors newB b) newP p))))
    (hFuture : FormulaProves (assumptions.imp (current.imp
      (FOL.substAt (FOL.substAt future newB b) newP p)))) :
    FormulaProves (assumptions.imp ((FOL.existsAt oldB (FOL.existsAt oldP current)).imp
      (FOL.existsAt newP (FOL.existsAt newB ((rows ⊓ divisors) ⊓ future))))) := by
  let Γ := [current, assumptions]
  have hUpdate : FormulaProves (assumptions.imp (current.imp
      (FOL.substAt (FOL.substAt ((rows ⊓ divisors) ⊓ future) newB b) newP p))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have ha : FOL.Context Peano.Axiom Γ assumptions :=
      FOL.Context.under (FOL.Context.head [] assumptions) current
    have hc : FOL.Context Peano.Axiom Γ current := FOL.Context.head _ _
    have hr := FOL.Context.mp (FOL.Context.mp (.closed hRows) ha) hc
    have hd := FOL.Context.mp (FOL.Context.mp (.closed hDivisors) ha) hc
    have hf := FOL.Context.mp (FOL.Context.mp (.closed hFuture) ha) hc
    have hconj := FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro hr hd) hf
    simpa only [substAt_both] using hconj
  exact exists_pair_update_under assumptions current ((rows ⊓ divisors) ⊓ future)
    oldB oldP newP newB p b haB haP hfB hfP hUpdate


private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- Conditional successor packaging for the fixed CRT invariant. The three
supplied PA derivations must establish the updated rows, factors and future
inverse clauses with the *same* explicit output witness terms `b` and `p`.
The side condition may contain the induction bound and external parameters,
but must not depend on the old existential code or product names. The output
witness terms are required to avoid the new bound names 11,12. Relating the
output back to invariantAt with names 9,10,
and proving the component updates, are separate obligations. -/
theorem conditional_successor (φ assumptions : Peano.Formula) (b p : Peano.Term)
    (_hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) (_hφ11 : 11 ∉ φ.freeVarFinset)
    (_hφ12 : 12 ∉ φ.freeVarFinset)
    (_hb11 : 11 ∉ b.varFinset) (_hb12 : 12 ∉ b.varFinset)
    (_hp11 : 11 ∉ p.varFinset) (_hp12 : 12 ∉ p.varFinset)
    (ha9 : 9 ∉ assumptions.freeVarFinset) (ha10 : 10 ∉ assumptions.freeVarFinset)
    (hRows : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt (nextRows φ) 11 b) 12 p))))
    (hFactors : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFactors 11 b) 12 p))))
    (hFuture : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFuture 11 b) 12 p)))) :
    FormulaProves (assumptions.imp ((currentInvariant φ).imp (nextInvariant φ))) := by
  have hf9 : 9 ∉ (nextInvariant φ).freeVarFinset := by
    have ha : 9 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
    have hb : 9 ∉ (beta (.var 11) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
    have hc : 9 ∉ (divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by decide
    have hd : 9 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
    have he : 9 ∉ (((mul (.var 12) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by decide
    simp [nextInvariant, nextMatrix, nextRows, nextFactors, nextFuture, rowsAt,
      factorsAt, futureAt, fv_exists, fv_inf, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hφ9, ha, hb, hc, hd, he]
  have hf10 : 10 ∉ (nextInvariant φ).freeVarFinset := by
    have ha : 10 ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by decide
    have hb : 10 ∉ (beta (.var 11) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
    have hc : 10 ∉ (divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by decide
    have hd : 10 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
    have he : 10 ∉ (((mul (.var 12) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by decide
    simp [nextInvariant, nextMatrix, nextRows, nextFactors, nextFuture, rowsAt,
      factorsAt, futureAt, fv_exists, fv_inf, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hφ10, ha, hb, hc, hd, he]
  exact exists_pair_update_components assumptions (currentMatrix φ)
    (nextRows φ) nextFactors nextFuture 10 9 11 12 b p
    ha10 ha9 hf10 hf9 hRows hFactors hFuture

end PASoundness.PeanoBetaCRTInvariant
