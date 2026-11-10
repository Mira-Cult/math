import PASoundness.PeanoBetaCRTAlpha
import PASoundness.PeanoBetaCRTPrefixSubst

/-! Conditional literal induction instances for the bounded CRT invariant.
The three update derivations and their side condition remain explicit premises.
This module does not prove the updates, unguarded induction, or bounded CRT. -/
namespace PASoundness.PeanoBetaCRTInductionBridge
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic
open PeanoBetaCRTInvariant

/-- PA derives the literal induction base for the fixed-name invariant. -/
theorem literal_base (φ : Peano.Formula)
    (hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) :
    FormulaProves (FOL.substAt (currentInvariant φ) 7 zero) := by
  simpa only [currentInvariant, PeanoBetaCRTPrefixSubst.invariant_zero φ hφ7] using
    (zero_invariant φ hφ7 hφ9 hφ10)

/-- The literal successor instance follows if three separate PA derivations
supply the updated rows, factors, and future inverse family, all with the same
capture-safe output terms. The side condition is retained, and may depend on
k=name 7. No component update is proved by this wrapper. -/
theorem literal_step (φ assumptions : Peano.Formula) (b p : Peano.Term)
    (hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) (hφ11 : 11 ∉ φ.freeVarFinset)
    (hφ12 : 12 ∉ φ.freeVarFinset)
    (hb11 : 11 ∉ b.varFinset) (hb12 : 12 ∉ b.varFinset)
    (hp11 : 11 ∉ p.varFinset) (hp12 : 12 ∉ p.varFinset)
    (ha9 : 9 ∉ assumptions.freeVarFinset) (ha10 : 10 ∉ assumptions.freeVarFinset)
    (hRows : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt (nextRows φ) 11 b) 12 p))))
    (hFactors : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFactors 11 b) 12 p))))
    (hFuture : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFuture 11 b) 12 p)))) :
    FormulaProves (assumptions.imp ((currentInvariant φ).imp
      (FOL.substAt (currentInvariant φ) 7 (succ (.var 7))))) := by
  have hstep := conditional_successor φ assumptions b p
    hφ7 hφ9 hφ10 hφ11 hφ12 hb11 hb12 hp11 hp12 ha9 ha10 hRows hFactors hFuture
  have halpha := PeanoBetaCRTAlpha.alpha_next φ hφ9 hφ10 hφ11 hφ12
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have ha : FOL.Context Peano.Axiom [currentInvariant φ, assumptions] assumptions :=
    FOL.Context.under (FOL.Context.head [] assumptions) (currentInvariant φ)
  have hi : FOL.Context Peano.Axiom [currentInvariant φ, assumptions] (currentInvariant φ) :=
    FOL.Context.head _ _
  have hn : FOL.Context Peano.Axiom [currentInvariant φ, assumptions] (nextInvariant φ) :=
    .mp (.mp (.closed hstep) ha) hi
  have hs : FOL.Context Peano.Axiom [currentInvariant φ, assumptions]
      (invariantAt φ (succ (.var 7))) := .mp (.closed halpha) hn
  simpa only [currentInvariant, PeanoBetaCRTPrefixSubst.invariant_succ φ hφ7] using hs

/-- Universally generalizing the conditional step retains a potentially
k-dependent side condition inside the quantifier. It is not an unguarded PA
induction step and does not assert that the side condition holds. -/
theorem literal_step_all (φ assumptions : Peano.Formula) (b p : Peano.Term)
    (hφ7 : 7 ∉ φ.freeVarFinset) (hφ9 : 9 ∉ φ.freeVarFinset)
    (hφ10 : 10 ∉ φ.freeVarFinset) (hφ11 : 11 ∉ φ.freeVarFinset)
    (hφ12 : 12 ∉ φ.freeVarFinset)
    (hb11 : 11 ∉ b.varFinset) (hb12 : 12 ∉ b.varFinset)
    (hp11 : 11 ∉ p.varFinset) (hp12 : 12 ∉ p.varFinset)
    (ha9 : 9 ∉ assumptions.freeVarFinset) (ha10 : 10 ∉ assumptions.freeVarFinset)
    (hRows : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt (nextRows φ) 11 b) 12 p))))
    (hFactors : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFactors 11 b) 12 p))))
    (hFuture : FormulaProves (assumptions.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFuture 11 b) 12 p)))) :
    FormulaProves (FOL.allAt 7 (assumptions.imp ((currentInvariant φ).imp
      (FOL.substAt (currentInvariant φ) 7 (succ (.var 7)))))) :=
  .generalize 7 (literal_step φ assumptions b p hφ7 hφ9 hφ10 hφ11 hφ12
    hb11 hb12 hp11 hp12 ha9 ha10 hRows hFactors hFuture)

end PASoundness.PeanoBetaCRTInductionBridge
