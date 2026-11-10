import PASoundness.PAtoCompactGuardedAllElim
import PASoundness.PAtoCompactGuardedEqualityReflexivityUnary
import PASoundness.PAtoCompactGuardedModusPonensTransport

/-! Bounded guarded universal-elimination families whose substitution results
are reflexive unary atoms. This does not establish general substitution
compatibility or cover general equality atoms. -/
namespace PASoundness.PAtoCompactAllElimVariableAtom

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedModusPonensTransport
open PASoundness.PAtoCompactGuardedEqualityReflexivityUnary PASoundness.PAtoCompactUnaryTermTransport

/-- A guarded proof of the consequent proves a guarded implication, after
transporting its free-variable guards to the implication's guard. -/
def guarded_consequent (φ ψ : Peano.Formula) (d : KDerivation (guardedCode ψ)) :
    KDerivation (guardedCode (φ.imp ψ)) := by
  have hs : ψ.freeVarFinset ⊆ (φ.imp ψ).freeVarFinset := by
    intro x hx
    simp [BoundedFormula.freeVarFinset, hx]
  have hg := guardFormula_transport_subset ψ (φ.imp ψ) hs
  have hp := compose hg d
  have hw := weakening (code ψ) (code φ)
  simpa only [guardedCode, code_imp] using compose hp hw

theorem self_atom_subst (x : Nat) (t : Peano.Term) :
    FOL.substAt (((.var x : Peano.Term).equal (.var x))) x t = t.equal t := by
  simp [FOL.substAt, FOL.equality_subst, Term.subst]

/-- Substitution of a unary term into a unary term remains in the unary
fragment. The evidence is Type-valued, as in the existing graph-totality proof. -/
noncomputable def unary_subst (x : Nat) {s : Peano.Term} (h : UnaryTerm s)
    (t : Peano.Term) (ht : UnaryTerm t) :
    UnaryTerm (s.subst (fun y => if y = x then t else .var y)) := by
  induction h with
  | var a =>
      by_cases ha : a = x
      · simpa [Term.subst, ha] using ht
      · simpa [Term.subst, ha] using UnaryTerm.var a
  | zero =>
      convert (UnaryTerm.zero : UnaryTerm (Peano.zero)) using 1
      simp only [Term.subst]
      congr 1
      funext i
      exact Fin.elim0 i
  | @succ s h ih =>
      convert UnaryTerm.succ ih using 1
      simp only [Term.subst]
      congr 1
      funext i
      fin_cases i
      rfl

theorem reflexive_atom_subst (x : Nat) (s t : Peano.Term) :
    FOL.substAt (s.equal s) x t =
      (s.subst (fun y => if y = x then t else .var y)).equal
        (s.subst (fun y => if y = x then t else .var y)) := by
  simp [FOL.substAt, FOL.equality_subst]

/-- Every universal-elimination leaf whose source is a reflexive unary term
atom and whose substitution term is unary has a finite K proof. -/
noncomputable def unary_reflexive_atom (x : Nat) (s : Peano.Term) (hs : UnaryTerm s)
    (t : Peano.Term) (ht : UnaryTerm t) :
    KDerivation (guardedCode ((FOL.allAt x (s.equal s)).imp
      (FOL.substAt (s.equal s) x t))) := by
  rw [reflexive_atom_subst]
  exact guarded_consequent _ _ (unary_reflexivity _ (unary_subst x hs t ht))

theorem unary_reflexive_atom_certificate (x : Nat) (s : Peano.Term) (hs : UnaryTerm s)
    (t : Peano.Term) (ht : UnaryTerm t) :
    theoremCode (certificate (unary_reflexive_atom x s hs t ht)) =
      guardedCode ((FOL.allAt x (s.equal s)).imp
        (FOL.substAt (s.equal s) x t)) := certificate_correct _

/-- The source equality may be non-reflexive: substituting y for x in x=y
makes the consequent y=y, including the case in which x equals y. -/
noncomputable def variable_atom_to_reflexive (x y : Nat) :
    KDerivation (guardedCode
      ((FOL.allAt x ((.var x : Peano.Term).equal (.var y))).imp
        (FOL.substAt ((.var x : Peano.Term).equal (.var y)) x (.var y)))) := by
  have hsubst :
      FOL.substAt ((.var x : Peano.Term).equal (.var y)) x (.var y) =
        ((.var y : Peano.Term).equal (.var y)) := by
    simp [FOL.substAt, FOL.equality_subst, Term.subst]
  rw [hsubst]
  exact guarded_consequent _ _ (unary_reflexivity (.var y) (.var y))

/-- If t is built from zero, successor and variables, the actual guarded PA
universal-elimination leaf for x=x is derivable in K. -/
noncomputable def unary_term_self_atom (x : Nat) (t : Peano.Term) (h : UnaryTerm t) :
    KDerivation (guardedCode ((FOL.allAt x ((.var x : Peano.Term).equal (.var x))).imp
      (FOL.substAt ((.var x : Peano.Term).equal (.var x)) x t))) := by
  rw [self_atom_subst]
  exact guarded_consequent _ _ (unary_reflexivity t h)

theorem unary_term_self_atom_certificate (x : Nat) (t : Peano.Term) (h : UnaryTerm t) :
    theoremCode (certificate (unary_term_self_atom x t h)) =
      guardedCode ((FOL.allAt x ((.var x : Peano.Term).equal (.var x))).imp
        (FOL.substAt ((.var x : Peano.Term).equal (.var x)) x t)) := certificate_correct _

end PASoundness.PAtoCompactAllElimVariableAtom

#print axioms PASoundness.PAtoCompactAllElimVariableAtom.guarded_consequent
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.self_atom_subst
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.unary_subst
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.reflexive_atom_subst
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.unary_reflexive_atom
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.unary_reflexive_atom_certificate
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.variable_atom_to_reflexive
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.unary_term_self_atom
#print axioms PASoundness.PAtoCompactAllElimVariableAtom.unary_term_self_atom_certificate
