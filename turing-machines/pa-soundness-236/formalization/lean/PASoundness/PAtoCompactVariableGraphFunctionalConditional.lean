import PASoundness.PAtoCompactTermTranslation
import PASoundness.CompactDerivations

/-! Variable-graph functionality as a finite K proof transformer. The quotient
symmetry and transitivity proofs are explicit inputs. This module does not
establish those inputs or functionality for composite arithmetic terms. -/
namespace PASoundness.PAtoCompactVariableGraphFunctionalConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation

/-- Two outputs of the same variable graph are quotient-equivalent, conditional
on the exact candidate-relative symmetry and transitivity derivations shown.
The derivation makes no syntactic freshness claim; any conditions required for
the inputs are the responsibility of the caller. -/
def variable_graph_functional {α : Type} (v : α → Nat) (a : α)
    (base x y : Nat)
    (sym : KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) x).encode (equivAt base x (v a)).encode)))
    (trans : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v a)).encode
        (imp (equivAt base (v a) y).encode (equivAt base x y).encode)))) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (termGraph v (.var a) x base).encode
        (imp (termGraph v (.var a) y base).encode (equivAt base x y).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := (domainAt base (v a)).encode
  let X := (termGraph v (.var a) x base).encode
  let Y := (termGraph v (.var a) y base).encode
  let Γ := [Y, X, A]
  have hd : Context Γ A := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := Context.head _ _
  have hdx : Context Γ (domainAt base x).encode := Context.conjunctionLeft hx
  have hex : Context Γ (equivAt base (v a) x).encode := Context.conjunctionRight hx
  have hey : Context Γ (equivAt base (v a) y).encode := Context.conjunctionRight hy
  have hrev := Context.mp hex (Context.mp hd (Context.closed sym))
  exact .mp hey (.mp hrev (.mp hdx (.closed trans)))

theorem variable_graph_functional_certificate {α : Type} (v : α → Nat) (a : α)
    (base x y : Nat)
    (sym : KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) x).encode (equivAt base x (v a)).encode)))
    (trans : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v a)).encode
        (imp (equivAt base (v a) y).encode (equivAt base x y).encode)))) :
    theoremCode (certificate (variable_graph_functional v a base x y sym trans)) =
      imp (domainAt base (v a)).encode
        (imp (termGraph v (.var a) x base).encode
          (imp (termGraph v (.var a) y base).encode (equivAt base x y).encode)) :=
  certificate_correct _

/-- Changing the source variable name from a to a quotient-equivalent b
preserves the quotient class of graph outputs. Both variable graphs and the
input equivalence are consumed. The three displayed K implications are
explicit inputs; no graph existence or quotient laws are assumed implicitly. -/
def variable_graph_congruence {α : Type} (v : α → Nat) (a b : α)
    (base x y : Nat)
    (sym : KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) x).encode (equivAt base x (v a)).encode)))
    (trans₁ : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v a)).encode
        (imp (equivAt base (v a) (v b)).encode (equivAt base x (v b)).encode))))
    (trans₂ : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v b)).encode
        (imp (equivAt base (v b) y).encode (equivAt base x y).encode)))) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) (v b)).encode
        (imp (termGraph v (.var a) x base).encode
          (imp (termGraph v (.var b) y base).encode (equivAt base x y).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := (domainAt base (v a)).encode
  let E := (equivAt base (v a) (v b)).encode
  let X := (termGraph v (.var a) x base).encode
  let Y := (termGraph v (.var b) y base).encode
  let Γ := [Y, X, E, A]
  have hd : Context Γ A := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := Context.head _ _
  have hdx : Context Γ (domainAt base x).encode := Context.conjunctionLeft hx
  have hex : Context Γ (equivAt base (v a) x).encode := Context.conjunctionRight hx
  have hey : Context Γ (equivAt base (v b) y).encode := Context.conjunctionRight hy
  have hrev := Context.mp hex (Context.mp hd (Context.closed sym))
  have hxb := Context.mp he (Context.mp hrev (Context.mp hdx (Context.closed trans₁)))
  exact .mp hey (.mp hxb (.mp hdx (.closed trans₂)))

theorem variable_graph_congruence_certificate {α : Type} (v : α → Nat) (a b : α)
    (base x y : Nat)
    (sym : KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) x).encode (equivAt base x (v a)).encode)))
    (trans₁ : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v a)).encode
        (imp (equivAt base (v a) (v b)).encode (equivAt base x (v b)).encode))))
    (trans₂ : KDerivation (imp (domainAt base x).encode
      (imp (equivAt base x (v b)).encode
        (imp (equivAt base (v b) y).encode (equivAt base x y).encode)))) :
    theoremCode (certificate (variable_graph_congruence v a b base x y sym trans₁ trans₂)) =
      imp (domainAt base (v a)).encode
        (imp (equivAt base (v a) (v b)).encode
          (imp (termGraph v (.var a) x base).encode
            (imp (termGraph v (.var b) y base).encode (equivAt base x y).encode))) :=
  certificate_correct _

end PASoundness.PAtoCompactVariableGraphFunctionalConditional

#print axioms PASoundness.PAtoCompactVariableGraphFunctionalConditional.variable_graph_functional
#print axioms PASoundness.PAtoCompactVariableGraphFunctionalConditional.variable_graph_functional_certificate
#print axioms PASoundness.PAtoCompactVariableGraphFunctionalConditional.variable_graph_congruence
#print axioms PASoundness.PAtoCompactVariableGraphFunctionalConditional.variable_graph_congruence_certificate
