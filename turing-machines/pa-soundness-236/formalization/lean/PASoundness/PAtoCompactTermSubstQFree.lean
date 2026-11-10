import PASoundness.PAtoCompactVacuousQuantifierFree
import PASoundness.PAtoCompactGuardedLogicalCongruence

/-! Conditional compound-term substitution for quantifier-free PA formulas.
The retained hypothesis can contain a graph witness and its guards. Equality
leaves remain explicit finite K proof data; this is not a graph-substitution
or arithmetic soundness theorem. -/
namespace PASoundness.PAtoCompactTermSubstQFree

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactGuardedLogicalCongruence

/-- A fixed hypothesis suffices for both directions of each equality leaf.
The variable `q` may already occur freely in a leaf: no freshness condition is
hidden in this interface. -/
abbrev EqualityAlignment (H : Formula) (x q : Nat) (t : Peano.Term) : Type :=
  ∀ s u : Peano.Term,
    GuardedBoth H (formula (FOL.substAt (s.equal u) x (.var q)))
      (formula (FOL.substAt (s.equal u) x t))

/-- Proof data only for the actual equality leaves of the selected formula.
In particular a guard need not cover the variables of unrelated atoms. -/
inductive LeafAlignment (H : Formula) (x q : Nat) (t : Peano.Term) :
    {φ : Peano.Formula} → QuantifierFree φ → Type
  | falsum : LeafAlignment H x q t QuantifierFree.falsum
  | equal (s u : Peano.Term) :
      GuardedBoth H (formula (FOL.substAt (s.equal u) x (.var q)))
        (formula (FOL.substAt (s.equal u) x t)) →
      LeafAlignment H x q t (QuantifierFree.equal s u)
  | imp {φ ψ : Peano.Formula} {hφ : QuantifierFree φ} {hψ : QuantifierFree ψ} :
      LeafAlignment H x q t hφ → LeafAlignment H x q t hψ →
      LeafAlignment H x q t (QuantifierFree.imp hφ hψ)

/-- Extend the source-specific leaf proofs under the same hypothesis. -/
noncomputable def qfree_substitution_local (H : Formula) (x q : Nat) (t : Peano.Term)
    (φ : Peano.Formula) (hf : QuantifierFree φ) (atoms : LeafAlignment H x q t hf) :
    GuardedBoth H (formula (FOL.substAt φ x (.var q)))
      (formula (FOL.substAt φ x t)) := by
  induction atoms with
  | falsum =>
      constructor <;> apply Context.closeEmpty <;> apply Context.deduction <;>
        exact .closed (identity _)
  | equal s u h => exact h
  | @imp φ ψ hφ hψ ha hb iha ihb =>
      change GuardedBoth H
        (.imp (formula (FOL.substAt φ x (.var q)))
          (formula (FOL.substAt ψ x (.var q))))
        (.imp (formula (FOL.substAt φ x t))
          (formula (FOL.substAt ψ x t)))
      exact guarded_implication _ _ _ _ _ iha ihb

theorem qfree_substitution_local_forward_certificate (H : Formula) (x q : Nat) (t : Peano.Term)
    (φ : Peano.Formula) (hf : QuantifierFree φ) (atoms : LeafAlignment H x q t hf) :
    theoremCode (certificate (qfree_substitution_local H x q t φ hf atoms).1) =
      imp H.encode (imp (formula (FOL.substAt φ x (.var q))).encode
        (formula (FOL.substAt φ x t)).encode) := certificate_correct _

theorem qfree_substitution_local_backward_certificate (H : Formula) (x q : Nat) (t : Peano.Term)
    (φ : Peano.Formula) (hf : QuantifierFree φ) (atoms : LeafAlignment H x q t hf) :
    theoremCode (certificate (qfree_substitution_local H x q t φ hf atoms).2) =
      imp H.encode (imp (formula (FOL.substAt φ x t)).encode
        (formula (FOL.substAt φ x (.var q))).encode) := certificate_correct _

/-- An equality-leaf family extends to every quantifier-free formula under
the same retained hypothesis. Implication uses the reverse child direction in
its antecedent. This does not construct the equality-leaf family. -/
noncomputable def qfree_substitution (H : Formula) (x q : Nat) (t : Peano.Term)
    (atoms : EqualityAlignment H x q t)
    (φ : Peano.Formula) (hf : QuantifierFree φ) :
    GuardedBoth H (formula (FOL.substAt φ x (.var q)))
      (formula (FOL.substAt φ x t)) := by
  induction hf with
  | falsum =>
      constructor <;> apply Context.closeEmpty <;> apply Context.deduction <;>
        exact .closed (identity _)
  | equal s u => exact atoms s u
  | @imp φ ψ hφ hψ ihφ ihψ =>
      change GuardedBoth H
        (.imp (formula (FOL.substAt φ x (.var q)))
          (formula (FOL.substAt ψ x (.var q))))
        (.imp (formula (FOL.substAt φ x t))
          (formula (FOL.substAt ψ x t)))
      exact guarded_implication _ _ _ _ _ ihφ ihψ

theorem qfree_substitution_forward_certificate (H : Formula) (x q : Nat) (t : Peano.Term)
    (atoms : EqualityAlignment H x q t) (φ : Peano.Formula) (hf : QuantifierFree φ) :
    theoremCode (certificate (qfree_substitution H x q t atoms φ hf).1) =
      imp H.encode (imp (formula (FOL.substAt φ x (.var q))).encode
        (formula (FOL.substAt φ x t)).encode) := certificate_correct _

theorem qfree_substitution_backward_certificate (H : Formula) (x q : Nat) (t : Peano.Term)
    (atoms : EqualityAlignment H x q t) (φ : Peano.Formula) (hf : QuantifierFree φ) :
    theoremCode (certificate (qfree_substitution H x q t atoms φ hf).2) =
      imp H.encode (imp (formula (FOL.substAt φ x t)).encode
        (formula (FOL.substAt φ x (.var q))).encode) := certificate_correct _

end PASoundness.PAtoCompactTermSubstQFree

#print axioms PASoundness.PAtoCompactTermSubstQFree.qfree_substitution
#print axioms PASoundness.PAtoCompactTermSubstQFree.qfree_substitution_local
#print axioms PASoundness.PAtoCompactTermSubstQFree.qfree_substitution_local_forward_certificate
#print axioms PASoundness.PAtoCompactTermSubstQFree.qfree_substitution_local_backward_certificate
#print axioms PASoundness.PAtoCompactTermSubstQFree.qfree_substitution_forward_certificate
#print axioms PASoundness.PAtoCompactTermSubstQFree.qfree_substitution_backward_certificate
