import PASoundness.PAtoCompactScopedAddZeroEquality
import PASoundness.PAtoCompactGuardedOutputReplacement

/-! Draft scoped equality adapter for guard-conditioned output transport.
The graph laws remain explicit finite K proof inputs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGuardedOutputEquality
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactSuccSubstSyntax PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactScopedAddZeroEquality PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactGuardedOutputReplacement

/-- Scoped equality alignment for any replacement with the two displayed
finite K graph laws. Source tags distinguish free variables from bound
levels even when their interpreted labels alias. -/
noncomputable def scoped_equal_of_replacement {n : Nat}
    (g : Formula) (replacement : Peano.Term) (x q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ replacement.varFinset, a < d)
    (hdom : ∀ a ∈ replacement.varFinset,
      KDerivation (imp g.encode (domainAt d a).encode))
    (output : GuardedOutputTransport g replacement) (functional : GuardFunctionality g replacement)
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat) :
    GuardedBoth (retained g replacement q d)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst
        (singleSubst x (.var q))) bound)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst
        (singleSubst x replacement)) bound) := by
  classical
  let σ := singleSubst x (.var q)
  let τ := singleSubst x replacement
  let select : Nat ⊕ Fin n → Prop := fun a => a = Sum.inl x
  let name : Nat ⊕ Fin n → Nat := Sum.elim id bound
  let mapσ : Nat ⊕ Fin n → Peano.Term := fun a => if select a then .var q else .var (name a)
  let mapτ : Nat ⊕ Fin n → Peano.Term := fun a => if select a then replacement else .var (name a)
  have heσ : Sum.elim σ (Term.var ∘ bound) = mapσ := by
    funext a
    cases a with
    | inl a => simp [σ, singleSubst, mapσ, select, name]
    | inr i => simp [σ, mapσ, select, name]
  have heτ : Sum.elim τ (Term.var ∘ bound) = mapτ := by
    funext a
    cases a with
    | inl a => simp [τ, singleSubst, mapτ, select, name]
    | inr i => simp [τ, mapτ, select, name]
  apply scoped_equal_of_graph_align (retained g replacement q d) σ τ s t bound
  · intro b out hout hH hs ht
    rw [heσ] at hs
    rw [heτ] at ht
    rw [heσ, heτ]
    exact PAtoCompactGuardedOutputReplacement.selected_substitution select name g replacement q d hqd htd hdom output functional
      s b out hout hH hs ht
  · intro b out hout hH hs ht
    rw [heσ] at hs
    rw [heτ] at ht
    rw [heσ, heτ]
    exact PAtoCompactGuardedOutputReplacement.selected_substitution select name g replacement q d hqd htd hdom output functional
      t b out hout hH hs ht

end PASoundness.PAtoCompactGuardedOutputEquality
#print axioms PASoundness.PAtoCompactGuardedOutputEquality.scoped_equal_of_replacement
