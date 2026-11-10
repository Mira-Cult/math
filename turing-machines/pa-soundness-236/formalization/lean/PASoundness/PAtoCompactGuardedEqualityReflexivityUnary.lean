import PASoundness.PAtoCompactUnaryGuardedCanonical
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactCandidateDynamicReflexivity
import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.PAtoCompactSuccTermTotality

/-! Guarded equality reflexivity from a shared graph witness. The two
occurrences need not be functional: both existential value names can denote
the same witness. This module constructs K proof data only. -/
namespace PASoundness.PAtoCompactGuardedEqualityReflexivityUnary

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactCandidateDynamicReflexivity PASoundness.PAtoCompactSuccTermTotality

theorem both_not_binders (t : Peano.Term) (b : Nat) :
    b ∉ (matrix id t t b (b+1) (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost t)).binders ∧
    b+1 ∉ (matrix id t t b (b+1) (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost t)).binders := by
  constructor <;> intro hm <;>
    simp only [matrix, andF_binders, Finset.mem_union] at hm <;>
    rcases hm with ht | hu | he
  · have h := termGraph_binder_range id t b (b+2) b ht; omega
  · have h := termGraph_binder_range id t (b+1) (b+2+termCost t) b hu; omega
  · have h := equivAt_private (b+2+termCost t+termCost t) b (b+1) b he; omega
  · have h := termGraph_binder_range id t b (b+2) (b+1) ht; omega
  · have h := termGraph_binder_range id t (b+1) (b+2+termCost t) (b+1) hu; omega
  · have h := equivAt_private (b+2+termCost t+termCost t) b (b+1) (b+1) he; omega

theorem matrix_replace_second (t : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) :
    replace (b+1) b (matrix id t t b (b+1) (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost t)) =
    matrix id t t b b (b+2) (b+2+termCost t)
      (b+2+termCost t+termCost t) := by
  rw [matrix_replace_fresh_source id t t b (b+1) (b+2) (b+2+termCost t)
    (b+2+termCost t+termCost t) (b+1) b (by omega) (by omega) (by omega)
    (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
    (by intro a ha; have := ht a ha; simp only [id_eq]; omega)]
  simp [rename]

/-- A graph value supplies both copies of the graph, rebased to their
separate private blocks, and its candidate guard supplies self-equivalence. -/
noncomputable def graph_to_diagonal (t : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) :
    KDerivation (imp (termGraph id t b (b+2)).encode
      (matrix id t t b b (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost t)).encode) := by
  have hg := termGraph_base_transport id t (b+2) (b+2+termCost t) b
    (by omega) (by omega) (by intro a ha; simp only [id_eq]; have := ht a ha; omega)
    (by intro a ha; simp only [id_eq]; have := ht a ha; omega)
  let e := b+2+termCost t+termCost t
  have hdom := compose (termGraph_domain id t b (b+2))
    (domainAt_transport (b+2) e b (by omega) (by dsimp [e]; omega))
  have he := compose hdom (dynamic_reflexive e b (by dsimp [e]; omega))
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(termGraph id t b (b+2)).encode]
  have h1 : Context Γ (termGraph id t b (b+2)).encode := Context.head [] _
  have h2 : Context Γ (termGraph id t b (b+2+termCost t)).encode := .mp h1 (.closed hg.1)
  have h3 : Context Γ (equivAt e b b).encode := .mp h1 (.closed he)
  have hp := Context.conjunctionIntro h2 h3
  have hq := Context.conjunctionIntro h1 hp
  simpa [matrix, e, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hq

/-- The second equality value can use the same object as the first. -/
noncomputable def graph_to_inner (t : Peano.Term) (b : Nat)
    (ht : ∀ a ∈ t.varFinset, a < b) :
    KDerivation (imp (termGraph id t b (b+2)).encode
      (existsCode (b+1) (matrix id t t b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost t)).encode)) := by
  have hi := exists_from_instance (b+1) b
    (matrix id t t b (b+1) (b+2) (b+2+termCost t) (b+2+termCost t+termCost t))
    (by omega) (both_not_binders t b).2 (both_not_binders t b).1
  rw [matrix_replace_second t b ht] at hi
  exact compose (graph_to_diagonal t b ht) hi

theorem guard_scope (t : Peano.Term) :
    guardBase (t.equal t) = scopeBase (t.equal t) Fin.elim0 := by
  simp [guardBase, scopeBase]

theorem term_coverage (t : Peano.Term) :
    ∀ a ∈ t.varFinset, (id : Nat → Nat) a ∈ (t.equal t).freeVarFinset := by
  intro a ha
  simpa [eq_free] using ha

theorem name_bound (t : Peano.Term) (a : Nat) (ha : a ∈ t.varFinset) :
    a < scopeBase (t.equal t) Fin.elim0 := by
  apply free_lt_scopeBase (t.equal t) Fin.elim0 a
  exact term_coverage t a ha

/-- Any supplied K graph-existence proof yields the corresponding guarded
equality-reflexivity axiom. The witnesses share one object, so functionality
is not needed. -/
noncomputable def reflexivity_of_graph_total (t : Peano.Term)
    (hv : KDerivation (imp (guardFormula (t.equal t)).encode
      (existsCode (scopeBase (t.equal t) Fin.elim0)
        (termGraph id t (scopeBase (t.equal t) Fin.elim0)
          (scopeBase (t.equal t) Fin.elim0 + 2)).encode))) :
    KDerivation (guardedCode (t.equal t)) := by
  let b := scopeBase (t.equal t) Fin.elim0
  have ht : ∀ a ∈ t.varFinset, a < b := by
    intro a ha
    exact name_bound t a ha
  have he := existsCongr b (graph_to_inner t b ht)
  have hfinal := compose hv he
  unfold guardedCode code
  rw [original_shape]
  change KDerivation (imp (guardFormula (t.equal t)).encode
    (existsCode b (existsCode (b+1)
      (matrix id t t b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost t)).encode)))
  exact hfinal

/-- Guarded PA equality reflexivity for every term built from variables, zero
and successor. The two graph outputs may denote the same object; no graph
functionality or soundness theorem is used. -/
noncomputable def unary_reflexivity (t : Peano.Term) (h : UnaryTerm t) :
    KDerivation (guardedCode (t.equal t)) := by
  apply reflexivity_of_graph_total
  have hv := PAtoCompactUnaryGuardedCanonical.unary_total id (t.equal t) h (term_coverage t)
  simpa only [PAtoCompactUnaryGuardedCanonical.outputName,
    PAtoCompactUnaryGuardedCanonical.allocatorBase, guard_scope] using hv

theorem unary_reflexivity_certificate (t : Peano.Term) (h : UnaryTerm t) :
    theoremCode (certificate (unary_reflexivity t h)) = guardedCode (t.equal t) :=
  certificate_correct _

end PASoundness.PAtoCompactGuardedEqualityReflexivityUnary

#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityUnary.unary_reflexivity
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityUnary.reflexivity_of_graph_total
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityUnary.unary_reflexivity_certificate
