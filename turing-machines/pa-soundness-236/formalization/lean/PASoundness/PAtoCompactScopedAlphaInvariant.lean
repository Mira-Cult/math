import PASoundness.PAtoCompactFreeNames
import PASoundness.CompactFreshen
import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactFreeVacuity

/-! The generated term graph depends on a variable-name function only at
the variables occurring in the source term. This is literal syntactic
invariance, not alpha-conversion of different binder blocks. -/
namespace PASoundness.PAtoCompactScopedAlphaInvariant

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactFreeVacuity

/-- If two name assignments agree on the source term's variables, their
generated graphs are literally equal at every output and allocator base. -/
theorem termGraph_name_agree {α : Type} [DecidableEq α]
    (t : Peano.language.Term α) (f g : α → Nat)
    (h : ∀ v ∈ t.varFinset, f v = g v) : ∀ out base,
    termGraph f t out base = termGraph g t out base := by
  induction t with
  | var v =>
      intro out base
      have hv : f v = g v := h v (by simp [Term.varFinset])
      simp [termGraph, hv]
  | @func l sym ts ih =>
      have hc (i : Fin l) : ∀ v ∈ (ts i).varFinset, f v = g v := by
        intro v hv
        apply h v
        simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hv⟩
      cases sym with
      | zero => intro out base; rfl
      | succ =>
          intro out base
          simp only [termGraph]
          rw [ih 0 (hc 0)]
      | add =>
          intro out base
          simp only [termGraph]
          rw [ih 0 (hc 0), ih 1 (hc 1)]
      | mul =>
          intro out base
          simp only [termGraph]
          rw [ih 0 (hc 0), ih 1 (hc 1)]

/-- The same invariance yields finite bidirectional K proof data directly. -/
def termGraph_name_agree_proof {α : Type} [DecidableEq α]
    (t : Peano.language.Term α) (f g : α → Nat)
    (h : ∀ v ∈ t.varFinset, f v = g v) (out base : Nat) :
    ProofEquiv (termGraph f t out base) (termGraph g t out base) := by
  rw [termGraph_name_agree t f g h out base]
  exact ProofEquiv.refl _

/-- Source-variable relabeling does not change the reserved graph size. -/
theorem termCost_relabel {α β : Type} (t : Peano.language.Term α) (r : α → β) :
    termCost (t.relabel r) = termCost t := by
  induction t with
  | var v => rfl
  | @func l sym ts ih =>
      cases sym with
      | zero => rfl
      | succ => simp [Term.relabel, termCost, ih 0]
      | add => simp [Term.relabel, termCost, ih 0, ih 1]
      | mul => simp [Term.relabel, termCost, ih 0, ih 1]

/-- Relabeling source variables and then interpreting the new names gives
the same literal term graph as composing the relabeling into its name map. -/
theorem termGraph_relabel {α β : Type} (t : Peano.language.Term α)
    (r : α → β) (g : β → Nat) : ∀ out base,
    termGraph g (t.relabel r) out base = termGraph (g ∘ r) t out base := by
  induction t with
  | var v => intro out base; rfl
  | @func l sym ts ih =>
      cases sym with
      | zero => intro out base; rfl
      | succ =>
          intro out base
          simp only [Term.relabel, termGraph]
          rw [ih 0]
      | add =>
          intro out base
          simp only [Term.relabel, termGraph, termCost_relabel]
          rw [ih 0, ih 1]
      | mul =>
          intro out base
          simp only [Term.relabel, termGraph, termCost_relabel]
          rw [ih 0, ih 1]

/-- Separated scopes never contain nested shadowing of a chosen name. -/
theorem separated_noShadow (f : Formula) (h : Separated f) (x : Nat) :
    NoShadow x f := by
  induction f with
  | truth | bottom | member | equal => trivial
  | imp a b ia ib =>
      exact ⟨ia h.1, ib h.2.1⟩
  | all z a ih | ex z a ih =>
      refine ⟨?_, ih h.1⟩
      intro hzx
      simpa [hzx] using h.2

/-- Every binder allocated by freshening is absent from the result's free
names, because all original names lie strictly below the allocation start. -/
theorem freshened_binder_not_free (f : Formula) (start : Nat)
    (hn : ∀ v ∈ f.names, v < start) (x : Nat)
    (hx : x ∈ (freshen f start hn).formula.binders) :
    x ∉ (freshen f start hn).formula.free := by
  intro hf
  have hsource := freshen_free_subset f start hn hf
  have hlt := hn x (Formula.free_subset_names f hsource)
  have hge := (freshen f start hn).binders_ge x hx
  omega

/-- One arbitrary freshly allocated binder can be moved to a new name with
actual K proof data. Iterating such moves and matching a target translation
remain separate obligations. -/
def freshened_binder_alpha (f : Formula) (start : Nat)
    (hn : ∀ v ∈ f.names, v < start) (x y : Nat)
    (hx : x ∈ (freshen f start hn).formula.binders)
    (hxy : x ≠ y) (hy : y ∉ (freshen f start hn).formula.names) :
    ProofEquiv (freshen f start hn).formula
      (mapNames (rename x y) (freshen f start hn).formula) :=
  alpha_map_one x y _ hxy (freshened_binder_not_free f start hn x hx) hy
    (separated_noShadow _ (freshen f start hn).separated x)

end PASoundness.PAtoCompactScopedAlphaInvariant

#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.termGraph_name_agree
#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.termGraph_name_agree_proof
#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.termCost_relabel
#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.termGraph_relabel
#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.separated_noShadow
#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.freshened_binder_not_free
#print axioms PASoundness.PAtoCompactScopedAlphaInvariant.freshened_binder_alpha
