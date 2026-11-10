import PASoundness.PAtoCompactSelectedSuccessorEqualityMatrix
import PASoundness.PAtoCompactGuardedExistsCongruence
import PASoundness.PAtoCompactScopedEqualityReplace

/-! Successor substitution through the two existential witnesses of a PA
equality frame at a common allocator base. Both substituted equality terms may
be arbitrary; all retained-guard and source-name bounds remain explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSelectedSuccessorEqualityFrame
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactTermSubstSuccessorInduction
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactGuardedExistsCongruence PASoundness.PAtoCompactSelectedSuccessorEqualityMatrix

/-- Neither allocated equality witness is rebound within the matrix, for any
two PA terms and either of the witness labels. -/
theorem selected_matrix_witness_not_binder (a b : Peano.Term) (base k : Nat) (hk : k < base+2) :
    k ∉ (matrix id a b base (base+1) (base+2) (base+2+termCost a)
      (base+2+termCost a+termCost b)).binders := by
  simp only [matrix, andF_binders, Finset.mem_union, not_or]
  refine ⟨termGraph_below_not_binder id a base (base+2) k (by omega),
    termGraph_below_not_binder id b (base+1) (base+2+termCost a) k (by omega), ?_⟩
  intro h
  have hp := equivAt_private (base+2+termCost a+termCost b) base (base+1) k h
  omega

/-- Both K implications between equality frames after replacing the selected
source variables by q and by S(u), respectively, at the same base. The fixed retained guard includes an
explicit graph for S(u) at q; candidate proofs for u's variables are inputs. -/
noncomputable def selected_equality_frame_alignment
    {α : Type} [DecidableEq α] (selected : α → Prop) [DecidablePred selected]
    (name : α → Nat) (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (s₁ s₂ : Peano.language.Term α) (b : Nat)
    (hH : ∀ a ∈ (retained g u q d).free, a < b)
    (h₁v : ∀ a ∈ (s₁.subst (fun a => if selected a then .var q else .var (name a))).varFinset, a < b)
    (h₁s : ∀ a ∈ (s₁.subst (fun a => if selected a then succTerm u else .var (name a))).varFinset, a < b)
    (h₂v : ∀ a ∈ (s₂.subst (fun a => if selected a then .var q else .var (name a))).varFinset, a < b)
    (h₂s : ∀ a ∈ (s₂.subst (fun a => if selected a then succTerm u else .var (name a))).varFinset, a < b) :
    let H := retained g u q d
    let a₁ := s₁.subst (fun a => if selected a then .var q else .var (name a))
    let a₂ := s₂.subst (fun a => if selected a then .var q else .var (name a))
    let b₁ := s₁.subst (fun a => if selected a then succTerm u else .var (name a))
    let b₂ := s₂.subst (fun a => if selected a then succTerm u else .var (name a))
    KDerivation (imp H.encode (imp (equalityFrame id a₁ a₂ b).encode (equalityFrame id b₁ b₂ b).encode)) ×
      KDerivation (imp H.encode (imp (equalityFrame id b₁ b₂ b).encode (equalityFrame id a₁ a₂ b).encode)) := by
  dsimp only
  let H := retained g u q d
  let a₁ := s₁.subst (fun a => if selected a then .var q else .var (name a))
  let a₂ := s₂.subst (fun a => if selected a then .var q else .var (name a))
  let b₁ := s₁.subst (fun a => if selected a then succTerm u else .var (name a))
  let b₂ := s₂.subst (fun a => if selected a then succTerm u else .var (name a))
  let A := matrix id a₁ a₂ b (b+1) (b+2) (b+2+termCost a₁) (b+2+termCost a₁+termCost a₂)
  let B := matrix id b₁ b₂ b (b+1) (b+2) (b+2+termCost b₁) (b+2+termCost b₁+termCost b₂)
  have hm := selected_equality_matrix_alignment selected name g u hu q d hqd hud hdom s₁ s₂ b hH h₁v h₁s h₂v h₂s
  have hv₀ : b ∉ H.free := by intro h; have := hH b h; omega
  have hv₁ : b+1 ∉ H.free := by intro h; have := hH (b+1) h; omega
  have hia : b+1 ∉ A.binders := selected_matrix_witness_not_binder a₁ a₂ b (b+1) (by omega)
  have hib : b+1 ∉ B.binders := selected_matrix_witness_not_binder b₁ b₂ b (b+1) (by omega)
  have hi := exists_both_of_free (b+1) H A B hv₁ hia hib hm.1 hm.2
  have hoa : b ∉ (Formula.ex (b+1) A).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨by omega, selected_matrix_witness_not_binder a₁ a₂ b b (by omega)⟩
  have hob : b ∉ (Formula.ex (b+1) B).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨by omega, selected_matrix_witness_not_binder b₁ b₂ b b (by omega)⟩
  have ho := exists_both_of_free b H (.ex (b+1) A) (.ex (b+1) B) hv₀ hoa hob hi.1 hi.2
  simpa only [equalityFrame, Formula.encode, matrix, A, B] using ho

end PASoundness.PAtoCompactSelectedSuccessorEqualityFrame

#print axioms PASoundness.PAtoCompactSelectedSuccessorEqualityFrame.selected_matrix_witness_not_binder
#print axioms PASoundness.PAtoCompactSelectedSuccessorEqualityFrame.selected_equality_frame_alignment
