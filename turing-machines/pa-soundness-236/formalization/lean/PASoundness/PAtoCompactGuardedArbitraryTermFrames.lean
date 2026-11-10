import PASoundness.PAtoCompactTermSubstInduction
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactGuardedExistsCongruence
import PASoundness.PAtoCompactScopedEqualityReplace

/-! Common-base equality matrix and frame congruence from arbitrary retained-
guard term-graph alignments. No term substitution or alignment is assumed to
exist: both input alignments are actual finite K derivations. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGuardedArbitraryTermFrames
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTermSubstInduction PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactGuardedExistsCongruence

/-- The two graph alignments are supplied at the first matrix's graph bases.
The right graph and quotient are transported to the other matrix's cost-based
allocations inside K. -/
noncomputable def guarded_matrix_alignment
    (H : Formula) (a₁ a₂ b₁ b₂ : Peano.Term) (b : Nat)
    (h₂ : ∀ a ∈ b₂.varFinset, a < b)
    (hleft : Align H a₁ b₁ (b+2) b)
    (hright : Align H a₂ b₂ (b+2+termCost a₁) (b+1)) :
    let A := matrix id a₁ a₂ b (b+1) (b+2) (b+2+termCost a₁) (b+2+termCost a₁+termCost a₂)
    let B := matrix id b₁ b₂ b (b+1) (b+2) (b+2+termCost b₁) (b+2+termCost b₁+termCost b₂)
    KDerivation (imp H.encode (imp A.encode B.encode)) ×
      KDerivation (imp H.encode (imp B.encode A.encode)) := by
  dsimp only
  let p := b+2
  let qa := b+2+termCost a₁
  let qb := b+2+termCost b₁
  let ea := qa+termCost a₂
  let eb := qb+termCost b₂
  let A₁ := (termGraph id a₁ b p).encode
  let A₂ := (termGraph id a₂ (b+1) qa).encode
  let B₁ := (termGraph id b₁ b p).encode
  let B₂ := (termGraph id b₂ (b+1) qb).encode
  let E₁ := (equivAt ea b (b+1)).encode
  let E₂ := (equivAt eb b (b+1)).encode
  have hmove := termGraph_base_transport id b₂ qa qb (b+1)
    (by dsimp [qa]; omega) (by dsimp [qb]; omega)
    (by intro a ha; simp only [id_eq]; have := h₂ a ha; dsimp [qa]; omega)
    (by intro a ha; simp only [id_eq]; have := h₂ a ha; dsimp [qb]; omega)
  have heq := equivAt_base_alpha ea eb b (b+1)
    (by dsimp [ea,qa]; omega) (by dsimp [ea,qa]; omega)
    (by dsimp [eb,qb]; omega) (by dsimp [eb,qb]; omega)
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both A₁ (both A₂ E₁),H.encode]
    have ha : Context Γ (both A₁ (both A₂ E₁)) := Context.head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have h1 : Context Γ B₁ := .mp (Context.conjunctionLeft ha) (.mp hh (.closed hleft.1))
    have h2' : Context Γ (termGraph id b₂ (b+1) qa).encode :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight ha)) (.mp hh (.closed hright.1))
    have h2 : Context Γ B₂ := .mp h2' (.closed hmove.1)
    have he : Context Γ E₂ := .mp (Context.conjunctionRight (Context.conjunctionRight ha)) (.closed heq.forward)
    change Context Γ (both B₁ (both B₂ E₂))
    exact Context.conjunctionIntro h1 (Context.conjunctionIntro h2 he)
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both B₁ (both B₂ E₂),H.encode]
    have hb : Context Γ (both B₁ (both B₂ E₂)) := Context.head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have h1 : Context Γ A₁ := .mp (Context.conjunctionLeft hb) (.mp hh (.closed hleft.2))
    have h2' : Context Γ (termGraph id b₂ (b+1) qa).encode :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight hb)) (.closed hmove.2)
    have h2 : Context Γ A₂ := .mp h2' (.mp hh (.closed hright.2))
    have he : Context Γ E₁ := .mp (Context.conjunctionRight (Context.conjunctionRight hb)) (.closed heq.backward)
    change Context Γ (both A₁ (both A₂ E₁))
    exact Context.conjunctionIntro h1 (Context.conjunctionIntro h2 he)

/-- Neither of the two allocated value labels is rebound inside an equality
matrix, regardless of the terms or their graph costs. -/
theorem matrix_value_not_binder (a b : Peano.Term) (base k : Nat) (hk : k < base+2) :
    k ∉ (matrix id a b base (base+1) (base+2) (base+2+termCost a)
      (base+2+termCost a+termCost b)).binders := by
  simp only [matrix, andF_binders, Finset.mem_union, not_or]
  refine ⟨termGraph_below_not_binder id a base (base+2) k (by omega),
    termGraph_below_not_binder id b (base+1) (base+2+termCost a) k (by omega), ?_⟩
  intro h
  have hp := equivAt_private (base+2+termCost a+termCost b) base (base+1) k h
  omega

/-- Both equality frames are aligned, assuming the guard's free names are
below the common base and the two displayed graph alignments exist. -/
noncomputable def guarded_frame_alignment
    (H : Formula) (a₁ a₂ b₁ b₂ : Peano.Term) (b : Nat)
    (hH : ∀ a ∈ H.free, a < b) (h₂ : ∀ a ∈ b₂.varFinset, a < b)
    (hleft : Align H a₁ b₁ (b+2) b)
    (hright : Align H a₂ b₂ (b+2+termCost a₁) (b+1)) :
    KDerivation (imp H.encode (imp (equalityFrame id a₁ a₂ b).encode (equalityFrame id b₁ b₂ b).encode)) ×
      KDerivation (imp H.encode (imp (equalityFrame id b₁ b₂ b).encode (equalityFrame id a₁ a₂ b).encode)) := by
  let A := matrix id a₁ a₂ b (b+1) (b+2) (b+2+termCost a₁) (b+2+termCost a₁+termCost a₂)
  let B := matrix id b₁ b₂ b (b+1) (b+2) (b+2+termCost b₁) (b+2+termCost b₁+termCost b₂)
  have hm := guarded_matrix_alignment H a₁ a₂ b₁ b₂ b h₂ hleft hright
  have hv₀ : b ∉ H.free := by intro h; have := hH b h; omega
  have hv₁ : b+1 ∉ H.free := by intro h; have := hH (b+1) h; omega
  have hia : b+1 ∉ A.binders := matrix_value_not_binder a₁ a₂ b (b+1) (by omega)
  have hib : b+1 ∉ B.binders := matrix_value_not_binder b₁ b₂ b (b+1) (by omega)
  have hi := exists_both_of_free (b+1) H A B hv₁ hia hib hm.1 hm.2
  have hoa : b ∉ (Formula.ex (b+1) A).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨by omega, matrix_value_not_binder a₁ a₂ b b (by omega)⟩
  have hob : b ∉ (Formula.ex (b+1) B).binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨by omega, matrix_value_not_binder b₁ b₂ b b (by omega)⟩
  have ho := exists_both_of_free b H (.ex (b+1) A) (.ex (b+1) B) hv₀ hoa hob hi.1 hi.2
  simpa only [equalityFrame, Formula.encode, matrix, A, B] using ho

end PASoundness.PAtoCompactGuardedArbitraryTermFrames

#print axioms PASoundness.PAtoCompactGuardedArbitraryTermFrames.guarded_matrix_alignment
#print axioms PASoundness.PAtoCompactGuardedArbitraryTermFrames.matrix_value_not_binder
#print axioms PASoundness.PAtoCompactGuardedArbitraryTermFrames.guarded_frame_alignment
