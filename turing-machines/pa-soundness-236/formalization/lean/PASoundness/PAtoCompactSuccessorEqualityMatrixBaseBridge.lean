import PASoundness.PAtoCompactTermSubstSuccessorInduction
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Finite K alignment of the equality matrices for successor substitution,
including the graph and equivalence block changes caused by differing term costs.
The existential equality frames and their allocated value labels are not yet
aligned here. All guard, graph and name bounds are explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorEqualityMatrixBaseBridge
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactTermSubstInduction PASoundness.PAtoCompactTermSubstSuccessorInduction
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactVacuousEqualityAlignment

/-- Both equality matrices use witness names b,b+1. The right graph and quotient
blocks differ because the two substituted terms need not have the same cost.
The retained guard contains the graph of the substituted successor at q. -/
noncomputable def equality_matrix_alignment
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (s₁ s₂ : Peano.Term) (b : Nat)
    (hH : ∀ a ∈ (retained g u q d).free, a < b)
    (h₁v : ∀ a ∈ (s₁.subst (variableSubst x q)).varFinset, a < b)
    (h₁s : ∀ a ∈ (s₁.subst (successorSubst x u)).varFinset, a < b)
    (h₂v : ∀ a ∈ (s₂.subst (variableSubst x q)).varFinset, a < b)
    (h₂s : ∀ a ∈ (s₂.subst (successorSubst x u)).varFinset, a < b) :
    let H := retained g u q d
    let a₁ := s₁.subst (variableSubst x q)
    let a₂ := s₂.subst (variableSubst x q)
    let b₁ := s₁.subst (successorSubst x u)
    let b₂ := s₂.subst (successorSubst x u)
    let av := matrix id a₁ a₂ b (b+1) (b+2) (b+2+termCost a₁) (b+2+termCost a₁+termCost a₂)
    let bs := matrix id b₁ b₂ b (b+1) (b+2) (b+2+termCost b₁) (b+2+termCost b₁+termCost b₂)
    KDerivation (imp H.encode (imp av.encode bs.encode)) ×
      KDerivation (imp H.encode (imp bs.encode av.encode)) := by
  dsimp only
  let H := retained g u q d
  let a₁ := s₁.subst (variableSubst x q)
  let a₂ := s₂.subst (variableSubst x q)
  let b₁ := s₁.subst (successorSubst x u)
  let b₂ := s₂.subst (successorSubst x u)
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
  have halign₁ := successor_substitution g u hu x q d hqd hud hdom s₁ p b
    (by dsimp [p]; omega) (by intro a ha; have := hH a ha; dsimp [p]; omega)
    (by intro a ha; have := h₁v a ha; dsimp [p]; omega)
    (by intro a ha; have := h₁s a ha; dsimp [p]; omega)
  have halign₂ := successor_substitution g u hu x q d hqd hud hdom s₂ qa (b+1)
    (by dsimp [qa]; omega) (by intro a ha; have := hH a ha; dsimp [qa]; omega)
    (by intro a ha; have := h₂v a ha; dsimp [qa]; omega)
    (by intro a ha; have := h₂s a ha; dsimp [qa]; omega)
  have hmove := termGraph_base_transport id b₂ qa qb (b+1)
    (by dsimp [qa]; omega) (by dsimp [qb]; omega)
    (by intro a ha; simp only [id_eq]; have := h₂s a ha; dsimp [qa]; omega)
    (by intro a ha; simp only [id_eq]; have := h₂s a ha; dsimp [qb]; omega)
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
    have h1 : Context Γ B₁ := .mp (Context.conjunctionLeft ha) (.mp hh (.closed halign₁.1))
    have h2' : Context Γ (termGraph id b₂ (b+1) qa).encode :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight ha)) (.mp hh (.closed halign₂.1))
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
    have h1 : Context Γ A₁ := .mp (Context.conjunctionLeft hb) (.mp hh (.closed halign₁.2))
    have h2' : Context Γ (termGraph id b₂ (b+1) qa).encode :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight hb)) (.closed hmove.2)
    have h2 : Context Γ A₂ := .mp h2' (.mp hh (.closed halign₂.2))
    have he : Context Γ E₁ := .mp (Context.conjunctionRight (Context.conjunctionRight hb)) (.closed heq.backward)
    change Context Γ (both A₁ (both A₂ E₁))
    exact Context.conjunctionIntro h1 (Context.conjunctionIntro h2 he)

end PASoundness.PAtoCompactSuccessorEqualityMatrixBaseBridge

#print axioms PASoundness.PAtoCompactSuccessorEqualityMatrixBaseBridge.equality_matrix_alignment
