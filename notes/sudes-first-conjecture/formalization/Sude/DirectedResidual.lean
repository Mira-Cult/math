import Sude.SimpleResidualPath

/-! Residual reachability for one-sided integral unit-capacity edges.
This is the directed cut half of the regular-factor flow construction. -/
namespace Sude
noncomputable section

/-- Only edges directed out of the set contribute to a one-sided cut. -/
def directedCutEdges {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (S : Finset (Fin n)) : Finset E := by
  classical
  exact Finset.univ.filter fun e => source e ∈ S ∧ target e ∉ S

/-- An available forward unit, or an available cancellation of prior flow. -/
def directedResidualArc {E : Type*} {n : ℕ} (source target : E → Fin n)
    (flow : E → ℤ) (u v : Fin n) : Prop :=
  ∃ e, (source e = u ∧ target e = v ∧ flow e < 1) ∨
    (target e = u ∧ source e = v ∧ 0 < flow e)

/-- Closure under the one-sided residual relation saturates outgoing edges
at one and incoming edges at zero. -/
def directedResidualClosed {E : Type*} {n : ℕ} (source target : E → Fin n)
    (flow : E → ℤ) (S : Finset (Fin n)) : Prop :=
  ∀ e, (source e ∈ S → target e ∉ S → 1 ≤ flow e) ∧
    (target e ∈ S → source e ∉ S → flow e ≤ 0)

theorem directed_closed_cut_edge_transfer {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ)
    (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1) (S : Finset (Fin n))
    (hclosed : directedResidualClosed source target flow S) (e : E) :
    (∑ v ∈ S, edgeTransfer source target flow e v) =
      if e ∈ directedCutEdges source target S then 1 else 0 := by
  classical
  by_cases hs : source e ∈ S <;> by_cases ht : target e ∈ S
  · simp [edgeTransfer, Finset.sum_sub_distrib, directedCutEdges, hs, ht]
  · have hf : flow e = 1 := by have := (hclosed e).1 hs ht; have := (hflow e).2; omega
    simp [edgeTransfer, directedCutEdges, hs, ht, hf]
  · have hf : flow e = 0 := by have := (hclosed e).2 ht hs; have := (hflow e).1; omega
    simp [edgeTransfer, directedCutEdges, hs, ht, hf]
  · simp [edgeTransfer, Finset.sum_sub_distrib, directedCutEdges, hs, ht]

/-- A feasible directed cut has nonpositive remaining demand once closed. -/
theorem directed_closed_cut_residual_nonpos {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ)
    (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1) (S : Finset (Fin n))
    (hcut : (∑ v ∈ S, d v) ≤ (directedCutEdges source target S).card)
    (hclosed : directedResidualClosed source target flow S) :
    (∑ v ∈ S, residualDemand source target d flow v) ≤ 0 := by
  classical
  have hsaturation : (∑ v ∈ S, ∑ e : E, edgeTransfer source target flow e v) =
      ((directedCutEdges source target S).card : ℤ) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ e : E, if e ∈ directedCutEdges source target S then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        exact directed_closed_cut_edge_transfer source target flow hflow S hclosed e
      _ = _ := by simp
  simp only [residualDemand, Finset.sum_sub_distrib]
  omega

def directedResidualReachable {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ u, 0 < residualDemand source target d flow u ∧
    Relation.ReflTransGen (directedResidualArc source target flow) u v

theorem directed_residual_reachable_closed {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) :
    directedResidualClosed source target flow (directedResidualReachable source target d flow) := by
  classical
  let S : Finset (Fin n) := directedResidualReachable source target d flow
  change directedResidualClosed source target flow S
  have step {u v : Fin n} (hu : u ∈ S) (harc : directedResidualArc source target flow u v) : v ∈ S := by
    obtain ⟨w, hw, hpath⟩ := (Finset.mem_filter.mp (show u ∈ Finset.univ.filter _ from hu)).2
    change v ∈ Finset.univ.filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hpath.tail harc⟩
  intro e
  constructor
  · intro hs ht
    by_contra hf
    have hf' : flow e < 1 := by omega
    exact ht (step hs ⟨e, Or.inl ⟨rfl, rfl, hf'⟩⟩)
  · intro ht hs
    by_contra hf
    have hf' : 0 < flow e := by omega
    exact hs (step ht ⟨e, Or.inr ⟨rfl, rfl, hf'⟩⟩)

/-- Cut feasibility forces an augmenting residual walk to a negative
residual vertex whenever a positive residual vertex exists. -/
theorem directed_positive_reaches_negative {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ)
    (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1)
    (hcut : ∀ S : Finset (Fin n), (∑ v ∈ S, d v) ≤ (directedCutEdges source target S).card)
    (hpositive : ∃ v, 0 < residualDemand source target d flow v) :
    ∃ u v, 0 < residualDemand source target d flow u ∧
      residualDemand source target d flow v < 0 ∧
      Relation.ReflTransGen (directedResidualArc source target flow) u v := by
  classical
  let S : Finset (Fin n) := directedResidualReachable source target d flow
  by_contra hn
  push Not at hn
  have hnonneg : ∀ v ∈ S, 0 ≤ residualDemand source target d flow v := by
    intro v hv
    obtain ⟨u, hu, hp⟩ := (Finset.mem_filter.mp (show v ∈ Finset.univ.filter _ from hv)).2
    by_contra hh
    have hvneg : residualDemand source target d flow v < 0 := by omega
    exact hn u v hu hvneg hp
  obtain ⟨w, hw⟩ := hpositive
  have hwS : w ∈ S := by
    change w ∈ Finset.univ.filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, Relation.ReflTransGen.refl⟩
  have hsum : 0 < ∑ v ∈ S, residualDemand source target d flow v :=
    Finset.sum_pos' hnonneg ⟨w, hwS, hw⟩
  have hclosed : directedResidualClosed source target flow S :=
    directed_residual_reachable_closed source target d flow
  have hnonpos := directed_closed_cut_residual_nonpos source target d flow hflow S (hcut S) hclosed
  omega

end
end Sude
