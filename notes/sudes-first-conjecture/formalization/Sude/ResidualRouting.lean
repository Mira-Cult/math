import Sude.CutRouting

/-! Residual paths for the bounded integer routing problem. This module does
not yet augment a flow along such a path or prove flow existence. -/
namespace Sude
noncomputable section

/-- A residual arc moves one unit from the first vertex to the second.
Oppositely oriented uses of an edge are both included. -/
def residualArc {E : Type*} {n : ℕ} (source target : E → Fin n)
    (flow : E → ℤ) (C : ℕ) (u v : Fin n) : Prop :=
  ∃ e, (source e = u ∧ target e = v ∧ flow e < (C : ℤ)) ∨
    (target e = u ∧ source e = v ∧ -((C : ℕ) : ℤ) < flow e)

/-- Unsatisfied signed demand after applying the current flow. -/
def residualDemand {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) (v : Fin n) : ℤ :=
  d v - ∑ e : E, edgeTransfer source target flow e v

/-- A closed cut has no residual arc leaving it. -/
def residualClosed {E : Type*} {n : ℕ} (source target : E → Fin n)
    (flow : E → ℤ) (C : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ e, (source e ∈ S → target e ∉ S → (C : ℤ) ≤ flow e) ∧
    (target e ∈ S → source e ∉ S → flow e ≤ -(C : ℤ))

/-- A closed cut saturates each edge crossing it in the outward direction. -/
theorem closed_cut_edge_transfer {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ)) (S : Finset (Fin n))
    (hclosed : residualClosed source target flow C S) (e : E) :
    (∑ v ∈ S, edgeTransfer source target flow e v) =
      if e ∈ cutEdges source target S then (C : ℤ) else 0 := by
  classical
  by_cases hs : source e ∈ S <;> by_cases ht : target e ∈ S
  · simp [edgeTransfer, Finset.sum_sub_distrib, cutEdges, hs, ht]
  · have hf : flow e = (C : ℤ) := by
      have h₁ := (abs_le.mp (hflow e)).2
      have h₂ := (hclosed e).1 hs ht
      omega
    simp [edgeTransfer, Finset.sum_sub_distrib, cutEdges, hs, ht, hf]
  · have hf : flow e = -(C : ℤ) := by
      have h₁ := (abs_le.mp (hflow e)).1
      have h₂ := (hclosed e).2 ht hs
      omega
    simp [edgeTransfer, Finset.sum_sub_distrib, cutEdges, hs, ht, hf]
  · simp [edgeTransfer, Finset.sum_sub_distrib, cutEdges, hs, ht]

/-- Cut feasibility implies nonpositive residual demand on every closed cut. -/
theorem closed_cut_residual_nonpos {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ)) (S : Finset (Fin n))
    (hcut : |∑ v ∈ S, d v| ≤ ((C * (cutEdges source target S).card : ℕ) : ℤ))
    (hclosed : residualClosed source target flow C S) :
    (∑ v ∈ S, residualDemand source target d flow v) ≤ 0 := by
  classical
  have hsaturation : (∑ v ∈ S, ∑ e : E, edgeTransfer source target flow e v) =
      ((C * (cutEdges source target S).card : ℕ) : ℤ) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ e : E, if e ∈ cutEdges source target S then (C : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        exact closed_cut_edge_transfer source target flow C hflow S hclosed e
      _ = _ := by simp [mul_comm]
  have hdemand := (abs_le.mp hcut).2
  simp only [residualDemand, Finset.sum_sub_distrib]
  omega

/-- The finite set reachable from at least one positive residual vertex. -/
def residualReachable {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) (C : ℕ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ u, 0 < residualDemand source target d flow u ∧
    Relation.ReflTransGen (residualArc source target flow C) u v

/-- Reachable vertices are closed under every residual arc. -/
theorem residual_reachable_closed {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) (C : ℕ) :
    residualClosed source target flow C (residualReachable source target d flow C) := by
  classical
  let S : Finset (Fin n) := residualReachable source target d flow C
  change residualClosed source target flow C S
  have step {u v : Fin n} (hu : u ∈ S) (harc : residualArc source target flow C u v) : v ∈ S := by
    obtain ⟨w, hw, hpath⟩ := (Finset.mem_filter.mp (show u ∈ Finset.univ.filter _ from hu)).2
    change v ∈ Finset.univ.filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hpath.tail harc⟩
  intro e
  constructor
  · intro hs ht
    by_contra hf
    have hf' : flow e < (C : ℤ) := by omega
    apply ht
    exact step hs ⟨e, Or.inl ⟨rfl, rfl, hf'⟩⟩
  · intro ht hs
    by_contra hf
    have hf' : -(C : ℤ) < flow e := by omega
    apply hs
    exact step ht ⟨e, Or.inr ⟨rfl, rfl, hf'⟩⟩

/-- Some positive residual vertex can reach a negative residual vertex,
provided all cuts obey the
capacity inequality. This is a path-existence lemma, not flow sufficiency. -/
theorem residual_positive_reaches_negative {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ))
    (hcut : ∀ S : Finset (Fin n),
      |∑ v ∈ S, d v| ≤ ((C * (cutEdges source target S).card : ℕ) : ℤ))
    (hpositive : ∃ v, 0 < residualDemand source target d flow v) :
    ∃ u v, 0 < residualDemand source target d flow u ∧
      residualDemand source target d flow v < 0 ∧
      Relation.ReflTransGen (residualArc source target flow C) u v := by
  classical
  let S : Finset (Fin n) := residualReachable source target d flow C
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
  have hclosed : residualClosed source target flow C S :=
    residual_reachable_closed source target d flow C
  have hnonpos := closed_cut_residual_nonpos source target d flow C hflow S (hcut S) hclosed
  omega


/-- Adding edge values adds their signed transfers at every vertex. -/
theorem edgeTransfer_add {E : Type*} {n : ℕ} (source target : E → Fin n)
    (flow delta : E → ℤ) (e : E) (v : Fin n) :
    edgeTransfer source target (fun x => flow x + delta x) e v =
      edgeTransfer source target flow e v + edgeTransfer source target delta e v := by
  unfold edgeTransfer
  split_ifs <;> ring

/-- Exact change in every residual demand after adding edge adjustments. -/
theorem residualDemand_add {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow delta : E → ℤ) (v : Fin n) :
    residualDemand source target d (fun e => flow e + delta e) v =
      residualDemand source target d flow v - ∑ e : E, edgeTransfer source target delta e v := by
  simp only [residualDemand, edgeTransfer_add, Finset.sum_add_distrib]
  ring

/-- Integral one-unit residual adjustments preserve the edge capacity. -/
theorem unit_adjustments_preserve_capacity {E : Type*} (flow delta : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ))
    (hdelta : ∀ e, delta e = 0 ∨
      (delta e = 1 ∧ flow e < (C : ℤ)) ∨
      (delta e = -1 ∧ -(C : ℤ) < flow e)) :
    ∀ e, |flow e + delta e| ≤ (C : ℤ) := by
  intro e
  obtain ⟨hlow, hhigh⟩ := abs_le.mp (hflow e)
  rcases hdelta e with hz | ⟨hp, hc⟩ | ⟨hm, hc⟩ <;> rw [abs_le] <;> omega

/-- The divergence of a unit routed from u to v, with no assumption that
u and v are distinct. -/
def unitTransfer {n : ℕ} (u v x : Fin n) : ℤ :=
  (if x = u then 1 else 0) - (if x = v then 1 else 0)

/-- An available integral unit adjustment with the given divergence
preserves every edge capacity and decreases residual demand at its source
while increasing it at its target. -/
theorem apply_unit_adjustment {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow delta : E → ℤ) (C : ℕ)
    (u v : Fin n) (hflow : ∀ e, |flow e| ≤ (C : ℤ))
    (hdelta : ∀ e, delta e = 0 ∨
      (delta e = 1 ∧ flow e < (C : ℤ)) ∨
      (delta e = -1 ∧ -(C : ℤ) < flow e))
    (hdiv : ∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x) :
    (∀ e, |flow e + delta e| ≤ (C : ℤ)) ∧
    (∀ x, residualDemand source target d (fun e => flow e + delta e) x =
      residualDemand source target d flow x - unitTransfer u v x) := by
  exact ⟨unit_adjustments_preserve_capacity flow delta C hflow hdelta,
    fun x => (residualDemand_add source target d flow delta x).trans (by rw [hdiv x])⟩

/-- The residual mass of an integer demand vector. -/
def residualMass {n : ℕ} (r : Fin n → ℤ) : ℤ := ∑ x, |r x|

/-- Routing one unit from a positive residual vertex to a negative one
strictly decreases the integer residual mass by two. -/
theorem unit_transfer_decreases_mass {n : ℕ} (r : Fin n → ℤ) (u v : Fin n)
    (hu : 0 < r u) (hv : r v < 0) :
    residualMass (fun x => r x - unitTransfer u v x) = residualMass r - 2 := by
  classical
  have huv : u ≠ v := by intro h; subst v; omega
  have hp : ∀ x, |r x - unitTransfer u v x| =
      |r x| - (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
    intro x
    by_cases hx : x = u
    · subst x
      simp only [unitTransfer, if_true, if_neg huv, sub_zero]
      rw [abs_of_pos hu, abs_of_nonneg (by omega : 0 ≤ r u - 1)]
    · by_cases hy : x = v
      · subst x
        have hvu : v ≠ u := Ne.symm huv
        simp only [unitTransfer, if_neg hvu, if_true, zero_sub, sub_neg_eq_add, sub_zero]
        rw [abs_of_neg hv, abs_of_nonpos (by omega : r v + 1 ≤ 0)]
        omega
      · simp [unitTransfer, hx, hy]
  unfold residualMass
  simp_rw [hp]
  simp [Finset.sum_sub_distrib]
  ring



/-- A residual arc is implemented by changing one actual edge by one
integer unit in its available direction. -/
theorem residual_arc_unit_adjustment {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (C : ℕ) (u v : Fin n)
    (harc : residualArc source target flow C u v) :
    ∃ delta : E → ℤ,
      (∀ e, delta e = 0 ∨
        (delta e = 1 ∧ flow e < (C : ℤ)) ∨
        (delta e = -1 ∧ -(C : ℤ) < flow e)) ∧
      (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x) := by
  classical
  obtain ⟨e, hforward | hreverse⟩ := harc
  · obtain ⟨hs, ht, havail⟩ := hforward
    refine ⟨fun j => if j = e then 1 else 0, ?_, ?_⟩
    · intro j
      by_cases h : j = e
      · subst j
        exact Or.inr (Or.inl ⟨by simp, havail⟩)
      · exact Or.inl (by simp [h])
    · intro x
      subst u
      subst v
      rw [Finset.sum_eq_single e (by intro j _ hj; simp [edgeTransfer, hj]) (by simp)]
      simp [edgeTransfer, unitTransfer, eq_comm]
  · obtain ⟨ht, hs, havail⟩ := hreverse
    refine ⟨fun j => if j = e then -1 else 0, ?_, ?_⟩
    · intro j
      by_cases h : j = e
      · subst j
        exact Or.inr (Or.inr ⟨by simp, havail⟩)
      · exact Or.inl (by simp [h])
    · intro x
      subst u
      subst v
      rw [Finset.sum_eq_single e (by intro j _ hj; simp [edgeTransfer, hj]) (by simp)]
      simp only [edgeTransfer, unitTransfer, (eq_comm (a := x) (b := source e)),
        (eq_comm (a := x) (b := target e))]
      split_ifs <;> ring

/-- Conservation makes the residual vector zero-total whenever demand is. -/
theorem residualDemand_sum_zero {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (flow : E → ℤ)
    (hzero : ∑ x, d x = 0) : ∑ x, residualDemand source target d flow x = 0 := by
  simp only [residualDemand, Finset.sum_sub_distrib, hzero,
    edge_divergence_sum_zero, sub_self]

/-- A nonzero zero-total integer vector has a positive coordinate. -/
theorem zero_total_nonzero_has_positive {n : ℕ} (r : Fin n → ℤ)
    (hzero : ∑ x, r x = 0) (hnonzero : ∃ x, r x ≠ 0) : ∃ x, 0 < r x := by
  classical
  by_contra h
  push Not at h
  have heach : ∀ x ∈ Finset.univ, r x ≤ 0 := by
    intro x _
    exact h x
  have hall := (Finset.sum_eq_zero_iff_of_nonpos heach).mp hzero
  obtain ⟨x, hx⟩ := hnonzero
  exact hx (hall x (Finset.mem_univ x))

/-- Residual mass is nonnegative, independently of whether the flow is feasible. -/
theorem residualMass_nonneg {n : ℕ} (r : Fin n → ℤ) : 0 ≤ residualMass r := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- If every nonzero residual admits an integral unit adjustment of the
specified form, repeated adjustment terminates at an exact bounded flow.
The step hypothesis is a local construction obligation, not an import. -/
theorem routing_by_unit_augmentations {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (C : ℕ)
    (hstep : ∀ flow : E → ℤ, (∀ e, |flow e| ≤ (C : ℤ)) →
      (∃ x, residualDemand source target d flow x ≠ 0) →
      ∃ (delta : E → ℤ) (u v : Fin n),
        0 < residualDemand source target d flow u ∧
        residualDemand source target d flow v < 0 ∧
        (∀ e, delta e = 0 ∨
          (delta e = 1 ∧ flow e < (C : ℤ)) ∨
          (delta e = -1 ∧ -(C : ℤ) < flow e)) ∧
        (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x)) :
    ∃ flow : E → ℤ, (∀ e, |flow e| ≤ (C : ℤ)) ∧
      ∀ v, (∑ e : E, edgeTransfer source target flow e v) = d v := by
  classical
  have loop : ∀ k : ℕ, ∀ flow : E → ℤ,
      (∀ e, |flow e| ≤ (C : ℤ)) →
      (residualMass (residualDemand source target d flow)).toNat = k →
      ∃ final : E → ℤ, (∀ e, |final e| ≤ (C : ℤ)) ∧
        ∀ v, (∑ e : E, edgeTransfer source target final e v) = d v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro flow hflow hmeasure
      by_cases hdone : ∀ v, residualDemand source target d flow v = 0
      · refine ⟨flow, hflow, ?_⟩
        intro v
        have h := hdone v
        dsimp [residualDemand] at h
        omega
      · push Not at hdone
        obtain ⟨delta, u, v, hu, hv, hdelta, hdiv⟩ := hstep flow hflow hdone
        obtain ⟨hcap, hres⟩ := apply_unit_adjustment source target d flow delta C u v
          hflow hdelta hdiv
        have hmass : residualMass (residualDemand source target d (fun e => flow e + delta e)) =
            residualMass (residualDemand source target d flow) - 2 := by
          rw [show residualDemand source target d (fun e => flow e + delta e) =
              (fun x => residualDemand source target d flow x - unitTransfer u v x) from funext hres]
          exact unit_transfer_decreases_mass (residualDemand source target d flow) u v hu hv
        have hnonneg := residualMass_nonneg (residualDemand source target d (fun e => flow e + delta e))
        have hsmaller : (residualMass (residualDemand source target d (fun e => flow e + delta e))).toNat < k := by
          omega
        exact ih _ hsmaller (fun e => flow e + delta e) hcap rfl
  apply loop ((residualMass (residualDemand source target d (fun _ => 0))).toNat) (fun _ => 0)
  · intro e
    simp
  · rfl



/-- Cut feasibility and an explicit path-to-adjustment construction imply a
bounded integer flow. The path construction remains an internal obligation. -/
theorem routing_of_residual_path_adjustments {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (d : Fin n → ℤ) (C : ℕ)
    (hzero : ∑ v, d v = 0)
    (hcut : ∀ S : Finset (Fin n),
      |∑ v ∈ S, d v| ≤ ((C * (cutEdges source target S).card : ℕ) : ℤ))
    (hpath : ∀ (flow : E → ℤ) (u v : Fin n),
      (∀ e, |flow e| ≤ (C : ℤ)) →
      Relation.ReflTransGen (residualArc source target flow C) u v → u ≠ v →
      ∃ delta : E → ℤ,
        (∀ e, delta e = 0 ∨
          (delta e = 1 ∧ flow e < (C : ℤ)) ∨
          (delta e = -1 ∧ -(C : ℤ) < flow e)) ∧
        (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x)) :
    ∃ flow : E → ℤ, (∀ e, |flow e| ≤ (C : ℤ)) ∧
      ∀ v, (∑ e : E, edgeTransfer source target flow e v) = d v := by
  apply routing_by_unit_augmentations source target d C
  intro flow hflow hnonzero
  have hreszero := residualDemand_sum_zero source target d flow hzero
  have hpositive := zero_total_nonzero_has_positive _ hreszero hnonzero
  obtain ⟨u, v, hu, hv, hreach⟩ :=
    residual_positive_reaches_negative source target d flow C hflow hcut hpositive
  have huv : u ≠ v := by intro h; subst v; omega
  obtain ⟨delta, hdelta, hdiv⟩ := hpath flow u v hflow hreach huv
  exact ⟨delta, u, v, hu, hv, hdelta, hdiv⟩


end
end Sude
