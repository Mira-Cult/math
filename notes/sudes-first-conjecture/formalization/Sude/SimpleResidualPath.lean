import Sude.ResidualRouting

/-! Loop erasure and edge-level realization for directed residual paths. -/
namespace Sude
noncomputable section

/-- A directed path whose vertices occur only once. The set records exactly
its vertices, including both endpoints. -/
inductive SimpleDirectedPath {V : Type*} [DecidableEq V] (r : V → V → Prop) :
    V → V → Finset V → Prop
  | nil (v : V) : SimpleDirectedPath r v v {v}
  | cons {u v w : V} {S : Finset V} : r u v → SimpleDirectedPath r v w S →
      u ∉ S → SimpleDirectedPath r u w (insert u S)

/-- Every vertex of a simple path starts a simple suffix, contained in the
original path's vertex set. -/
theorem SimpleDirectedPath.suffix {V : Type*} [DecidableEq V] {r : V → V → Prop}
    {u v : V} {S : Finset V} (p : SimpleDirectedPath r u v S)
    {x : V} (hx : x ∈ S) : ∃ T ⊆ S, SimpleDirectedPath r x v T := by
  induction p with
  | nil v =>
    simp only [Finset.mem_singleton] at hx
    subst x
    exact ⟨{v}, Finset.Subset.rfl, SimpleDirectedPath.nil v⟩
  | @cons a b c T hab p ha ih =>
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ⟨insert x T, Finset.Subset.rfl, SimpleDirectedPath.cons hab p ha⟩
    · obtain ⟨U, hU, hp⟩ := ih hx
      exact ⟨U, hU.trans (Finset.subset_insert a T), hp⟩

/-- Every directed walk has a loop-erased path with the same endpoints. -/
theorem simpleDirectedPath_of_reachable {V : Type*} [DecidableEq V] {r : V → V → Prop}
    {u v : V} (h : Relation.ReflTransGen r u v) :
    ∃ S, SimpleDirectedPath r u v S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, SimpleDirectedPath.nil _⟩
  | @head a b hab hp ih =>
    obtain ⟨S, p⟩ := ih
    by_cases ha : a ∈ S
    · obtain ⟨T, _, hp⟩ := p.suffix ha
      exact ⟨T, hp⟩
    · exact ⟨insert a S, SimpleDirectedPath.cons hab p ha⟩


/-- An arc has an actual edge witness whose singleton unit adjustment has
the required direction, divergence, and incidence at its starting vertex. -/
theorem residual_arc_singleton {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (C : ℕ) (u v : Fin n)
    (harc : residualArc source target flow C u v) :
    ∃ (e : E) (k : ℤ),
      ((source e = u ∧ target e = v) ∨ (target e = u ∧ source e = v)) ∧
      (∀ j, (if j = e then k else 0) = 0 ∨
        ((if j = e then k else 0) = 1 ∧ flow j < (C : ℤ)) ∨
        ((if j = e then k else 0) = -1 ∧ -(C : ℤ) < flow j)) ∧
      (∀ x, (∑ j : E, edgeTransfer source target (fun j => if j = e then k else 0) j x) =
        unitTransfer u v x) := by
  classical
  obtain ⟨e, hforward | hreverse⟩ := harc
  · obtain ⟨hs, ht, havail⟩ := hforward
    refine ⟨e, 1, Or.inl ⟨hs, ht⟩, ?_, ?_⟩
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
    refine ⟨e, -1, Or.inr ⟨ht, hs⟩, ?_, ?_⟩
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

/-- A simple directed residual path can be implemented by simultaneous
unit changes, each attached to a distinct actual edge in the path. -/
theorem simple_residual_path_adjustment {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (flow : E → ℤ) (C : ℕ)
    {u v : Fin n} {S : Finset (Fin n)}
    (p : SimpleDirectedPath (residualArc source target flow C) u v S) :
    ∃ delta : E → ℤ,
      (∀ e, delta e = 0 ∨ (delta e = 1 ∧ flow e < (C : ℤ)) ∨
        (delta e = -1 ∧ -(C : ℤ) < flow e)) ∧
      (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x) ∧
      (∀ e, delta e ≠ 0 → source e ∈ S ∧ target e ∈ S) := by
  classical
  induction p with
  | nil a =>
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro e; exact Or.inl rfl
    · intro x; simp [edgeTransfer, unitTransfer]
    · intro e he; exact (he rfl).elim
  | @cons a b c T hab p ha ih =>
    obtain ⟨delta, hdelta, hdiv, hsupport⟩ := ih
    obtain ⟨e, k, hincident, hsingle, hsinglediv⟩ :=
      residual_arc_singleton source target flow C a b hab
    have hezero : delta e = 0 := by
      by_contra hne
      obtain ⟨hs, ht⟩ := hsupport e hne
      rcases hincident with ⟨hsEq, _⟩ | ⟨htEq, _⟩
      · exact ha (hsEq ▸ hs)
      · exact ha (htEq ▸ ht)
    let single : E → ℤ := fun j => if j = e then k else 0
    refine ⟨fun j => delta j + single j, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = e
      · subst j
        simpa [hezero, single] using hsingle e
      · simpa [single, hj] using hdelta j
    · intro x
      dsimp only [single]
      simp only [edgeTransfer_add, Finset.sum_add_distrib, hdiv, hsinglediv]
      simp only [unitTransfer]
      ring
    · intro j hj
      by_cases hje : j = e
      · subst j
        have hbT : b ∈ T := by cases p <;> simp
        rcases hincident with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact ⟨hs.symm ▸ Finset.mem_insert_self a T,
            ht.symm ▸ Finset.mem_insert_of_mem hbT⟩
        · exact ⟨hs.symm ▸ Finset.mem_insert_of_mem hbT,
            ht.symm ▸ Finset.mem_insert_self a T⟩
      · have hd : delta j ≠ 0 := by simpa [single, hje] using hj
        obtain ⟨hs, ht⟩ := hsupport j hd
        exact ⟨Finset.mem_insert_of_mem hs, Finset.mem_insert_of_mem ht⟩



/-- A residual walk admits an integral unit adjustment with its endpoint
divergence; loops are erased before distinct edge indices are chosen. -/
theorem residual_path_adjustment {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (C : ℕ) (u v : Fin n)
    (hpath : Relation.ReflTransGen (residualArc source target flow C) u v) :
    ∃ delta : E → ℤ,
      (∀ e, delta e = 0 ∨ (delta e = 1 ∧ flow e < (C : ℤ)) ∨
        (delta e = -1 ∧ -(C : ℤ) < flow e)) ∧
      (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x) := by
  obtain ⟨S, p⟩ := simpleDirectedPath_of_reachable hpath
  obtain ⟨delta, hcapacity, hdiv, _⟩ := simple_residual_path_adjustment source target flow C p
  exact ⟨delta, hcapacity, hdiv⟩

/-- Integral max-flow/min-cut for finite indexed undirected edges with a
uniform integer capacity, oriented for signed flow. Parallel edges and loops
are permitted. No flow existence hypothesis is used. -/
theorem integer_flow_of_cut_inequalities {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (d : Fin n → ℤ) (C : ℕ)
    (hzero : ∑ v, d v = 0)
    (hcut : ∀ S : Finset (Fin n),
      |∑ v ∈ S, d v| ≤ ((C * (cutEdges source target S).card : ℕ) : ℤ)) :
    ∃ flow : E → ℤ, (∀ e, |flow e| ≤ (C : ℤ)) ∧
      ∀ v, (∑ e : E, edgeTransfer source target flow e v) = d v := by
  apply routing_of_residual_path_adjustments source target d C hzero hcut
  intro flow u v _ hpath _
  exact residual_path_adjustment source target flow C u v hpath

/-- FC2K's demand box, expansion and floor-capacity gate produce an
actual bounded integral flow with the requested signed divergence. -/
theorem fc2k_integral_flow {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (N B : ℕ)
    (hN : 2000 ≤ N) (hB : 400000 * B < 199 * 999 * N)
    (hzero : ∑ v, d v = 0) (hbound : ∀ v, |d v| ≤ (B : ℤ))
    (hexp : ∀ S : Finset (Fin n),
      199 * min S.card (n - S.card) ≤ 200 * (cutEdges source target S).card) :
    ∃ flow : E → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ flow e ∧ flow e ≤ ((N / 2 : ℕ) : ℤ)) ∧
      ∀ v, (∑ e : E, edgeTransfer source target flow e v) = d v := by
  obtain ⟨flow, hcap, hdiv⟩ := integer_flow_of_cut_inequalities source target d (N / 2)
    hzero (fc2k_cut_inequalities source target d N B hN hB hzero hbound hexp)
  exact ⟨flow, fun e => abs_le.mp (hcap e), hdiv⟩


end
end Sude
