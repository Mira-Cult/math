import Sude.DirectedResidual

/-! One-sided residual walks have integral physical edge adjustments. -/
namespace Sude
noncomputable section

/-- An arc has an actual edge witness whose singleton unit adjustment has
the required direction, divergence, and incidence at its starting vertex. -/
theorem directed_residual_arc_singleton {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (u v : Fin n)
    (harc : directedResidualArc source target flow u v) :
    ∃ (e : E) (k : ℤ),
      ((source e = u ∧ target e = v) ∨ (target e = u ∧ source e = v)) ∧
      (∀ j, (if j = e then k else 0) = 0 ∨
        ((if j = e then k else 0) = 1 ∧ flow j < 1) ∨
        ((if j = e then k else 0) = -1 ∧ 0 < flow j)) ∧
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
theorem directed_simple_residual_path_adjustment {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (flow : E → ℤ)
    {u v : Fin n} {S : Finset (Fin n)}
    (p : SimpleDirectedPath (directedResidualArc source target flow) u v S) :
    ∃ delta : E → ℤ,
      (∀ e, delta e = 0 ∨ (delta e = 1 ∧ flow e < 1) ∨
        (delta e = -1 ∧ 0 < flow e)) ∧
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
      directed_residual_arc_singleton source target flow a b hab
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
theorem directed_residual_path_adjustment {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (u v : Fin n)
    (hpath : Relation.ReflTransGen (directedResidualArc source target flow) u v) :
    ∃ delta : E → ℤ,
      (∀ e, delta e = 0 ∨ (delta e = 1 ∧ flow e < 1) ∨
        (delta e = -1 ∧ 0 < flow e)) ∧
      (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x) := by
  obtain ⟨S, p⟩ := simpleDirectedPath_of_reachable hpath
  obtain ⟨delta, hcapacity, hdiv, _⟩ := directed_simple_residual_path_adjustment source target flow p
  exact ⟨delta, hcapacity, hdiv⟩


end
end Sude
