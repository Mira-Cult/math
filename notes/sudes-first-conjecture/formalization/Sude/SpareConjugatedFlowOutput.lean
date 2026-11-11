import Sude.OffRolesFlowDifference
import Sude.OffSupportReservationImage

/-! Conjugate one supplied flow output together with its exact CY reference.
All continuation and agreement hypotheses are explicit. This does not construct
the permutation or CY, prove line bounds, choose targets, or supply a prime. -/

namespace Sude
noncomputable section

/-- If an output agrees with a reference off the active roles, precomposing
both by one cell permutation supported in `full \ roles` preserves their
physical line differences, their supplied agreement on `keep`, and the supplied
equalities of their full-value images and unused pools. In particular,
`keep` is agreement with the *transformed* reference; this makes no assertion
that either transformed square agrees with the old reference there. -/
theorem spare_conjugated_flow_output {n : ℕ}
    (roles full support keep : Finset (Cell n))
    (σ : Equiv.Perm (Cell n)) (cy out : Cell n ≃ Fin (n*n))
    (hsub : support ⊆ full \ roles)
    (hfix : ∀ z ∉ support, σ z = z)
    (hoff : ∀ z ∉ roles, entry out z = entry cy z)
    (hkeep : ∀ z ∈ keep, entry out z = entry cy z)
    (himage : roles.image (entry out) = roles.image (entry cy))
    (hfull : full.image (entry out) = full.image (entry cy))
    (hunused : actualUnusedPool out full = actualUnusedPool cy full) :
    (∀ r, (rowSum (σ.trans out) r : ℤ) - (rowSum (σ.trans cy) r : ℤ) =
      (rowSum out r : ℤ) - (rowSum cy r : ℤ)) ∧
    (∀ c, (columnSum (σ.trans out) c : ℤ) - (columnSum (σ.trans cy) c : ℤ) =
      (columnSum out c : ℤ) - (columnSum cy c : ℤ)) ∧
    ((mainSum (σ.trans out) : ℤ) - (mainSum (σ.trans cy) : ℤ) =
      (mainSum out : ℤ) - (mainSum cy : ℤ)) ∧
    ((antiSum (σ.trans out) : ℤ) - (antiSum (σ.trans cy) : ℤ) =
      (antiSum out : ℤ) - (antiSum cy : ℤ)) ∧
    (∀ z ∈ keep, entry (σ.trans out) z = entry (σ.trans cy) z) ∧
    (∀ z ∉ roles, entry (σ.trans out) z = entry (σ.trans cy) z) ∧
    roles.image (entry (σ.trans out)) = roles.image (entry (σ.trans cy)) ∧
    full.image (entry (σ.trans out)) = full.image (entry (σ.trans cy)) ∧
    actualUnusedPool (σ.trans out) full = actualUnusedPool (σ.trans cy) full ∧
    Set.range (entry (σ.trans out)) = pool n ∧
    Function.Injective (entry (σ.trans out)) := by
  classical
  have hroles : ∀ z ∈ roles, σ z = z := by
    intro z hz
    apply hfix
    intro hs
    exact (Finset.mem_sdiff.mp (hsub hs)).2 hz
  have hsubset : support ⊆ full := fun z hz => (Finset.mem_sdiff.mp (hsub hz)).1
  obtain ⟨hr, hc, hm, ha⟩ := off_roles_perm_physical_differences roles σ out cy hroles hoff
  have hkeep' : ∀ z ∈ keep, entry (σ.trans out) z = entry (σ.trans cy) z := by
    intro z hz
    change entry out (σ z) = entry cy (σ z)
    exact off_roles_perm_agreement (roles : Set (Cell n)) σ (entry out) (entry cy)
      hroles hoff (hkeep z hz)
  have hoff' : ∀ z ∉ roles, entry (σ.trans out) z = entry (σ.trans cy) z := by
    intro z hz
    change entry out (σ z) = entry cy (σ z)
    exact hoff (σ z) (off_roles_perm_outside (roles : Set (Cell n)) σ hroles hz)
  have hroleOut : roles.image (entry (σ.trans out)) = roles.image (entry out) := by
    apply Finset.image_congr
    intro z hz
    simp only [entry, Equiv.trans_apply, hroles z hz]
  have hroleCy : roles.image (entry (σ.trans cy)) = roles.image (entry cy) := by
    apply Finset.image_congr
    intro z hz
    simp only [entry, Equiv.trans_apply, hroles z hz]
  have ho := off_support_reservation_value_images full support hsubset σ hfix out
  have hy := off_support_reservation_value_images full support hsubset σ hfix cy
  refine ⟨hr, hc, hm, ha, hkeep', hoff', ?_, ?_, ?_, entry_range _, entry_injective _⟩
  · exact hroleOut.trans (himage.trans hroleCy.symm)
  · exact ho.1.trans (hfull.trans hy.1.symm)
  · exact ho.2.2.trans (hunused.trans hy.2.2.symm)

/-- Transport an entire supplied family of row and column flows to the
permuted reference. The index predicates may encode any required flow bounds.
The retained predicate must have an explicit transport proof; no arbitrary
predicate is silently assumed invariant. -/
theorem spare_conjugated_supplied_flows {n : ℕ} {F C : Type*}
    (roles full support keep : Finset (Cell n))
    (σ : Equiv.Perm (Cell n)) (cy : Cell n ≃ Fin (n*n))
    (hsub : support ⊆ full \ roles)
    (hfix : ∀ z ∉ support, σ z = z)
    (validRow : F → Prop) (validCol : C → Prop)
    (rowDelta : F → Fin n → ℤ) (colDelta : C → Fin n → ℤ)
    (P P' : (Cell n ≃ Fin (n*n)) → Prop)
    (hP : ∀ b, P b → P' (σ.trans b))
    (hflows : ∀ fr, validRow fr → ∀ fc, validCol fc →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum cy r : ℤ) = rowDelta fr r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum cy c : ℤ) = colDelta fc c) ∧
        mainSum b = mainSum cy ∧ antiSum b = antiSum cy ∧
        (∀ z ∈ keep, entry b z = entry cy z) ∧
        (∀ z ∉ roles, entry b z = entry cy z) ∧
        roles.image (entry b) = roles.image (entry cy) ∧
        full.image (entry b) = full.image (entry cy) ∧
        actualUnusedPool b full = actualUnusedPool cy full ∧ P b) :
    ∀ fr, validRow fr → ∀ fc, validCol fc →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum (σ.trans cy) r : ℤ) = rowDelta fr r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum (σ.trans cy) c : ℤ) = colDelta fc c) ∧
        mainSum b = mainSum (σ.trans cy) ∧ antiSum b = antiSum (σ.trans cy) ∧
        (∀ z ∈ keep, entry b z = entry (σ.trans cy) z) ∧
        (∀ z ∉ roles, entry b z = entry (σ.trans cy) z) ∧
        roles.image (entry b) = roles.image (entry (σ.trans cy)) ∧
        full.image (entry b) = full.image (entry (σ.trans cy)) ∧
        actualUnusedPool b full = actualUnusedPool (σ.trans cy) full ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧ P' b := by
  intro fr hfr fc hfc
  obtain ⟨b, hr, hc, hm, ha, hk, hoff, hi, hf, hu, hp⟩ := hflows fr hfr fc hfc
  obtain ⟨hr', hc', hm', ha', hk', hoff', hi', hf', hu', hpool, hinj⟩ :=
    spare_conjugated_flow_output roles full support keep σ cy b hsub hfix hoff hk hi hf hu
  refine ⟨σ.trans b, ?_, ?_, ?_, ?_, hk', hoff', hi', hf', hu', hpool, hinj, hP b hp⟩
  · intro r
    exact (hr' r).trans (hr r)
  · intro c
    exact (hc' c).trans (hc c)
  · exact_mod_cast (show (mainSum (σ.trans b) : ℤ) = mainSum (σ.trans cy) by
      rw [hm] at hm'
      omega)
  · exact_mod_cast (show (antiSum (σ.trans b) : ℤ) = antiSum (σ.trans cy) by
      rw [ha] at ha'
      omega)

end
end Sude
