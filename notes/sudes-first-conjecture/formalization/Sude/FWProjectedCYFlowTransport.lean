import Sude.FWThetaFamilyDQRFInputs
import Sude.FWThetaNetworkWitness
import Sude.FWCompletedSuppliedFlows
import Sude.FWRoleSupportForNetworks
import Sude.ActiveSupportFullKeepout

/-! Transport the supplied bounded flow family to one given completion of
the same fresh reference. This does not construct flows, select prime targets,
or give absolute line bounds. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

/-- If `completed` fixes the full geometric reservation of the supplied
reference, synchronize every supplied pair of bounded flows with that exact
completion. The new output fixes the rectangle and the previously unreserved
diagonal cells, but need not fix every cell of the full reservation. -/
theorem fw_projected_cy_supplied_flows
    {n : ℕ} (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (completed : Cell n ≃ Fin (n*n))
    (hcompleted : ∀ z ∈ fwThetaFamilyFull f, entry completed z = entry oldReference z) :
    ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
        fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
        fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∃ b b' : Cell n ≃ Fin (n*n),
      (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum oldReference c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry oldReference z) ∧
      (∀ z ∉ roles, entry b z = entry oldReference z) ∧
      roles.image (entry b) = roles.image (entry oldReference) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
      (∀ z ∈ roles, entry b' z = entry b z) ∧
      (∀ z ∉ roles, entry b' z = entry completed z) ∧
      (∀ r, (rowSum b' r : ℤ) - (rowSum completed r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b' c : ℤ) - (columnSum completed c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b' = mainSum completed ∧ antiSum b' = antiSum completed ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry b' z = entry completed z) ∧
      roles.image (entry b') = roles.image (entry completed) ∧
      Set.range (entry b') = pool n ∧ Function.Injective (entry b') ∧
      (∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry b' z = entry completed z) ∧
      (fwThetaFamilyFull f).image (entry b') = (fwThetaFamilyFull f).image (entry completed) ∧
      actualUnusedPool b' (fwThetaFamilyFull f) = actualUnusedPool completed (fwThetaFamilyFull f) := by
  classical
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
    f.hrows f.hcols
  dsimp only at hgeom
  have hsub : roles ⊆ fwThetaFamilyFull f := by
    rw [net.roles_eq]
    simpa only [fwThetaFamilyFull] using hgeom.2.2.1
  have hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
        fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
        fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum oldReference c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
        mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
        (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry oldReference z) ∧
        (∀ z ∉ roles, entry b z = entry oldReference z) ∧
        roles.image (entry b) = roles.image (entry oldReference) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
    intro fr hfr fc hfc
    obtain ⟨b, hr, hc, hm, ha, hrect, hoff, himage, hpool, hinj⟩ := net.flows fr hfr fc hfc
    refine ⟨b, hr, hc, hm, ha, hrect, ?_, himage.trans net.roles_image.symm, hpool, hinj⟩
    intro z hz
    exact (hoff z hz).trans (net.off_roles z hz).symm
  have h := fw_completed_supplied_flows (N := (n / 450) * poolMaximum n)
    p oldReference oldReference completed completed roles (fwThetaFamilyFull f)
    (packedRectangleSupport f.hs choice) hsub hcompleted (by intros; rfl)
    (fun z hz => hcompleted z (hsub hz)) (by intros; rfl) hflows
  intro fr hfr fc hfc
  obtain ⟨b, b', hr, hc, hm, ha, hrect, hoff, himage, hpool, hinj,
    hbActive, hbOff, hrow, hcol, hm', ha', hrect', himage', hpool', hinj'⟩ := h fr hfr fc hfc
  have hdiag : ∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry b' z = entry completed z := by
    intro z hz
    have hzfull : z ∉ fwThetaFamilyFull f := (Finset.mem_sdiff.mp hz).2
    exact hbOff z (fun hzr => hzfull (hsub hzr))
  have hfull := full_keepout_value_image_and_unused_eq completed b' roles (fwThetaFamilyFull f)
    hsub hbOff himage'
  exact ⟨b, b', hr, hc, hm, ha, hrect, hoff, himage, hpool, hinj,
    hbActive, hbOff, hrow, hcol, hm', ha', hrect', himage', hpool', hinj', hdiag, hfull.1, hfull.2⟩

end
end Sude
