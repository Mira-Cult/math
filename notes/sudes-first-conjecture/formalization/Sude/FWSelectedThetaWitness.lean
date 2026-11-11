import Sude.FWThetaProjectedJoinWitness
import Sude.FWThetaFamilyDQRFInputs
import Sude.FWProjectedThetaDQRFAllLineFlows

/-! A selected projected witness for conditional DQ/RF use. Its existence
follows from one theta invocation, and its family, permutation, old reference
and network satisfy the projected facts together. The selection retains no
link to omitted theta facts. The DQ/RF gate, growth diagonal invoices, prime
targets, and post-flow line bounds are not established. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- The projected theta data, with the dependent network tied to the exact
family geometry, ordered square, permutation and old reference. -/
structure FWSelectedThetaWitness (n : ℕ)
    (choice : Fin (fwJointRectangleCount n 254) → Bool) where
  family : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice
  p : Fin 3 → Equiv.Perm (Fin n)
  oldReference : Cell n ≃ Fin (n*n)
  roles : Finset (Cell n)
  derangement : ∀ i v, p i v ≠ v
  expansion : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
    500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card
  network : FWThetaNetworkWitness n family.stages.length
    family.hrect family.hseedrect family.hwide family.hoff family.hs choice
    family.br family.bc family.sr family.sc family.wr family.wc family.gr family.gc
    family.hbr family.hbc family.hsr family.hsc family.hwr family.hwc family.hgr family.hgc
    family.hrows family.hcols p family.ordered oldReference roles

/-- The rectangle choice used by the first-band theta construction. -/
def fwSelectedThetaChoice {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool) :
    Fin (fwJointRectangleCount n 254) → Bool :=
  let hrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).1
  let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.1
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  fwBridgeSeedRectangleChoice hrect hseedrect
    (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))

/-- Select a projected witness whose existence follows from theta. To apply the
conditional completion theorem, supply its DQ/RF input on this exact family's
ordered square and `fwThetaFamilyFull`, then apply
`fw_projected_theta_dqrf_all_line_flows` to this same record's fields. -/
def fwSelectedThetaWitness
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    FWSelectedThetaWitness n (fwSelectedThetaChoice hnlo otherChoice) := by
  classical
  have hexists : Nonempty (FWSelectedThetaWitness n (fwSelectedThetaChoice hnlo otherChoice)) := by
    have h := fw_theta_projected_join_witness mv bmor upper lower sharp upperSharp
      n hnlo hnhi otherChoice a seeds hseed hprime hcount
    dsimp only [fwSelectedThetaChoice] at h ⊢
    obtain ⟨f, p, b₀, roles, hder, hexp, ⟨network⟩⟩ := h
    exact ⟨⟨f, p, b₀, roles, hder, hexp, network⟩⟩
  exact Classical.choice hexists

end
end Sude
