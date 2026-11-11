import Sude.FWThetaProjectedCrossWitness
import Sude.FWSelectedThetaWitness

/-! Select a single theta witness whose crossing bound, family, network,
growth selection and role inputs all come from one theta invocation. It is
not identified with earlier selectors. The DQ/RF numerical and stock gates,
prime targets and later-flow line bounds remain unproved. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- One crossing witness with all dependent components on its same family. -/
structure FWSelectedCrossThetaWitness (n : ℕ)
    (choice : Fin (fwJointRectangleCount n 254) → Bool) (seeds : Finset ℕ) where
  family : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice
  p : Fin 3 → Equiv.Perm (Fin n)
  oldReference : Cell n ≃ Fin (n*n)
  roles : Finset (Cell n)
  derangement : ∀ i v, p i v ≠ v
  expansion : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
    500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card
  cross : (poolMaximum n : ℝ) / 23 ≤ family.last
  network : FWThetaNetworkWitness n family.stages.length
    family.hrect family.hseedrect family.hwide family.hoff family.hs choice
    family.br family.bc family.sr family.sc family.wr family.wc family.gr family.gc
    family.hbr family.hbc family.hsr family.hsc family.hwr family.hwc family.hgr family.hgc
    family.hrows family.hcols p family.ordered oldReference roles
  diagonal : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice family
  roleInputs : FWThetaRoleValueInputs family seeds

/-- Select one crossing witness guaranteed by the supplied theta and seed
hypotheses. Further gates must be supplied for this exact selected family. -/
def fwSelectedCrossThetaWitness
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    FWSelectedCrossThetaWitness n (fwSelectedThetaChoice hnlo otherChoice) seeds := by
  classical
  have hexists : Nonempty (FWSelectedCrossThetaWitness n (fwSelectedThetaChoice hnlo otherChoice) seeds) := by
    have h := fw_theta_projected_cross_witness mv bmor upper lower sharp upperSharp
      n hnlo hnhi otherChoice a seeds hseed hprime hcount
    dsimp only [fwSelectedThetaChoice] at h ⊢
    obtain ⟨f, p, b₀, roles, hder, hexp, hcross, ⟨network⟩, ⟨diagonal⟩, ⟨roleInputs⟩⟩ := h
    exact ⟨⟨f, p, b₀, roles, hder, hexp, hcross, network, diagonal, roleInputs⟩⟩
  exact Classical.choice hexists

end
end Sude
