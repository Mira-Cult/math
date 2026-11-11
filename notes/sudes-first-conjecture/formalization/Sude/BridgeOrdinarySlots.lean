import Sude.BridgeRectangleAllocation
import Sude.LayerNetworks

/-! Allocate the ordinary bridge pairs to both physical networks without
reusing any of the 4d blocks reserved for diagonal rectangles. -/
namespace Sude
noncomputable section

/-- The first 4d blocks are diagonal blocks; subsequent blocks supply one
ordinary pair to each of the row and column networks. -/
def bridgeOrdinaryBlockIndex {r n d k : ℕ} (hfit : 4 * d + r * n ≤ k)
    (x : Fin r × Fin n) : Fin k :=
  ⟨4 * d + (finProdFinEquiv x).val, by have h := (finProdFinEquiv x).isLt; omega⟩

theorem bridgeOrdinaryBlockIndex_injective {r n d k : ℕ} (hfit : 4 * d + r * n ≤ k) :
    Function.Injective (bridgeOrdinaryBlockIndex hfit) := by
  intro x y heq
  apply finProdFinEquiv.injective
  apply Fin.ext
  have h := congrArg Fin.val heq
  change 4 * d + (finProdFinEquiv x).val = 4 * d + (finProdFinEquiv y).val at h
  omega

/-- `network=false` uses the first pair; `network=true` uses the second.
`high=true` always denotes the larger entry of that pair. -/
def bridgeOrdinarySide (x : Bool × Bool) : Fin 4 :=
  if x.1 then (if x.2 then 2 else 3) else (if x.2 then 1 else 0)

theorem bridgeOrdinarySide_injective : Function.Injective bridgeOrdinarySide := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [bridgeOrdinarySide]

/-- A network/edge/side slot points to the corresponding physical
stage/block/endpoint slot from the already selected bridge history. -/
def bridgeOrdinarySlot {J r n d k : ℕ} (hfit : 4 * d + r * n ≤ k)
    (x : (Fin J × (Fin r × Fin n)) × (Bool × Bool)) : (Fin J × Fin k) × Fin 4 :=
  ((x.1.1, bridgeOrdinaryBlockIndex hfit x.1.2), bridgeOrdinarySide x.2)

theorem bridgeOrdinarySlot_injective {J r n d k : ℕ} (hfit : 4 * d + r * n ≤ k) :
    Function.Injective (bridgeOrdinarySlot (J := J) hfit) := by
  rintro ⟨⟨j, p⟩, side⟩ ⟨⟨j', p'⟩, side'⟩ heq
  have hfirst := congrArg (fun z : (Fin J × Fin k) × Fin 4 => z.1) heq
  have hstage : j = j' := congrArg Prod.fst hfirst
  have hblock : bridgeOrdinaryBlockIndex hfit p = bridgeOrdinaryBlockIndex hfit p' :=
    congrArg Prod.snd hfirst
  have hp : p = p' := bridgeOrdinaryBlockIndex_injective hfit hblock
  have hside : side = side' := bridgeOrdinarySide_injective (congrArg Prod.snd heq)
  subst j'
  subst p'
  subst side'
  rfl

/-- No ordinary network slot refers to a diagonal rectangle block. -/
theorem bridgeOrdinarySlot_ne_diagonal {J r n d k : ℕ} (hfit : 4 * d + r * n ≤ k)
    (hdiag : 4 * d ≤ k) (x : (Fin J × (Fin r × Fin n)) × (Bool × Bool))
    (t : Fin (J * (4 * d))) (side : Fin 4) :
    bridgeOrdinarySlot hfit x ≠ (bridgeDiagonalBlockSelect hdiag t, side) := by
  intro heq
  have hblock := congrArg (fun z : (Fin J × Fin k) × Fin 4 => z.1.2.val) heq
  have hlarge : 4 * d ≤ (bridgeOrdinaryBlockIndex hfit x.1.2).val := by
    simp [bridgeOrdinaryBlockIndex]
  have hsmall : (bridgeDiagonalBlockSelect hdiag t).2.val < 4 * d := by
    exact (finProdFinEquiv.symm t : Fin J × Fin (4 * d)).2.isLt
  change (bridgeOrdinaryBlockIndex hfit x.1.2).val =
    (bridgeDiagonalBlockSelect hdiag t).2.val at hblock
  omega

/-- The actual prime value for an ordinary network slot. -/
def bridgeOrdinaryEndpoint {J r n d k : ℕ} (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k)
    (x : (Fin J × (Fin r × Fin n)) × (Bool × Bool)) : ℕ :=
  bridgeStageEndpoint n initial radii batches k J hvalid (bridgeOrdinarySlot hfit x)

theorem bridgeOrdinaryEndpoint_injective {J r n d k : ℕ} (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hpositive : ∀ j < J, 0 < radii j) :
    Function.Injective (bridgeOrdinaryEndpoint initial radii batches hvalid hfit) := by
  intro x y heq
  apply bridgeOrdinarySlot_injective hfit
  apply bridgeStageEndpoint_injective n initial radii batches k J hvalid hpositive
  exact heq

theorem bridgeOrdinaryEndpoint_pool_avoids {J r n d k : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j)
    (x : (Fin J × (Fin r × Fin n)) × (Bool × Bool)) :
    bridgeOrdinaryEndpoint initial radii batches hvalid hfit x ∈ pool n ∧
      bridgeOrdinaryEndpoint initial radii batches hvalid hfit x ∉ initial :=
  bridgeStageEndpoint_pool_avoids bmor upper n initial radii batches k J hvalid
    hn hnmax hpositive (bridgeOrdinarySlot hfit x)

/-- Every ordinary endpoint differs from every allocated diagonal endpoint. -/
theorem bridgeOrdinaryEndpoint_ne_diagonal {J r n d k : ℕ} (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (hdiag : 4 * d ≤ k)
    (hpositive : ∀ j < J, 0 < radii j)
    (x : (Fin J × (Fin r × Fin n)) × (Bool × Bool))
    (t : Fin (J * (4 * d))) (side : Fin 4) :
    bridgeOrdinaryEndpoint initial radii batches hvalid hfit x ≠
      bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hdiag t, side) := by
  intro heq
  apply bridgeOrdinarySlot_ne_diagonal hfit hdiag x t side
  exact bridgeStageEndpoint_injective n initial radii batches k J hvalid hpositive heq

/-- The row and column pair from one ordinary block both have its actual
positive even gap, with the high and low endpoint orientation explicit. -/
theorem bridgeOrdinary_pair_gap {J r n d k : ℕ} (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hfit : 4 * d + r * n ≤ k) (j : Fin J) (p : Fin r × Fin n) (network : Bool) :
    let g := selectedBridgeGap batches (bridgeOrdinaryBlockIndex hfit p) j
    0 < g ∧ 2 ∣ g ∧
      bridgeOrdinaryEndpoint initial radii batches hvalid hfit ((j, p), (network, true)) =
        bridgeOrdinaryEndpoint initial radii batches hvalid hfit ((j, p), (network, false)) + g := by
  let i := bridgeOrdinaryBlockIndex hfit p
  let b := bridgeStageBlock n initial radii batches k J hvalid j i
  have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j i
  have hstage := (hvalid j j.isLt).2.2.2 b (bridgeStageBlock_mem n initial radii batches k J hvalid j i)
  have hgap := bridgeStageBlock_gap n initial radii batches k J hvalid j i
  rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
  refine ⟨by rw [hgap]; omega, by rw [hgap]; exact hstage.1, ?_⟩
  cases network
  · change b.high₁ = b.low₁ + selectedBridgeGap batches i j
    rw [hgap]
    dsimp only [b] at *
    omega
  · change b.high₂ = b.low₂ + selectedBridgeGap batches i j
    rw [hgap]
    dsimp only [b] at *
    omega

/-- FC2K's Q=6(n+8) splits exactly into 4d=24 double blocks for
diagonals and 3n double blocks, each supplying two ordinary pairs. -/
theorem fc2k_bridge_ordinary_blocks_fit (n : ℕ) :
    4 * 6 + 3 * n ≤ (6 * (n + 8)) / 2 := by omega

end
end Sude
