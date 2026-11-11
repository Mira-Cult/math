import Sude.StageLineExplicitMean
import Sude.StageDoubleBlockReallocation
import Sude.PhysicalPairLineSum
import Sude.FairBlockSwap

/-! Exact physical midpoint score for stage-wise double-block reallocations.
No probability, slot geometry, grid preservation or reallocation existence is
asserted here. A single Boolean exchanges the two pairs of a destination block;
it does not reverse either pair's endpoint orientation. -/
namespace Sude
noncomputable section

/-- Exchange the two pair positions when requested, preserving endpoint sides. -/
def doubleBlockPairSwap (s : Bool) : Equiv.Perm (Fin 2) :=
  if s then Equiv.swap 0 1 else Equiv.refl _

/-- Pair midpoint on a given square and fixed map of physical slots. -/
def doubleBlockPairMidpoint {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n * n)) (j : Fin P) (b : Fin B) (p : Fin 2) : ℝ :=
  ((entry a (cells ((j,b,p), false)) : ℝ) + entry a (cells ((j,b,p), true))) / 2

/-- The mean of the two source pair midpoints in a double block. -/
def doubleBlockMidpoint {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n * n)) (j : Fin P) (b : Fin B) : ℝ :=
  (doubleBlockPairMidpoint cells a j b 0 + doubleBlockPairMidpoint cells a j b 1) / 2

/-- The actual mean of the selected source pair midpoints in one stage. -/
def doubleStageMidpointMean {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n * n)) (j : Fin P) : ℝ :=
  (∑ b, doubleBlockMidpoint cells a j b) / (B : ℝ)

/-- The destination line weight of a complete two-pair block. -/
def doubleBlockLineWeight {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (j : Fin P) (b : Fin B) : ℝ :=
  physicalPairLineWeight cells line (j,b,0) + physicalPairLineWeight cells line (j,b,1)

/-- A single physical block's weighted midpoint score is the fair-swap
expression for its two selected source midpoints. -/
theorem double_block_weighted_midpoint_eq_swap {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) (s : Fin P → Fin B → Bool)
    (hentry : ∀ j b p side, entry new (cells ((j,b,p),side)) =
      entry old (cells ((j,π j b, doubleBlockPairSwap (s j b) p),side)))
    (j : Fin P) (b : Fin B) :
    (∑ p, physicalPairLineWeight cells line (j,b,p) * doubleBlockPairMidpoint cells new j b p) =
      fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
        (doubleBlockPairMidpoint cells old j (π j b) 1)
        (physicalPairLineWeight cells line (j,b,0))
        (physicalPairLineWeight cells line (j,b,1)) (s j b) := by
  classical
  simp only [Fin.sum_univ_two, doubleBlockPairMidpoint, hentry]
  cases s j b <;> simp [fairBlockSwapValue, doubleBlockPairSwap]


/-- The actual centered weighted midpoint score splits exactly into the
centered permutation score of block means and a sum of shared fair-swap
scores. Stage means are computed from the old square's selected population. -/
theorem double_block_midpoint_score_decomposition {n P B : ℕ} (hB : 0 < B)
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) (s : Fin P → Fin B → Bool)
    (hentry : ∀ j b p side, entry new (cells ((j,b,p),side)) =
      entry old (cells ((j,π j b, doubleBlockPairSwap (s j b) p),side))) :
    (∑ j, ∑ b, ((∑ p, physicalPairLineWeight cells line (j,b,p) *
      doubleBlockPairMidpoint cells new j b p) -
      doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j)) =
    (∑ j, stageWeightedCentered (fun _ => Finset.univ) (doubleBlockLineWeight cells line)
      (doubleBlockMidpoint cells old) j (π j)) +
    ∑ j, ∑ b, (fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
      (doubleBlockPairMidpoint cells old j (π j b) 1)
      (physicalPairLineWeight cells line (j,b,0)) (physicalPairLineWeight cells line (j,b,1)) (s j b) -
      doubleBlockLineWeight cells line j b * doubleBlockMidpoint cells old j (π j b)) := by
  classical
  have hblock (j : Fin P) (b : Fin B) :
      (∑ p, physicalPairLineWeight cells line (j,b,p) * doubleBlockPairMidpoint cells new j b p) -
        doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j =
      doubleBlockLineWeight cells line j b *
        (doubleBlockMidpoint cells old j (π j b) - doubleStageMidpointMean cells old j) +
      (fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
        (doubleBlockPairMidpoint cells old j (π j b) 1)
        (physicalPairLineWeight cells line (j,b,0)) (physicalPairLineWeight cells line (j,b,1)) (s j b) -
        doubleBlockLineWeight cells line j b * doubleBlockMidpoint cells old j (π j b)) := by
    rw [double_block_weighted_midpoint_eq_swap cells line old new π s hentry j b]
    ring
  calc
    _ = ∑ j, ∑ b, (doubleBlockLineWeight cells line j b *
          (doubleBlockMidpoint cells old j (π j b) - doubleStageMidpointMean cells old j) +
        (fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
          (doubleBlockPairMidpoint cells old j (π j b) 1)
          (physicalPairLineWeight cells line (j,b,0)) (physicalPairLineWeight cells line (j,b,1)) (s j b) -
          doubleBlockLineWeight cells line j b * doubleBlockMidpoint cells old j (π j b))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_congr rfl (fun b _ => hblock j b)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [stageWeightedCentered_eq_explicit_mean hB]
      simp only [doubleStageMidpointMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]


/-- The selected physical line sum has the same two midpoint terms plus its
separate signed half-gap orientation term. Injectivity is needed only to
identify the sum over the image with the sum over labelled endpoints. -/
theorem double_block_physical_line_score_decomposition {n P B : ℕ} (hB : 0 < B)
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line] (old new : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) (s : Fin P → Fin B → Bool)
    (hentry : ∀ j b p side, entry new (cells ((j,b,p),side)) =
      entry old (cells ((j,π j b, doubleBlockPairSwap (s j b) p),side))) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry new c : ℝ)) -
      (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) =
    (∑ j, stageWeightedCentered (fun _ => Finset.univ) (doubleBlockLineWeight cells line)
      (doubleBlockMidpoint cells old) j (π j)) +
    (∑ j, ∑ b, (fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
      (doubleBlockPairMidpoint cells old j (π j b) 1)
      (physicalPairLineWeight cells line (j,b,0)) (physicalPairLineWeight cells line (j,b,1)) (s j b) -
      doubleBlockLineWeight cells line j b * doubleBlockMidpoint cells old j (π j b))) +
    ∑ j, ∑ b, ∑ p, physicalPairLineOrientation cells line (j,b,p) *
      (((entry new (cells ((j,b,p),true)) : ℝ) - entry new (cells ((j,b,p),false))) / 2) := by
  classical
  have hmid : (∑ c ∈ (Finset.univ.image cells).filter line, (entry new c : ℝ)) =
      (∑ j, ∑ b, ∑ p, physicalPairLineWeight cells line (j,b,p) *
        doubleBlockPairMidpoint cells new j b p) +
      (∑ j, ∑ b, ∑ p, physicalPairLineOrientation cells line (j,b,p) *
        (((entry new (cells ((j,b,p),true)) : ℝ) - entry new (cells ((j,b,p),false))) / 2)) := by
    simpa only [Fintype.sum_prod_type, Finset.sum_add_distrib, doubleBlockPairMidpoint] using
      physicalPair_line_sum_midpoint cells hcells line new
  have hscore := double_block_midpoint_score_decomposition hB cells line old new π s hentry
  simp only [Finset.sum_sub_distrib] at hscore
  rw [hmid]
  simp only [Finset.sum_sub_distrib]
  linarith


end
end Sude
