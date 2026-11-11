import Sude.FWControllerStageReindex
import Sude.PhysicalPairLineSum

/-! Stage-preserving reindexing of squared physical pair incidences from
block/pair labels through controller labels to prefix slot labels. No
geometric upper bound or choice of physical line is asserted. -/
namespace Sude
noncomputable section

/-- Within one stage, block and pair labels bijectively index all controller
pair slots. This is the stage component of `fwBlockPairIndex`. -/
def fwGroupedStagePairEquiv (n : ℕ) :
    (Fin (3 * (n + 8)) × Fin 2) ≃ Fin (6 * (n + 8)) :=
  finProdFinEquiv.trans (finCongr (by omega))

/-- Grouping pair slots into blocks preserves each stage's squared physical
line-incidence sum, for any supplied cell map and line. -/
theorem fw_grouped_stage_squared_pair_mass {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (line : Cell n → Prop) (j : Fin P) :
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (cells ∘ fwBlockPairIndex P n) line (j,b,p)) ^ 2) =
      ∑ q, (physicalPairLineWeight cells line (j,q)) ^ 2 := by
  classical
  calc
    _ = ∑ x : Fin (3 * (n + 8)) × Fin 2,
        (physicalPairLineWeight cells line (j,fwGroupedStagePairEquiv n x)) ^ 2 := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := Equiv.sum_comp (fwGroupedStagePairEquiv n)
      (fun q => (physicalPairLineWeight cells line (j,q)) ^ 2)

/-- The same squared mass in reviewed prefix slot order. Endpoint sides and
stage labels remain fixed by both regroupings. -/
theorem fw_grouped_prefix_stage_squared_pair_mass {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (line : Cell n → Prop) (j : Fin P) :
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (cells ∘ fwBlockPairIndex P n) line (j,b,p)) ^ 2) =
    ∑ q, (physicalPairLineWeight cells line (j,fwPrefixToControllerPair n q)) ^ 2 := by
  classical
  rw [fw_grouped_stage_squared_pair_mass]
  exact (fw_controller_stage_squared_invoice cells line j).symm

/-- Arbitrary stage-specific width factors remain attached to the same stage
through the two reindexings. -/
theorem fw_grouped_prefix_weighted_squared_pair_mass {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (line : Cell n → Prop) (width : Fin P → ℝ) :
    (∑ j, (width j) ^ 2 * ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (cells ∘ fwBlockPairIndex P n) line (j,b,p)) ^ 2) =
    ∑ j, (width j) ^ 2 * ∑ q,
      (physicalPairLineWeight cells line (j,fwPrefixToControllerPair n q)) ^ 2 := by
  classical
  simp_rw [fw_grouped_prefix_stage_squared_pair_mass]

end
end Sude
