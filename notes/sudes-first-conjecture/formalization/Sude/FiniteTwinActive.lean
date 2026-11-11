import Sude.ActiveTwinBase
import Sude.FiniteTwinFlexible

/-! The active-base checker feeds the exact finite source count. -/
namespace Sude
noncomputable section

/-- A kernel-accepted active-base scan of any exact partition would prove
the FT population. The scan acceptance is an internal obligation. -/
theorem finiteTwinSeeds_count_of_active_partition (base : List ℕ) (widths : List ℕ)
    (hbase : CompletePrimeBase base.toFinset 32768)
    (hwidth : widths.sum = 536870889)
    (hscan : activeStreamingTwinScan base 45 widths = 3650551) :
    finiteTwinSeeds.card = 3650551 := by
  apply finiteTwinSeeds_count_of_partition base widths hbase hwidth
  rw [← activeStreamingTwinScan_eq]
  exact hscan

end
end Sude
