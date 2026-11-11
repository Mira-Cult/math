import Sude.BitsetPrefix4096

/-! An independently kernel-checked scan of the next 4,096 candidates. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bitsetNext4096_checked :
    bitsetSegmentScan (canonicalPrimeBaseList 128) 8195 bitsetFirst4096Widths = (872, 10676000) := by
  decide +kernel

end
end Sude
