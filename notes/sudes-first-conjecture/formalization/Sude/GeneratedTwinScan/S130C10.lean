import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16552)) 273940525 273973293 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273940525 273973293).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16552 273940525 273973293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16553)) 273973293 274006061 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273973293 274006061).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16553 273973293 274006061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16554)) 274006061 274038829 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274006061 274038829).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16554 274006061 274038829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16555)) 274038829 274071597 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274038829 274071597).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16555 274038829 274071597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273940525 274006061).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 273940525 ≤ 273973293)
    (by decide : 273973293 ≤ 274006061) block0 block1

theorem join_0_1 : (twinPrimeSegment 274006061 274071597).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 274006061 ≤ 274038829)
    (by decide : 274038829 ≤ 274071597) block2 block3

theorem join_1_0 : (twinPrimeSegment 273940525 274071597).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 273940525 ≤ 274006061)
    (by decide : 274006061 ≤ 274071597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273940525 274071597).card = 459 := join_1_0

end S130C10
end Sude.GeneratedTwinScan
