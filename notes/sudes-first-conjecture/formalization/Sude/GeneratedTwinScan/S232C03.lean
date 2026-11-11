import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22067)) 486932525 486965293 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486932525 486965293).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22067 486932525 486965293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22068)) 486965293 486998061 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486965293 486998061).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22068 486965293 486998061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22068)) 486998061 487030829 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486998061 487030829).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22068 486998061 487030829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22069)) 487030829 487063597 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487030829 487063597).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22069 487030829 487063597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486932525 486998061).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 486932525 ≤ 486965293)
    (by decide : 486965293 ≤ 486998061) block0 block1

theorem join_0_1 : (twinPrimeSegment 486998061 487063597).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 486998061 ≤ 487030829)
    (by decide : 487030829 ≤ 487063597) block2 block3

theorem join_1_0 : (twinPrimeSegment 486932525 487063597).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 486932525 ≤ 486998061)
    (by decide : 486998061 ≤ 487063597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486932525 487063597).card = 426 := join_1_0

end S232C03
end Sude.GeneratedTwinScan
