import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20329)) 413270061 413302829 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 413270061 413302829).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20329 413270061 413302829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20330)) 413302829 413335597 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 413302829 413335597).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20330 413302829 413335597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20331)) 413335597 413368365 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 413335597 413368365).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20331 413335597 413368365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20332)) 413368365 413401133 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 413368365 413401133).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20332 413368365 413401133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 413270061 413335597).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 413270061 ≤ 413302829)
    (by decide : 413302829 ≤ 413335597) block0 block1

theorem join_0_1 : (twinPrimeSegment 413335597 413401133).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 413335597 ≤ 413368365)
    (by decide : 413368365 ≤ 413401133) block2 block3

theorem join_1_0 : (twinPrimeSegment 413270061 413401133).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 413270061 ≤ 413335597)
    (by decide : 413335597 ≤ 413401133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 413270061 413401133).card = 436 := join_1_0

end S197C01
end Sude.GeneratedTwinScan
