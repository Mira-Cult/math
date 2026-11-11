import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15424)) 237895725 237928493 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 237895725 237928493).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15424 237895725 237928493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15425)) 237928493 237961261 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237928493 237961261).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15425 237928493 237961261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15427)) 237961261 237994029 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237961261 237994029).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15427 237961261 237994029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15428)) 237994029 238026797 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237994029 238026797).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15428 237994029 238026797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 237895725 237961261).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 237895725 ≤ 237928493)
    (by decide : 237928493 ≤ 237961261) block0 block1

theorem join_0_1 : (twinPrimeSegment 237961261 238026797).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 237961261 ≤ 237994029)
    (by decide : 237994029 ≤ 238026797) block2 block3

theorem join_1_0 : (twinPrimeSegment 237895725 238026797).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 237895725 ≤ 237961261)
    (by decide : 237961261 ≤ 238026797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 237895725 238026797).card = 488 := join_1_0

end S113C07
end Sude.GeneratedTwinScan
