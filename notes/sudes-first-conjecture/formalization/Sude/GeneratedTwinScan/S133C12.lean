import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16748)) 280494125 280526893 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280494125 280526893).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16748 280494125 280526893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16749)) 280526893 280559661 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280526893 280559661).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16749 280526893 280559661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16750)) 280559661 280592429 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280559661 280592429).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16750 280559661 280592429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16751)) 280592429 280625197 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280592429 280625197).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16751 280592429 280625197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280494125 280559661).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 280494125 ≤ 280526893)
    (by decide : 280526893 ≤ 280559661) block0 block1

theorem join_0_1 : (twinPrimeSegment 280559661 280625197).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 280559661 ≤ 280592429)
    (by decide : 280592429 ≤ 280625197) block2 block3

theorem join_1_0 : (twinPrimeSegment 280494125 280625197).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 280494125 ≤ 280559661)
    (by decide : 280559661 ≤ 280625197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280494125 280625197).card = 493 := join_1_0

end S133C12
end Sude.GeneratedTwinScan
