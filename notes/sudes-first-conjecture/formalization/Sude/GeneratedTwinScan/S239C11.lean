import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22420)) 502661165 502693933 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502661165 502693933).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22420 502661165 502693933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22421)) 502693933 502726701 = 85 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502693933 502726701).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22421 502693933 502726701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22422)) 502726701 502759469 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502726701 502759469).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22422 502726701 502759469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22423)) 502759469 502792237 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502759469 502792237).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22423 502759469 502792237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502661165 502726701).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 502661165 ≤ 502693933)
    (by decide : 502693933 ≤ 502726701) block0 block1

theorem join_0_1 : (twinPrimeSegment 502726701 502792237).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 502726701 ≤ 502759469)
    (by decide : 502759469 ≤ 502792237) block2 block3

theorem join_1_0 : (twinPrimeSegment 502661165 502792237).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 502661165 ≤ 502726701)
    (by decide : 502726701 ≤ 502792237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502661165 502792237).card = 414 := join_1_0

end S239C11
end Sude.GeneratedTwinScan
