import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21605)) 466747437 466780205 = 88 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 466747437 466780205).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21605 466747437 466780205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21605)) 466780205 466812973 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 466780205 466812973).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21605 466780205 466812973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21606)) 466812973 466845741 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 466812973 466845741).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21606 466812973 466845741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21607)) 466845741 466878509 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 466845741 466878509).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21607 466845741 466878509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 466747437 466812973).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 466747437 ≤ 466780205)
    (by decide : 466780205 ≤ 466812973) block0 block1

theorem join_0_1 : (twinPrimeSegment 466812973 466878509).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 466812973 ≤ 466845741)
    (by decide : 466845741 ≤ 466878509) block2 block3

theorem join_1_0 : (twinPrimeSegment 466747437 466878509).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 466747437 ≤ 466812973)
    (by decide : 466812973 ≤ 466878509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 466747437 466878509).card = 448 := join_1_0

end S222C09
end Sude.GeneratedTwinScan
