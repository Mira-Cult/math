import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14796)) 218890285 218923053 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 218890285 218923053).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14796 218890285 218923053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14797)) 218923053 218955821 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218923053 218955821).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14797 218923053 218955821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14798)) 218955821 218988589 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218955821 218988589).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14798 218955821 218988589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14799)) 218988589 219021357 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218988589 219021357).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14799 218988589 219021357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 218890285 218955821).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 218890285 ≤ 218923053)
    (by decide : 218923053 ≤ 218955821) block0 block1

theorem join_0_1 : (twinPrimeSegment 218955821 219021357).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 218955821 ≤ 218988589)
    (by decide : 218988589 ≤ 219021357) block2 block3

theorem join_1_0 : (twinPrimeSegment 218890285 219021357).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 218890285 ≤ 218955821)
    (by decide : 218955821 ≤ 219021357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 218890285 219021357).card = 465 := join_1_0

end S104C06
end Sude.GeneratedTwinScan
