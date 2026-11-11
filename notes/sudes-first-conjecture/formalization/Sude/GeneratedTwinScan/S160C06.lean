import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18340)) 336330797 336363565 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336330797 336363565).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18340 336330797 336363565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18341)) 336363565 336396333 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 336363565 336396333).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18341 336363565 336396333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18342)) 336396333 336429101 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336396333 336429101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18342 336396333 336429101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18342)) 336429101 336461869 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336429101 336461869).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18342 336429101 336461869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336330797 336396333).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 336330797 ≤ 336363565)
    (by decide : 336363565 ≤ 336396333) block0 block1

theorem join_0_1 : (twinPrimeSegment 336396333 336461869).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 336396333 ≤ 336429101)
    (by decide : 336429101 ≤ 336461869) block2 block3

theorem join_1_0 : (twinPrimeSegment 336330797 336461869).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 336330797 ≤ 336396333)
    (by decide : 336396333 ≤ 336461869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336330797 336461869).card = 435 := join_1_0

end S160C06
end Sude.GeneratedTwinScan
