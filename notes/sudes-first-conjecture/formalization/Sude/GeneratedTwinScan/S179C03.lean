import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19385)) 375783469 375816237 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 375783469 375816237).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19385 375783469 375816237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19386)) 375816237 375849005 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 375816237 375849005).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19386 375816237 375849005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19387)) 375849005 375881773 = 88 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 375849005 375881773).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19387 375849005 375881773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19388)) 375881773 375914541 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 375881773 375914541).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19388 375881773 375914541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 375783469 375849005).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 375783469 ≤ 375816237)
    (by decide : 375816237 ≤ 375849005) block0 block1

theorem join_0_1 : (twinPrimeSegment 375849005 375914541).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 375849005 ≤ 375881773)
    (by decide : 375881773 ≤ 375914541) block2 block3

theorem join_1_0 : (twinPrimeSegment 375783469 375914541).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 375783469 ≤ 375849005)
    (by decide : 375849005 ≤ 375914541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 375783469 375914541).card = 442 := join_1_0

end S179C03
end Sude.GeneratedTwinScan
