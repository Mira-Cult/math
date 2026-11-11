import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18110)) 327942189 327974957 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327942189 327974957).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18110 327942189 327974957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18110)) 327974957 328007725 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327974957 328007725).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18110 327974957 328007725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18111)) 328007725 328040493 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 328007725 328040493).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18111 328007725 328040493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18112)) 328040493 328073261 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 328040493 328073261).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18112 328040493 328073261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327942189 328007725).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 327942189 ≤ 327974957)
    (by decide : 327974957 ≤ 328007725) block0 block1

theorem join_0_1 : (twinPrimeSegment 328007725 328073261).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 328007725 ≤ 328040493)
    (by decide : 328040493 ≤ 328073261) block2 block3

theorem join_1_0 : (twinPrimeSegment 327942189 328073261).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 327942189 ≤ 328007725)
    (by decide : 328007725 ≤ 328073261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327942189 328073261).card = 445 := join_1_0

end S156C06
end Sude.GeneratedTwinScan
