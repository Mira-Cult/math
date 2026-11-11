import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12390)) 153485357 153518125 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153485357 153518125).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12390 153485357 153518125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12391)) 153518125 153550893 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153518125 153550893).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12391 153518125 153550893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12392)) 153550893 153583661 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153550893 153583661).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12392 153550893 153583661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12394)) 153583661 153616429 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153583661 153616429).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12394 153583661 153616429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153485357 153550893).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 153485357 ≤ 153518125)
    (by decide : 153518125 ≤ 153550893) block0 block1

theorem join_0_1 : (twinPrimeSegment 153550893 153616429).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 153550893 ≤ 153583661)
    (by decide : 153583661 ≤ 153616429) block2 block3

theorem join_1_0 : (twinPrimeSegment 153485357 153616429).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 153485357 ≤ 153550893)
    (by decide : 153550893 ≤ 153616429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153485357 153616429).card = 514 := join_1_0

end S073C03
end Sude.GeneratedTwinScan
