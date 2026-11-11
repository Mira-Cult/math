import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17291)) 298975277 299008045 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298975277 299008045).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17291 298975277 299008045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17292)) 299008045 299040813 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299008045 299040813).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17292 299008045 299040813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17293)) 299040813 299073581 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299040813 299073581).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17293 299040813 299073581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17294)) 299073581 299106349 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299073581 299106349).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17294 299073581 299106349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298975277 299040813).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 298975277 ≤ 299008045)
    (by decide : 299008045 ≤ 299040813) block0 block1

theorem join_0_1 : (twinPrimeSegment 299040813 299106349).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 299040813 ≤ 299073581)
    (by decide : 299073581 ≤ 299106349) block2 block3

theorem join_1_0 : (twinPrimeSegment 298975277 299106349).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 298975277 ≤ 299040813)
    (by decide : 299040813 ≤ 299106349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298975277 299106349).card = 485 := join_1_0

end S142C09
end Sude.GeneratedTwinScan
