import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22315)) 497942573 497975341 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497942573 497975341).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22315 497942573 497975341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22316)) 497975341 498008109 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497975341 498008109).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22316 497975341 498008109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22316)) 498008109 498040877 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498008109 498040877).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22316 498008109 498040877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22317)) 498040877 498073645 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498040877 498073645).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22317 498040877 498073645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497942573 498008109).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 497942573 ≤ 497975341)
    (by decide : 497975341 ≤ 498008109) block0 block1

theorem join_0_1 : (twinPrimeSegment 498008109 498073645).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 498008109 ≤ 498040877)
    (by decide : 498040877 ≤ 498073645) block2 block3

theorem join_1_0 : (twinPrimeSegment 497942573 498073645).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 497942573 ≤ 498008109)
    (by decide : 498008109 ≤ 498073645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497942573 498073645).card = 437 := join_1_0

end S237C07
end Sude.GeneratedTwinScan
