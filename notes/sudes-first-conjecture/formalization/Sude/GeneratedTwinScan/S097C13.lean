import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14323)) 205127725 205160493 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205127725 205160493).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14323 205127725 205160493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14324)) 205160493 205193261 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205160493 205193261).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14324 205160493 205193261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14325)) 205193261 205226029 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205193261 205226029).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14325 205193261 205226029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14326)) 205226029 205258797 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205226029 205258797).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14326 205226029 205258797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205127725 205193261).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 205127725 ≤ 205160493)
    (by decide : 205160493 ≤ 205193261) block0 block1

theorem join_0_1 : (twinPrimeSegment 205193261 205258797).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 205193261 ≤ 205226029)
    (by decide : 205226029 ≤ 205258797) block2 block3

theorem join_1_0 : (twinPrimeSegment 205127725 205258797).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 205127725 ≤ 205193261)
    (by decide : 205193261 ≤ 205258797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205127725 205258797).card = 441 := join_1_0

end S097C13
end Sude.GeneratedTwinScan
