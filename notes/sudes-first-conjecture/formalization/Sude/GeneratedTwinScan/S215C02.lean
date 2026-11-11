import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21241)) 451149869 451182637 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 451149869 451182637).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21241 451149869 451182637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21241)) 451182637 451215405 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 451182637 451215405).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21241 451182637 451215405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21242)) 451215405 451248173 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 451215405 451248173).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21242 451215405 451248173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21243)) 451248173 451280941 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 451248173 451280941).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21243 451248173 451280941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 451149869 451215405).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 451149869 ≤ 451182637)
    (by decide : 451182637 ≤ 451215405) block0 block1

theorem join_0_1 : (twinPrimeSegment 451215405 451280941).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 451215405 ≤ 451248173)
    (by decide : 451248173 ≤ 451280941) block2 block3

theorem join_1_0 : (twinPrimeSegment 451149869 451280941).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 451149869 ≤ 451215405)
    (by decide : 451215405 ≤ 451280941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 451149869 451280941).card = 441 := join_1_0

end S215C02
end Sude.GeneratedTwinScan
