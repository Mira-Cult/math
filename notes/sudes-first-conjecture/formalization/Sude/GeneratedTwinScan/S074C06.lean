import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12490)) 155975725 156008493 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155975725 156008493).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12490 155975725 156008493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12491)) 156008493 156041261 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 156008493 156041261).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12491 156008493 156041261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12492)) 156041261 156074029 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 156041261 156074029).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12492 156041261 156074029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12494)) 156074029 156106797 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 156074029 156106797).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12494 156074029 156106797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155975725 156041261).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 155975725 ≤ 156008493)
    (by decide : 156008493 ≤ 156041261) block0 block1

theorem join_0_1 : (twinPrimeSegment 156041261 156106797).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 156041261 ≤ 156074029)
    (by decide : 156074029 ≤ 156106797) block2 block3

theorem join_1_0 : (twinPrimeSegment 155975725 156106797).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 155975725 ≤ 156041261)
    (by decide : 156041261 ≤ 156106797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155975725 156106797).card = 513 := join_1_0

end S074C06
end Sude.GeneratedTwinScan
