import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16504)) 272367661 272400429 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 272367661 272400429).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16504 272367661 272400429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16505)) 272400429 272433197 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272400429 272433197).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16505 272400429 272433197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16506)) 272433197 272465965 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272433197 272465965).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16506 272433197 272465965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16507)) 272465965 272498733 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272465965 272498733).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16507 272465965 272498733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 272367661 272433197).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 272367661 ≤ 272400429)
    (by decide : 272400429 ≤ 272433197) block0 block1

theorem join_0_1 : (twinPrimeSegment 272433197 272498733).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 272433197 ≤ 272465965)
    (by decide : 272465965 ≤ 272498733) block2 block3

theorem join_1_0 : (twinPrimeSegment 272367661 272498733).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 272367661 ≤ 272433197)
    (by decide : 272433197 ≤ 272498733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 272367661 272498733).card = 489 := join_1_0

end S129C14
end Sude.GeneratedTwinScan
