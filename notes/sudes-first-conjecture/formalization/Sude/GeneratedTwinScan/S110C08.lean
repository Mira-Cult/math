import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15223)) 231735341 231768109 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231735341 231768109).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15223 231735341 231768109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15225)) 231768109 231800877 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231768109 231800877).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15225 231768109 231800877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15226)) 231800877 231833645 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231800877 231833645).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15226 231800877 231833645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15227)) 231833645 231866413 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231833645 231866413).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15227 231833645 231866413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231735341 231800877).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 231735341 ≤ 231768109)
    (by decide : 231768109 ≤ 231800877) block0 block1

theorem join_0_1 : (twinPrimeSegment 231800877 231866413).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 231800877 ≤ 231833645)
    (by decide : 231833645 ≤ 231866413) block2 block3

theorem join_1_0 : (twinPrimeSegment 231735341 231866413).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 231735341 ≤ 231800877)
    (by decide : 231800877 ≤ 231866413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231735341 231866413).card = 432 := join_1_0

end S110C08
end Sude.GeneratedTwinScan
