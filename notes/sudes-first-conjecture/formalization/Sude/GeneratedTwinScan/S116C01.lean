import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15602)) 243400749 243433517 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243400749 243433517).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15602 243400749 243433517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15603)) 243433517 243466285 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243433517 243466285).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15603 243433517 243466285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15604)) 243466285 243499053 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243466285 243499053).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15604 243466285 243499053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15605)) 243499053 243531821 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 243499053 243531821).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15605 243499053 243531821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243400749 243466285).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 243400749 ≤ 243433517)
    (by decide : 243433517 ≤ 243466285) block0 block1

theorem join_0_1 : (twinPrimeSegment 243466285 243531821).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 243466285 ≤ 243499053)
    (by decide : 243499053 ≤ 243531821) block2 block3

theorem join_1_0 : (twinPrimeSegment 243400749 243531821).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 243400749 ≤ 243466285)
    (by decide : 243466285 ≤ 243531821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243400749 243531821).card = 478 := join_1_0

end S116C01
end Sude.GeneratedTwinScan
