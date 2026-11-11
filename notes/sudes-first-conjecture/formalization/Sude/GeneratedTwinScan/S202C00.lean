import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20582)) 423624749 423657517 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423624749 423657517).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20582 423624749 423657517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20583)) 423657517 423690285 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423657517 423690285).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20583 423657517 423690285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20584)) 423690285 423723053 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423690285 423723053).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20584 423690285 423723053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20585)) 423723053 423755821 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423723053 423755821).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20585 423723053 423755821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423624749 423690285).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 423657517)
    (by decide : 423657517 ≤ 423690285) block0 block1

theorem join_0_1 : (twinPrimeSegment 423690285 423755821).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 423690285 ≤ 423723053)
    (by decide : 423723053 ≤ 423755821) block2 block3

theorem join_1_0 : (twinPrimeSegment 423624749 423755821).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 423690285)
    (by decide : 423690285 ≤ 423755821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423624749 423755821).card = 414 := join_1_0

end S202C00
end Sude.GeneratedTwinScan
