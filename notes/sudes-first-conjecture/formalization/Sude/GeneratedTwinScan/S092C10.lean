import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13938)) 194248749 194281517 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 194248749 194281517).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13938 194248749 194281517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13939)) 194281517 194314285 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194281517 194314285).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13939 194281517 194314285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13940)) 194314285 194347053 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194314285 194347053).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13940 194314285 194347053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13942)) 194347053 194379821 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194347053 194379821).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13942 194347053 194379821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 194248749 194314285).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 194248749 ≤ 194281517)
    (by decide : 194281517 ≤ 194314285) block0 block1

theorem join_0_1 : (twinPrimeSegment 194314285 194379821).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 194314285 ≤ 194347053)
    (by decide : 194347053 ≤ 194379821) block2 block3

theorem join_1_0 : (twinPrimeSegment 194248749 194379821).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 194248749 ≤ 194314285)
    (by decide : 194314285 ≤ 194379821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 194248749 194379821).card = 496 := join_1_0

end S092C10
end Sude.GeneratedTwinScan
