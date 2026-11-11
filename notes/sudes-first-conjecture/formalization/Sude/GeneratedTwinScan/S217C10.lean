import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21364)) 456392749 456425517 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456392749 456425517).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21364 456392749 456425517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21364)) 456425517 456458285 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456425517 456458285).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21364 456425517 456458285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21365)) 456458285 456491053 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456458285 456491053).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21365 456458285 456491053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21366)) 456491053 456523821 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 456491053 456523821).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21366 456491053 456523821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456392749 456458285).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 456392749 ≤ 456425517)
    (by decide : 456425517 ≤ 456458285) block0 block1

theorem join_0_1 : (twinPrimeSegment 456458285 456523821).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 456458285 ≤ 456491053)
    (by decide : 456491053 ≤ 456523821) block2 block3

theorem join_1_0 : (twinPrimeSegment 456392749 456523821).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 456392749 ≤ 456458285)
    (by decide : 456458285 ≤ 456523821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456392749 456523821).card = 469 := join_1_0

end S217C10
end Sude.GeneratedTwinScan
