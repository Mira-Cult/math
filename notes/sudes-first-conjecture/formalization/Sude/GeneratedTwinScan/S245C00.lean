import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22667)) 513802285 513835053 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513802285 513835053).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22667 513802285 513835053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22668)) 513835053 513867821 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513835053 513867821).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22668 513835053 513867821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22669)) 513867821 513900589 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513867821 513900589).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22669 513867821 513900589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22670)) 513900589 513933357 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513900589 513933357).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22670 513900589 513933357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513802285 513867821).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 513802285 ≤ 513835053)
    (by decide : 513835053 ≤ 513867821) block0 block1

theorem join_0_1 : (twinPrimeSegment 513867821 513933357).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 513867821 ≤ 513900589)
    (by decide : 513900589 ≤ 513933357) block2 block3

theorem join_1_0 : (twinPrimeSegment 513802285 513933357).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 513802285 ≤ 513867821)
    (by decide : 513867821 ≤ 513933357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513802285 513933357).card = 436 := join_1_0

end S245C00
end Sude.GeneratedTwinScan
