import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20576)) 423362605 423395373 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423362605 423395373).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20576 423362605 423395373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20577)) 423395373 423428141 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423395373 423428141).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20577 423395373 423428141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20578)) 423428141 423460909 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423428141 423460909).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20578 423428141 423460909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20578)) 423460909 423493677 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423460909 423493677).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20578 423460909 423493677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423362605 423428141).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 423362605 ≤ 423395373)
    (by decide : 423395373 ≤ 423428141) block0 block1

theorem join_0_1 : (twinPrimeSegment 423428141 423493677).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 423428141 ≤ 423460909)
    (by decide : 423460909 ≤ 423493677) block2 block3

theorem join_1_0 : (twinPrimeSegment 423362605 423493677).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 423362605 ≤ 423428141)
    (by decide : 423428141 ≤ 423493677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423362605 423493677).card = 416 := join_1_0

end S201C14
end Sude.GeneratedTwinScan
