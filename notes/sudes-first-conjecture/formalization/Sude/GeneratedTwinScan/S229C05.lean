import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21930)) 480903213 480935981 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 480903213 480935981).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21930 480903213 480935981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21930)) 480935981 480968749 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 480935981 480968749).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21930 480935981 480968749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21931)) 480968749 481001517 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 480968749 481001517).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21931 480968749 481001517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21932)) 481001517 481034285 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481001517 481034285).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21932 481001517 481034285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 480903213 480968749).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 480903213 ≤ 480935981)
    (by decide : 480935981 ≤ 480968749) block0 block1

theorem join_0_1 : (twinPrimeSegment 480968749 481034285).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 480968749 ≤ 481001517)
    (by decide : 481001517 ≤ 481034285) block2 block3

theorem join_1_0 : (twinPrimeSegment 480903213 481034285).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 480903213 ≤ 480968749)
    (by decide : 480968749 ≤ 481034285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 480903213 481034285).card = 421 := join_1_0

end S229C05
end Sude.GeneratedTwinScan
