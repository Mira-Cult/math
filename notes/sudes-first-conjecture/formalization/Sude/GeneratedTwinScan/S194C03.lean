import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20181)) 407240749 407273517 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 407240749 407273517).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20181 407240749 407273517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20181)) 407273517 407306285 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407273517 407306285).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20181 407273517 407306285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20182)) 407306285 407339053 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407306285 407339053).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20182 407306285 407339053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20183)) 407339053 407371821 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407339053 407371821).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20183 407339053 407371821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 407240749 407306285).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 407240749 ≤ 407273517)
    (by decide : 407273517 ≤ 407306285) block0 block1

theorem join_0_1 : (twinPrimeSegment 407306285 407371821).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 407306285 ≤ 407339053)
    (by decide : 407339053 ≤ 407371821) block2 block3

theorem join_1_0 : (twinPrimeSegment 407240749 407371821).card = 395 := by
  simpa using combineTwinPrimeSegments (by decide : 407240749 ≤ 407306285)
    (by decide : 407306285 ≤ 407371821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 407240749 407371821).card = 395 := join_1_0

end S194C03
end Sude.GeneratedTwinScan
