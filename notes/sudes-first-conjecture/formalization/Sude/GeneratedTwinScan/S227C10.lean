import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21849)) 477364269 477397037 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 477364269 477397037).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21849 477364269 477397037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21850)) 477397037 477429805 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477397037 477429805).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21850 477397037 477429805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21850)) 477429805 477462573 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477429805 477462573).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21850 477429805 477462573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21851)) 477462573 477495341 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477462573 477495341).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21851 477462573 477495341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 477364269 477429805).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 477364269 ≤ 477397037)
    (by decide : 477397037 ≤ 477429805) block0 block1

theorem join_0_1 : (twinPrimeSegment 477429805 477495341).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 477429805 ≤ 477462573)
    (by decide : 477462573 ≤ 477495341) block2 block3

theorem join_1_0 : (twinPrimeSegment 477364269 477495341).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 477364269 ≤ 477429805)
    (by decide : 477429805 ≤ 477495341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 477364269 477495341).card = 473 := join_1_0

end S227C10
end Sude.GeneratedTwinScan
