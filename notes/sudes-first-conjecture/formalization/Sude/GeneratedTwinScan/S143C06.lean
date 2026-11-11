import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17341)) 300679213 300711981 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300679213 300711981).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17341 300679213 300711981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17341)) 300711981 300744749 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300711981 300744749).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17341 300711981 300744749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17342)) 300744749 300777517 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300744749 300777517).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17342 300744749 300777517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17343)) 300777517 300810285 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300777517 300810285).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17343 300777517 300810285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300679213 300744749).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 300679213 ≤ 300711981)
    (by decide : 300711981 ≤ 300744749) block0 block1

theorem join_0_1 : (twinPrimeSegment 300744749 300810285).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 300744749 ≤ 300777517)
    (by decide : 300777517 ≤ 300810285) block2 block3

theorem join_1_0 : (twinPrimeSegment 300679213 300810285).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 300679213 ≤ 300744749)
    (by decide : 300744749 ≤ 300810285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300679213 300810285).card = 474 := join_1_0

end S143C06
end Sude.GeneratedTwinScan
