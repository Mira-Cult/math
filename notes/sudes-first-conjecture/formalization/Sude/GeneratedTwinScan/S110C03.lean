import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15202)) 231079981 231112749 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231079981 231112749).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15202 231079981 231112749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15203)) 231112749 231145517 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231112749 231145517).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15203 231112749 231145517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15204)) 231145517 231178285 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231145517 231178285).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15204 231145517 231178285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15205)) 231178285 231211053 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231178285 231211053).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15205 231178285 231211053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231079981 231145517).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 231079981 ≤ 231112749)
    (by decide : 231112749 ≤ 231145517) block0 block1

theorem join_0_1 : (twinPrimeSegment 231145517 231211053).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 231145517 ≤ 231178285)
    (by decide : 231178285 ≤ 231211053) block2 block3

theorem join_1_0 : (twinPrimeSegment 231079981 231211053).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 231079981 ≤ 231145517)
    (by decide : 231145517 ≤ 231211053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231079981 231211053).card = 438 := join_1_0

end S110C03
end Sude.GeneratedTwinScan
