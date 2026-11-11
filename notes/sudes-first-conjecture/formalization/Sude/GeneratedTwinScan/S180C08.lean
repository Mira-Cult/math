import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19456)) 378535981 378568749 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 378535981 378568749).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19456 378535981 378568749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19457)) 378568749 378601517 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 378568749 378601517).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19457 378568749 378601517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19458)) 378601517 378634285 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 378601517 378634285).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19458 378601517 378634285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19459)) 378634285 378667053 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 378634285 378667053).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19459 378634285 378667053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 378535981 378601517).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 378535981 ≤ 378568749)
    (by decide : 378568749 ≤ 378601517) block0 block1

theorem join_0_1 : (twinPrimeSegment 378601517 378667053).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 378601517 ≤ 378634285)
    (by decide : 378634285 ≤ 378667053) block2 block3

theorem join_1_0 : (twinPrimeSegment 378535981 378667053).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 378535981 ≤ 378601517)
    (by decide : 378601517 ≤ 378667053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 378535981 378667053).card = 425 := join_1_0

end S180C08
end Sude.GeneratedTwinScan
