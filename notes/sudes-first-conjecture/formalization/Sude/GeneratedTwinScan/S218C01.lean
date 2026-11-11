import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21385)) 457310253 457343021 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457310253 457343021).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21385 457310253 457343021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21386)) 457343021 457375789 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457343021 457375789).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21386 457343021 457375789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21387)) 457375789 457408557 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457375789 457408557).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21387 457375789 457408557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21387)) 457408557 457441325 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457408557 457441325).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21387 457408557 457441325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457310253 457375789).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 457310253 ≤ 457343021)
    (by decide : 457343021 ≤ 457375789) block0 block1

theorem join_0_1 : (twinPrimeSegment 457375789 457441325).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 457375789 ≤ 457408557)
    (by decide : 457408557 ≤ 457441325) block2 block3

theorem join_1_0 : (twinPrimeSegment 457310253 457441325).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 457310253 ≤ 457375789)
    (by decide : 457375789 ≤ 457441325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457310253 457441325).card = 417 := join_1_0

end S218C01
end Sude.GeneratedTwinScan
