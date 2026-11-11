import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20605)) 424542253 424575021 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424542253 424575021).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20605 424542253 424575021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20606)) 424575021 424607789 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424575021 424607789).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20606 424575021 424607789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20606)) 424607789 424640557 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 424607789 424640557).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20606 424607789 424640557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20607)) 424640557 424673325 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 424640557 424673325).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20607 424640557 424673325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424542253 424607789).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 424542253 ≤ 424575021)
    (by decide : 424575021 ≤ 424607789) block0 block1

theorem join_0_1 : (twinPrimeSegment 424607789 424673325).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 424607789 ≤ 424640557)
    (by decide : 424640557 ≤ 424673325) block2 block3

theorem join_1_0 : (twinPrimeSegment 424542253 424673325).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 424542253 ≤ 424607789)
    (by decide : 424607789 ≤ 424673325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424542253 424673325).card = 439 := join_1_0

end S202C07
end Sude.GeneratedTwinScan
