import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21382)) 457179181 457211949 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457179181 457211949).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21382 457179181 457211949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21383)) 457211949 457244717 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457211949 457244717).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21383 457211949 457244717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21384)) 457244717 457277485 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457244717 457277485).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21384 457244717 457277485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21384)) 457277485 457310253 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457277485 457310253).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21384 457277485 457310253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457179181 457244717).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 457211949)
    (by decide : 457211949 ≤ 457244717) block0 block1

theorem join_0_1 : (twinPrimeSegment 457244717 457310253).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 457244717 ≤ 457277485)
    (by decide : 457277485 ≤ 457310253) block2 block3

theorem join_1_0 : (twinPrimeSegment 457179181 457310253).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 457244717)
    (by decide : 457244717 ≤ 457310253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457179181 457310253).card = 462 := join_1_0

end S218C00
end Sude.GeneratedTwinScan
