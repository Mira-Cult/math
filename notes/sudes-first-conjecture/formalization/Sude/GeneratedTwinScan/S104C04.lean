import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14787)) 218628141 218660909 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 218628141 218660909).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14787 218628141 218660909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14788)) 218660909 218693677 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218660909 218693677).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14788 218660909 218693677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14789)) 218693677 218726445 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218693677 218726445).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14789 218693677 218726445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14790)) 218726445 218759213 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218726445 218759213).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14790 218726445 218759213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 218628141 218693677).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 218628141 ≤ 218660909)
    (by decide : 218660909 ≤ 218693677) block0 block1

theorem join_0_1 : (twinPrimeSegment 218693677 218759213).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 218693677 ≤ 218726445)
    (by decide : 218726445 ≤ 218759213) block2 block3

theorem join_1_0 : (twinPrimeSegment 218628141 218759213).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 218628141 ≤ 218693677)
    (by decide : 218693677 ≤ 218759213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 218628141 218759213).card = 461 := join_1_0

end S104C04
end Sude.GeneratedTwinScan
