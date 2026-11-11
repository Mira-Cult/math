import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20252)) 410124333 410157101 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 410124333 410157101).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20252 410124333 410157101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20253)) 410157101 410189869 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410157101 410189869).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20253 410157101 410189869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20253)) 410189869 410222637 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410189869 410222637).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20253 410189869 410222637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20254)) 410222637 410255405 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 410222637 410255405).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20254 410222637 410255405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 410124333 410189869).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 410124333 ≤ 410157101)
    (by decide : 410157101 ≤ 410189869) block0 block1

theorem join_0_1 : (twinPrimeSegment 410189869 410255405).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 410189869 ≤ 410222637)
    (by decide : 410222637 ≤ 410255405) block2 block3

theorem join_1_0 : (twinPrimeSegment 410124333 410255405).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 410124333 ≤ 410189869)
    (by decide : 410189869 ≤ 410255405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 410124333 410255405).card = 453 := join_1_0

end S195C09
end Sude.GeneratedTwinScan
