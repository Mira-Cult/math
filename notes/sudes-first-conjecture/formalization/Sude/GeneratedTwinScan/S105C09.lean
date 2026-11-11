import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14879)) 221380653 221413421 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221380653 221413421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14879 221380653 221413421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14881)) 221413421 221446189 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221413421 221446189).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14881 221413421 221446189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14882)) 221446189 221478957 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221446189 221478957).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14882 221446189 221478957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14883)) 221478957 221511725 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221478957 221511725).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14883 221478957 221511725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221380653 221446189).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 221380653 ≤ 221413421)
    (by decide : 221413421 ≤ 221446189) block0 block1

theorem join_0_1 : (twinPrimeSegment 221446189 221511725).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 221446189 ≤ 221478957)
    (by decide : 221478957 ≤ 221511725) block2 block3

theorem join_1_0 : (twinPrimeSegment 221380653 221511725).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 221380653 ≤ 221446189)
    (by decide : 221446189 ≤ 221511725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221380653 221511725).card = 485 := join_1_0

end S105C09
end Sude.GeneratedTwinScan
