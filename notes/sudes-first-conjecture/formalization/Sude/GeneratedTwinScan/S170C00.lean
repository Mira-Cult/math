import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18882)) 356515885 356548653 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 356515885 356548653).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18882 356515885 356548653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18883)) 356548653 356581421 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356548653 356581421).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18883 356548653 356581421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18884)) 356581421 356614189 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356581421 356614189).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18884 356581421 356614189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18885)) 356614189 356646957 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 356614189 356646957).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18885 356614189 356646957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 356515885 356581421).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 356548653)
    (by decide : 356548653 ≤ 356581421) block0 block1

theorem join_0_1 : (twinPrimeSegment 356581421 356646957).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 356581421 ≤ 356614189)
    (by decide : 356614189 ≤ 356646957) block2 block3

theorem join_1_0 : (twinPrimeSegment 356515885 356646957).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 356581421)
    (by decide : 356581421 ≤ 356646957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 356515885 356646957).card = 434 := join_1_0

end S170C00
end Sude.GeneratedTwinScan
