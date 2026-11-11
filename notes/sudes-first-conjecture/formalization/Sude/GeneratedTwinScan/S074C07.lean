import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12495)) 156106797 156139565 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 156106797 156139565).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12495 156106797 156139565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12496)) 156139565 156172333 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 156139565 156172333).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12496 156139565 156172333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12498)) 156172333 156205101 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 156172333 156205101).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12498 156172333 156205101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12499)) 156205101 156237869 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 156205101 156237869).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12499 156205101 156237869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 156106797 156172333).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 156106797 ≤ 156139565)
    (by decide : 156139565 ≤ 156172333) block0 block1

theorem join_0_1 : (twinPrimeSegment 156172333 156237869).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 156172333 ≤ 156205101)
    (by decide : 156205101 ≤ 156237869) block2 block3

theorem join_1_0 : (twinPrimeSegment 156106797 156237869).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 156106797 ≤ 156172333)
    (by decide : 156172333 ≤ 156237869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 156106797 156237869).card = 496 := join_1_0

end S074C07
end Sude.GeneratedTwinScan
