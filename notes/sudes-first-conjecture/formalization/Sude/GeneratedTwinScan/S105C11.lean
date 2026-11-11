import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14888)) 221642797 221675565 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221642797 221675565).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14888 221642797 221675565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14889)) 221675565 221708333 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221675565 221708333).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14889 221675565 221708333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14890)) 221708333 221741101 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221708333 221741101).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14890 221708333 221741101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14892)) 221741101 221773869 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221741101 221773869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14892 221741101 221773869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221642797 221708333).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 221642797 ≤ 221675565)
    (by decide : 221675565 ≤ 221708333) block0 block1

theorem join_0_1 : (twinPrimeSegment 221708333 221773869).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 221708333 ≤ 221741101)
    (by decide : 221741101 ≤ 221773869) block2 block3

theorem join_1_0 : (twinPrimeSegment 221642797 221773869).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 221642797 ≤ 221708333)
    (by decide : 221708333 ≤ 221773869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221642797 221773869).card = 491 := join_1_0

end S105C11
end Sude.GeneratedTwinScan
