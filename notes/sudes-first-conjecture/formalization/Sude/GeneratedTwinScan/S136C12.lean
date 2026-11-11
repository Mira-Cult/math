import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16935)) 286785581 286818349 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286785581 286818349).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16935 286785581 286818349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16936)) 286818349 286851117 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286818349 286851117).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16936 286818349 286851117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16937)) 286851117 286883885 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286851117 286883885).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16937 286851117 286883885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16938)) 286883885 286916653 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286883885 286916653).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16938 286883885 286916653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286785581 286851117).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 286785581 ≤ 286818349)
    (by decide : 286818349 ≤ 286851117) block0 block1

theorem join_0_1 : (twinPrimeSegment 286851117 286916653).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 286851117 ≤ 286883885)
    (by decide : 286883885 ≤ 286916653) block2 block3

theorem join_1_0 : (twinPrimeSegment 286785581 286916653).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 286785581 ≤ 286851117)
    (by decide : 286851117 ≤ 286916653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286785581 286916653).card = 432 := join_1_0

end S136C12
end Sude.GeneratedTwinScan
