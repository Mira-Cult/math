import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19308)) 372768813 372801581 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372768813 372801581).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19308 372768813 372801581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19308)) 372801581 372834349 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372801581 372834349).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19308 372801581 372834349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19309)) 372834349 372867117 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372834349 372867117).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19309 372834349 372867117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19310)) 372867117 372899885 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372867117 372899885).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19310 372867117 372899885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372768813 372834349).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 372768813 ≤ 372801581)
    (by decide : 372801581 ≤ 372834349) block0 block1

theorem join_0_1 : (twinPrimeSegment 372834349 372899885).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 372834349 ≤ 372867117)
    (by decide : 372867117 ≤ 372899885) block2 block3

theorem join_1_0 : (twinPrimeSegment 372768813 372899885).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 372768813 ≤ 372834349)
    (by decide : 372834349 ≤ 372899885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372768813 372899885).card = 463 := join_1_0

end S177C12
end Sude.GeneratedTwinScan
