import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16615)) 276037677 276070445 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276037677 276070445).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16615 276037677 276070445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16616)) 276070445 276103213 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276070445 276103213).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16616 276070445 276103213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16617)) 276103213 276135981 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 276103213 276135981).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16617 276103213 276135981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16618)) 276135981 276168749 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276135981 276168749).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16618 276135981 276168749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276037677 276103213).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 276037677 ≤ 276070445)
    (by decide : 276070445 ≤ 276103213) block0 block1

theorem join_0_1 : (twinPrimeSegment 276103213 276168749).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 276103213 ≤ 276135981)
    (by decide : 276135981 ≤ 276168749) block2 block3

theorem join_1_0 : (twinPrimeSegment 276037677 276168749).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 276037677 ≤ 276103213)
    (by decide : 276103213 ≤ 276168749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276037677 276168749).card = 461 := join_1_0

end S131C10
end Sude.GeneratedTwinScan
