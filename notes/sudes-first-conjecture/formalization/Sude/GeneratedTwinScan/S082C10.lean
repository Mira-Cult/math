import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13164)) 173277229 173309997 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173277229 173309997).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13164 173277229 173309997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13165)) 173309997 173342765 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173309997 173342765).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13165 173309997 173342765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13167)) 173342765 173375533 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173342765 173375533).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13167 173342765 173375533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13168)) 173375533 173408301 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 173375533 173408301).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13168 173375533 173408301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173277229 173342765).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 173277229 ≤ 173309997)
    (by decide : 173309997 ≤ 173342765) block0 block1

theorem join_0_1 : (twinPrimeSegment 173342765 173408301).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 173342765 ≤ 173375533)
    (by decide : 173375533 ≤ 173408301) block2 block3

theorem join_1_0 : (twinPrimeSegment 173277229 173408301).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 173277229 ≤ 173342765)
    (by decide : 173342765 ≤ 173408301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173277229 173408301).card = 493 := join_1_0

end S082C10
end Sude.GeneratedTwinScan
