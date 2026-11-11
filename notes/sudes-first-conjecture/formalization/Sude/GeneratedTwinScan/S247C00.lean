import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22760)) 517996589 518029357 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 517996589 518029357).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22760 517996589 518029357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22760)) 518029357 518062125 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 518029357 518062125).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22760 518029357 518062125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22761)) 518062125 518094893 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 518062125 518094893).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22761 518062125 518094893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22762)) 518094893 518127661 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 518094893 518127661).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22762 518094893 518127661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 517996589 518062125).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 517996589 ≤ 518029357)
    (by decide : 518029357 ≤ 518062125) block0 block1

theorem join_0_1 : (twinPrimeSegment 518062125 518127661).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 518062125 ≤ 518094893)
    (by decide : 518094893 ≤ 518127661) block2 block3

theorem join_1_0 : (twinPrimeSegment 517996589 518127661).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 517996589 ≤ 518062125)
    (by decide : 518062125 ≤ 518127661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 517996589 518127661).card = 422 := join_1_0

end S247C00
end Sude.GeneratedTwinScan
