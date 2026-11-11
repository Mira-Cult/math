import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17367)) 301596717 301629485 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301596717 301629485).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17367 301596717 301629485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17368)) 301629485 301662253 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 301629485 301662253).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17368 301629485 301662253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17369)) 301662253 301695021 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301662253 301695021).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17369 301662253 301695021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17370)) 301695021 301727789 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301695021 301727789).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17370 301695021 301727789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301596717 301662253).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 301596717 ≤ 301629485)
    (by decide : 301629485 ≤ 301662253) block0 block1

theorem join_0_1 : (twinPrimeSegment 301662253 301727789).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 301662253 ≤ 301695021)
    (by decide : 301695021 ≤ 301727789) block2 block3

theorem join_1_0 : (twinPrimeSegment 301596717 301727789).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 301596717 ≤ 301662253)
    (by decide : 301662253 ≤ 301727789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301596717 301727789).card = 434 := join_1_0

end S143C13
end Sude.GeneratedTwinScan
