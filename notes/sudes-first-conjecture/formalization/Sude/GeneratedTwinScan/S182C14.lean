import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19584)) 383516717 383549485 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383516717 383549485).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19584 383516717 383549485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19585)) 383549485 383582253 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383549485 383582253).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19585 383549485 383582253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19586)) 383582253 383615021 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383582253 383615021).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19586 383582253 383615021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19586)) 383615021 383647789 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383615021 383647789).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19586 383615021 383647789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383516717 383582253).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 383516717 ≤ 383549485)
    (by decide : 383549485 ≤ 383582253) block0 block1

theorem join_0_1 : (twinPrimeSegment 383582253 383647789).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 383582253 ≤ 383615021)
    (by decide : 383615021 ≤ 383647789) block2 block3

theorem join_1_0 : (twinPrimeSegment 383516717 383647789).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 383516717 ≤ 383582253)
    (by decide : 383582253 ≤ 383647789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383516717 383647789).card = 436 := join_1_0

end S182C14
end Sude.GeneratedTwinScan
