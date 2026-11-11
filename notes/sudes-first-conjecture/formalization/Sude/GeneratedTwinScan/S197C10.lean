import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20358)) 414449709 414482477 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414449709 414482477).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20358 414449709 414482477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20359)) 414482477 414515245 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 414482477 414515245).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20359 414482477 414515245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20360)) 414515245 414548013 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 414515245 414548013).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20360 414515245 414548013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20361)) 414548013 414580781 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 414548013 414580781).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20361 414548013 414580781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414449709 414515245).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 414449709 ≤ 414482477)
    (by decide : 414482477 ≤ 414515245) block0 block1

theorem join_0_1 : (twinPrimeSegment 414515245 414580781).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 414515245 ≤ 414548013)
    (by decide : 414548013 ≤ 414580781) block2 block3

theorem join_1_0 : (twinPrimeSegment 414449709 414580781).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 414449709 ≤ 414515245)
    (by decide : 414515245 ≤ 414580781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414449709 414580781).card = 453 := join_1_0

end S197C10
end Sude.GeneratedTwinScan
