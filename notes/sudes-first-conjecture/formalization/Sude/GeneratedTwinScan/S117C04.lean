import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15681)) 245891117 245923885 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 245891117 245923885).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15681 245891117 245923885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15683)) 245923885 245956653 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245923885 245956653).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15683 245923885 245956653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15684)) 245956653 245989421 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245956653 245989421).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15684 245956653 245989421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15685)) 245989421 246022189 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245989421 246022189).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15685 245989421 246022189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 245891117 245956653).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 245891117 ≤ 245923885)
    (by decide : 245923885 ≤ 245956653) block0 block1

theorem join_0_1 : (twinPrimeSegment 245956653 246022189).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 245956653 ≤ 245989421)
    (by decide : 245989421 ≤ 246022189) block2 block3

theorem join_1_0 : (twinPrimeSegment 245891117 246022189).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 245891117 ≤ 245956653)
    (by decide : 245956653 ≤ 246022189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 245891117 246022189).card = 466 := join_1_0

end S117C04
end Sude.GeneratedTwinScan
