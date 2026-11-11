import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15677)) 245760045 245792813 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 245760045 245792813).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15677 245760045 245792813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15678)) 245792813 245825581 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245792813 245825581).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15678 245792813 245825581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15679)) 245825581 245858349 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245825581 245858349).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15679 245825581 245858349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15680)) 245858349 245891117 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245858349 245891117).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15680 245858349 245891117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 245760045 245825581).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 245760045 ≤ 245792813)
    (by decide : 245792813 ≤ 245825581) block0 block1

theorem join_0_1 : (twinPrimeSegment 245825581 245891117).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 245825581 ≤ 245858349)
    (by decide : 245858349 ≤ 245891117) block2 block3

theorem join_1_0 : (twinPrimeSegment 245760045 245891117).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 245760045 ≤ 245825581)
    (by decide : 245825581 ≤ 245891117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 245760045 245891117).card = 460 := join_1_0

end S117C03
end Sude.GeneratedTwinScan
