import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13881)) 192675885 192708653 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192675885 192708653).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13881 192675885 192708653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13883)) 192708653 192741421 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192708653 192741421).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13883 192708653 192741421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13884)) 192741421 192774189 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 192741421 192774189).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13884 192741421 192774189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13885)) 192774189 192806957 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 192774189 192806957).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13885 192774189 192806957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192675885 192741421).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 192675885 ≤ 192708653)
    (by decide : 192708653 ≤ 192741421) block0 block1

theorem join_0_1 : (twinPrimeSegment 192741421 192806957).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 192741421 ≤ 192774189)
    (by decide : 192774189 ≤ 192806957) block2 block3

theorem join_1_0 : (twinPrimeSegment 192675885 192806957).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 192675885 ≤ 192741421)
    (by decide : 192741421 ≤ 192806957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192675885 192806957).card = 487 := join_1_0

end S091C14
end Sude.GeneratedTwinScan
