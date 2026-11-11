import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22209)) 493223981 493256749 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493223981 493256749).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22209 493223981 493256749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22210)) 493256749 493289517 = 88 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493256749 493289517).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22210 493256749 493289517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22210)) 493289517 493322285 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493289517 493322285).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22210 493289517 493322285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22211)) 493322285 493355053 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493322285 493355053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22211 493322285 493355053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493223981 493289517).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 493223981 ≤ 493256749)
    (by decide : 493256749 ≤ 493289517) block0 block1

theorem join_0_1 : (twinPrimeSegment 493289517 493355053).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 493289517 ≤ 493322285)
    (by decide : 493322285 ≤ 493355053) block2 block3

theorem join_1_0 : (twinPrimeSegment 493223981 493355053).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 493223981 ≤ 493289517)
    (by decide : 493289517 ≤ 493355053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493223981 493355053).card = 426 := join_1_0

end S235C03
end Sude.GeneratedTwinScan
