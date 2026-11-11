import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19972)) 398852141 398884909 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 398852141 398884909).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19972 398852141 398884909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19972)) 398884909 398917677 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 398884909 398917677).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19972 398884909 398917677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19973)) 398917677 398950445 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 398917677 398950445).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19973 398917677 398950445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19974)) 398950445 398983213 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 398950445 398983213).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19974 398950445 398983213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 398852141 398917677).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 398852141 ≤ 398884909)
    (by decide : 398884909 ≤ 398917677) block0 block1

theorem join_0_1 : (twinPrimeSegment 398917677 398983213).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 398917677 ≤ 398950445)
    (by decide : 398950445 ≤ 398983213) block2 block3

theorem join_1_0 : (twinPrimeSegment 398852141 398983213).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 398852141 ≤ 398917677)
    (by decide : 398917677 ≤ 398983213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 398852141 398983213).card = 440 := join_1_0

end S190C03
end Sude.GeneratedTwinScan
