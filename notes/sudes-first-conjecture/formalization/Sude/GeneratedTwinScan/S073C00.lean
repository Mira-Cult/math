import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12374)) 153092141 153124909 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153092141 153124909).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12374 153092141 153124909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12375)) 153124909 153157677 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153124909 153157677).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12375 153124909 153157677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12377)) 153157677 153190445 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153157677 153190445).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12377 153157677 153190445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12378)) 153190445 153223213 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153190445 153223213).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12378 153190445 153223213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153092141 153157677).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 153092141 ≤ 153124909)
    (by decide : 153124909 ≤ 153157677) block0 block1

theorem join_0_1 : (twinPrimeSegment 153157677 153223213).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 153157677 ≤ 153190445)
    (by decide : 153190445 ≤ 153223213) block2 block3

theorem join_1_0 : (twinPrimeSegment 153092141 153223213).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 153092141 ≤ 153157677)
    (by decide : 153157677 ≤ 153223213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153092141 153223213).card = 513 := join_1_0

end S073C00
end Sude.GeneratedTwinScan
