import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20930)) 438042669 438075437 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438042669 438075437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20930 438042669 438075437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20931)) 438075437 438108205 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438075437 438108205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20931 438075437 438108205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20931)) 438108205 438140973 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438108205 438140973).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20931 438108205 438140973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20932)) 438140973 438173741 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438140973 438173741).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20932 438140973 438173741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438042669 438108205).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 438042669 ≤ 438075437)
    (by decide : 438075437 ≤ 438108205) block0 block1

theorem join_0_1 : (twinPrimeSegment 438108205 438173741).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 438108205 ≤ 438140973)
    (by decide : 438140973 ≤ 438173741) block2 block3

theorem join_1_0 : (twinPrimeSegment 438042669 438173741).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 438042669 ≤ 438108205)
    (by decide : 438108205 ≤ 438173741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438042669 438173741).card = 441 := join_1_0

end S208C14
end Sude.GeneratedTwinScan
