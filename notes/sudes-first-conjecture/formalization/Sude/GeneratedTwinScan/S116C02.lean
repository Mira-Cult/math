import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15606)) 243531821 243564589 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243531821 243564589).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15606 243531821 243564589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15607)) 243564589 243597357 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243564589 243597357).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15607 243564589 243597357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15608)) 243597357 243630125 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243597357 243630125).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15608 243597357 243630125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15609)) 243630125 243662893 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 243630125 243662893).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15609 243630125 243662893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243531821 243597357).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 243531821 ≤ 243564589)
    (by decide : 243564589 ≤ 243597357) block0 block1

theorem join_0_1 : (twinPrimeSegment 243597357 243662893).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 243597357 ≤ 243630125)
    (by decide : 243630125 ≤ 243662893) block2 block3

theorem join_1_0 : (twinPrimeSegment 243531821 243662893).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 243531821 ≤ 243597357)
    (by decide : 243597357 ≤ 243662893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243531821 243662893).card = 476 := join_1_0

end S116C02
end Sude.GeneratedTwinScan
