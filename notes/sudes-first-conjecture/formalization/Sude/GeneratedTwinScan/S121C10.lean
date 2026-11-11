import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15971)) 255066157 255098925 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255066157 255098925).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15971 255066157 255098925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15972)) 255098925 255131693 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 255098925 255131693).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15972 255098925 255131693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15973)) 255131693 255164461 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255131693 255164461).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15973 255131693 255164461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15974)) 255164461 255197229 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255164461 255197229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15974 255164461 255197229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255066157 255131693).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 255066157 ≤ 255098925)
    (by decide : 255098925 ≤ 255131693) block0 block1

theorem join_0_1 : (twinPrimeSegment 255131693 255197229).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 255131693 ≤ 255164461)
    (by decide : 255164461 ≤ 255197229) block2 block3

theorem join_1_0 : (twinPrimeSegment 255066157 255197229).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 255066157 ≤ 255131693)
    (by decide : 255131693 ≤ 255197229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255066157 255197229).card = 442 := join_1_0

end S121C10
end Sude.GeneratedTwinScan
