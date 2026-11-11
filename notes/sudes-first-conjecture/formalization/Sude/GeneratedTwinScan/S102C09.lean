import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14667)) 215089197 215121965 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 215089197 215121965).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14667 215089197 215121965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14668)) 215121965 215154733 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 215121965 215154733).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14668 215121965 215154733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14669)) 215154733 215187501 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215154733 215187501).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14669 215154733 215187501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14670)) 215187501 215220269 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215187501 215220269).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14670 215187501 215220269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 215089197 215154733).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 215089197 ≤ 215121965)
    (by decide : 215121965 ≤ 215154733) block0 block1

theorem join_0_1 : (twinPrimeSegment 215154733 215220269).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 215154733 ≤ 215187501)
    (by decide : 215187501 ≤ 215220269) block2 block3

theorem join_1_0 : (twinPrimeSegment 215089197 215220269).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 215089197 ≤ 215154733)
    (by decide : 215154733 ≤ 215220269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 215089197 215220269).card = 443 := join_1_0

end S102C09
end Sude.GeneratedTwinScan
