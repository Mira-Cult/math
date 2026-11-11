import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14635)) 214171693 214204461 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214171693 214204461).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14635 214171693 214204461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14636)) 214204461 214237229 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214204461 214237229).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14636 214204461 214237229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14637)) 214237229 214269997 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 214237229 214269997).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14637 214237229 214269997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14639)) 214269997 214302765 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214269997 214302765).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14639 214269997 214302765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214171693 214237229).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 214171693 ≤ 214204461)
    (by decide : 214204461 ≤ 214237229) block0 block1

theorem join_0_1 : (twinPrimeSegment 214237229 214302765).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 214237229 ≤ 214269997)
    (by decide : 214269997 ≤ 214302765) block2 block3

theorem join_1_0 : (twinPrimeSegment 214171693 214302765).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 214171693 ≤ 214237229)
    (by decide : 214237229 ≤ 214302765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214171693 214302765).card = 456 := join_1_0

end S102C02
end Sude.GeneratedTwinScan
