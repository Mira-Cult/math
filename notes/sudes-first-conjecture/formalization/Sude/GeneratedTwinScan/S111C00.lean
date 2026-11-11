import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15258)) 232783917 232816685 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 232783917 232816685).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15258 232783917 232816685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15259)) 232816685 232849453 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232816685 232849453).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15259 232816685 232849453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15260)) 232849453 232882221 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232849453 232882221).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15260 232849453 232882221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15261)) 232882221 232914989 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232882221 232914989).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15261 232882221 232914989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 232783917 232849453).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 232783917 ≤ 232816685)
    (by decide : 232816685 ≤ 232849453) block0 block1

theorem join_0_1 : (twinPrimeSegment 232849453 232914989).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 232849453 ≤ 232882221)
    (by decide : 232882221 ≤ 232914989) block2 block3

theorem join_1_0 : (twinPrimeSegment 232783917 232914989).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 232783917 ≤ 232849453)
    (by decide : 232849453 ≤ 232914989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 232783917 232914989).card = 462 := join_1_0

end S111C00
end Sude.GeneratedTwinScan
