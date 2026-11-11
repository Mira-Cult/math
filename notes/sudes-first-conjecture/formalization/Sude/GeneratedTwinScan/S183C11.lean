import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19627)) 385220653 385253421 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385220653 385253421).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19627 385220653 385253421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19628)) 385253421 385286189 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385253421 385286189).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19628 385253421 385286189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19629)) 385286189 385318957 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385286189 385318957).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19629 385286189 385318957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19630)) 385318957 385351725 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385318957 385351725).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19630 385318957 385351725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385220653 385286189).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 385220653 ≤ 385253421)
    (by decide : 385253421 ≤ 385286189) block0 block1

theorem join_0_1 : (twinPrimeSegment 385286189 385351725).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 385286189 ≤ 385318957)
    (by decide : 385318957 ≤ 385351725) block2 block3

theorem join_1_0 : (twinPrimeSegment 385220653 385351725).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 385220653 ≤ 385286189)
    (by decide : 385286189 ≤ 385351725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385220653 385351725).card = 460 := join_1_0

end S183C11
end Sude.GeneratedTwinScan
