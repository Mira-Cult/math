import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13079)) 171049005 171081773 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171049005 171081773).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13079 171049005 171081773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13081)) 171081773 171114541 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171081773 171114541).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13081 171081773 171114541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13082)) 171114541 171147309 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 171114541 171147309).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13082 171114541 171147309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13083)) 171147309 171180077 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171147309 171180077).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13083 171147309 171180077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171049005 171114541).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 171049005 ≤ 171081773)
    (by decide : 171081773 ≤ 171114541) block0 block1

theorem join_0_1 : (twinPrimeSegment 171114541 171180077).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 171114541 ≤ 171147309)
    (by decide : 171147309 ≤ 171180077) block2 block3

theorem join_1_0 : (twinPrimeSegment 171049005 171180077).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 171049005 ≤ 171114541)
    (by decide : 171114541 ≤ 171180077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171049005 171180077).card = 482 := join_1_0

end S081C09
end Sude.GeneratedTwinScan
