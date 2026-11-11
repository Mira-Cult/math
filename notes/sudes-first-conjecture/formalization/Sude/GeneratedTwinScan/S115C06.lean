import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15556)) 241958957 241991725 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241958957 241991725).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15556 241958957 241991725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15557)) 241991725 242024493 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241991725 242024493).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15557 241991725 242024493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15558)) 242024493 242057261 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242024493 242057261).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15558 242024493 242057261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15559)) 242057261 242090029 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242057261 242090029).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15559 242057261 242090029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241958957 242024493).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 241958957 ≤ 241991725)
    (by decide : 241991725 ≤ 242024493) block0 block1

theorem join_0_1 : (twinPrimeSegment 242024493 242090029).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 242024493 ≤ 242057261)
    (by decide : 242057261 ≤ 242090029) block2 block3

theorem join_1_0 : (twinPrimeSegment 241958957 242090029).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 241958957 ≤ 242024493)
    (by decide : 242024493 ≤ 242090029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241958957 242090029).card = 482 := join_1_0

end S115C06
end Sude.GeneratedTwinScan
