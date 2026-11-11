import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13528)) 182976557 183009325 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182976557 183009325).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13528 182976557 183009325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13529)) 183009325 183042093 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183009325 183042093).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13529 183009325 183042093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13530)) 183042093 183074861 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183042093 183074861).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13530 183042093 183074861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13531)) 183074861 183107629 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183074861 183107629).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13531 183074861 183107629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182976557 183042093).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 182976557 ≤ 183009325)
    (by decide : 183009325 ≤ 183042093) block0 block1

theorem join_0_1 : (twinPrimeSegment 183042093 183107629).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 183042093 ≤ 183074861)
    (by decide : 183074861 ≤ 183107629) block2 block3

theorem join_1_0 : (twinPrimeSegment 182976557 183107629).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 182976557 ≤ 183042093)
    (by decide : 183042093 ≤ 183107629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182976557 183107629).card = 478 := join_1_0

end S087C04
end Sude.GeneratedTwinScan
