import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19711)) 388497453 388530221 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 388497453 388530221).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19711 388497453 388530221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19712)) 388530221 388562989 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388530221 388562989).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19712 388530221 388562989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19712)) 388562989 388595757 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388562989 388595757).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19712 388562989 388595757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19713)) 388595757 388628525 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388595757 388628525).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19713 388595757 388628525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 388497453 388562989).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 388497453 ≤ 388530221)
    (by decide : 388530221 ≤ 388562989) block0 block1

theorem join_0_1 : (twinPrimeSegment 388562989 388628525).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 388562989 ≤ 388595757)
    (by decide : 388595757 ≤ 388628525) block2 block3

theorem join_1_0 : (twinPrimeSegment 388497453 388628525).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 388497453 ≤ 388562989)
    (by decide : 388562989 ≤ 388628525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 388497453 388628525).card = 427 := join_1_0

end S185C04
end Sude.GeneratedTwinScan
