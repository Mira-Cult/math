import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17212)) 296222765 296255533 = 86 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296222765 296255533).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17212 296222765 296255533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17213)) 296255533 296288301 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296255533 296288301).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17213 296255533 296288301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17213)) 296288301 296321069 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296288301 296321069).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17213 296288301 296321069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17214)) 296321069 296353837 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296321069 296353837).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17214 296321069 296353837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296222765 296288301).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 296222765 ≤ 296255533)
    (by decide : 296255533 ≤ 296288301) block0 block1

theorem join_0_1 : (twinPrimeSegment 296288301 296353837).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 296288301 ≤ 296321069)
    (by decide : 296321069 ≤ 296353837) block2 block3

theorem join_1_0 : (twinPrimeSegment 296222765 296353837).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 296222765 ≤ 296288301)
    (by decide : 296288301 ≤ 296353837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296222765 296353837).card = 412 := join_1_0

end S141C04
end Sude.GeneratedTwinScan
