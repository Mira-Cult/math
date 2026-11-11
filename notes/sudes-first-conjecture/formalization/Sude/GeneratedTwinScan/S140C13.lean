import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17185)) 295305261 295338029 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295305261 295338029).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17185 295305261 295338029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17186)) 295338029 295370797 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295338029 295370797).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17186 295338029 295370797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17187)) 295370797 295403565 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 295370797 295403565).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17187 295370797 295403565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17188)) 295403565 295436333 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295403565 295436333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17188 295403565 295436333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295305261 295370797).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 295305261 ≤ 295338029)
    (by decide : 295338029 ≤ 295370797) block0 block1

theorem join_0_1 : (twinPrimeSegment 295370797 295436333).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 295370797 ≤ 295403565)
    (by decide : 295403565 ≤ 295436333) block2 block3

theorem join_1_0 : (twinPrimeSegment 295305261 295436333).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 295305261 ≤ 295370797)
    (by decide : 295370797 ≤ 295436333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295305261 295436333).card = 476 := join_1_0

end S140C13
end Sude.GeneratedTwinScan
