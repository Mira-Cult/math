import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21042)) 442761261 442794029 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 442761261 442794029).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21042 442761261 442794029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21043)) 442794029 442826797 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442794029 442826797).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21043 442794029 442826797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21044)) 442826797 442859565 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442826797 442859565).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21044 442826797 442859565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21045)) 442859565 442892333 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442859565 442892333).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21045 442859565 442892333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 442761261 442826797).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 442761261 ≤ 442794029)
    (by decide : 442794029 ≤ 442826797) block0 block1

theorem join_0_1 : (twinPrimeSegment 442826797 442892333).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 442826797 ≤ 442859565)
    (by decide : 442859565 ≤ 442892333) block2 block3

theorem join_1_0 : (twinPrimeSegment 442761261 442892333).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 442761261 ≤ 442826797)
    (by decide : 442826797 ≤ 442892333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 442761261 442892333).card = 447 := join_1_0

end S211C02
end Sude.GeneratedTwinScan
