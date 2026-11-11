import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15159)) 229769261 229802029 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229769261 229802029).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15159 229769261 229802029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15160)) 229802029 229834797 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229802029 229834797).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15160 229802029 229834797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15161)) 229834797 229867565 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229834797 229867565).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15161 229834797 229867565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15162)) 229867565 229900333 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229867565 229900333).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15162 229867565 229900333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229769261 229834797).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 229769261 ≤ 229802029)
    (by decide : 229802029 ≤ 229834797) block0 block1

theorem join_0_1 : (twinPrimeSegment 229834797 229900333).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 229834797 ≤ 229867565)
    (by decide : 229867565 ≤ 229900333) block2 block3

theorem join_1_0 : (twinPrimeSegment 229769261 229900333).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 229769261 ≤ 229834797)
    (by decide : 229834797 ≤ 229900333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229769261 229900333).card = 454 := join_1_0

end S109C09
end Sude.GeneratedTwinScan
