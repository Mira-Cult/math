import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13639)) 185991213 186023981 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185991213 186023981).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13639 185991213 186023981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13640)) 186023981 186056749 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186023981 186056749).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13640 186023981 186056749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13641)) 186056749 186089517 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186056749 186089517).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13641 186056749 186089517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13642)) 186089517 186122285 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 186089517 186122285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13642 186089517 186122285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185991213 186056749).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 185991213 ≤ 186023981)
    (by decide : 186023981 ≤ 186056749) block0 block1

theorem join_0_1 : (twinPrimeSegment 186056749 186122285).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 186056749 ≤ 186089517)
    (by decide : 186089517 ≤ 186122285) block2 block3

theorem join_1_0 : (twinPrimeSegment 185991213 186122285).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 185991213 ≤ 186056749)
    (by decide : 186056749 ≤ 186122285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185991213 186122285).card = 482 := join_1_0

end S088C11
end Sude.GeneratedTwinScan
