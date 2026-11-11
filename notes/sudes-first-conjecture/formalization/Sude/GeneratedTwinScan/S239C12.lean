import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22423)) 502792237 502825005 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502792237 502825005).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22423 502792237 502825005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22424)) 502825005 502857773 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502825005 502857773).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22424 502825005 502857773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22425)) 502857773 502890541 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502857773 502890541).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22425 502857773 502890541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22425)) 502890541 502923309 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502890541 502923309).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22425 502890541 502923309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502792237 502857773).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 502792237 ≤ 502825005)
    (by decide : 502825005 ≤ 502857773) block0 block1

theorem join_0_1 : (twinPrimeSegment 502857773 502923309).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 502857773 ≤ 502890541)
    (by decide : 502890541 ≤ 502923309) block2 block3

theorem join_1_0 : (twinPrimeSegment 502792237 502923309).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 502792237 ≤ 502857773)
    (by decide : 502857773 ≤ 502923309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502792237 502923309).card = 409 := join_1_0

end S239C12
end Sude.GeneratedTwinScan
