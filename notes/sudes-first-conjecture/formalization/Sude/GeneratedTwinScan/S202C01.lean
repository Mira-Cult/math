import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20586)) 423755821 423788589 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423755821 423788589).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20586 423755821 423788589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20586)) 423788589 423821357 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423788589 423821357).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20586 423788589 423821357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20587)) 423821357 423854125 = 87 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423821357 423854125).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20587 423821357 423854125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20588)) 423854125 423886893 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423854125 423886893).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20588 423854125 423886893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423755821 423821357).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 423755821 ≤ 423788589)
    (by decide : 423788589 ≤ 423821357) block0 block1

theorem join_0_1 : (twinPrimeSegment 423821357 423886893).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 423821357 ≤ 423854125)
    (by decide : 423854125 ≤ 423886893) block2 block3

theorem join_1_0 : (twinPrimeSegment 423755821 423886893).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 423755821 ≤ 423821357)
    (by decide : 423821357 ≤ 423886893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423755821 423886893).card = 406 := join_1_0

end S202C01
end Sude.GeneratedTwinScan
