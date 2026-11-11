import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20352)) 414187565 414220333 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414187565 414220333).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20352 414187565 414220333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20353)) 414220333 414253101 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 414220333 414253101).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20353 414220333 414253101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20354)) 414253101 414285869 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 414253101 414285869).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20354 414253101 414285869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20354)) 414285869 414318637 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 414285869 414318637).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20354 414285869 414318637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414187565 414253101).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 414187565 ≤ 414220333)
    (by decide : 414220333 ≤ 414253101) block0 block1

theorem join_0_1 : (twinPrimeSegment 414253101 414318637).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 414253101 ≤ 414285869)
    (by decide : 414285869 ≤ 414318637) block2 block3

theorem join_1_0 : (twinPrimeSegment 414187565 414318637).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 414187565 ≤ 414253101)
    (by decide : 414253101 ≤ 414318637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414187565 414318637).card = 446 := join_1_0

end S197C08
end Sude.GeneratedTwinScan
