import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22803)) 519962669 519995437 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519962669 519995437).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22803 519962669 519995437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22804)) 519995437 520028205 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519995437 520028205).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22804 519995437 520028205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22804)) 520028205 520060973 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520028205 520060973).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22804 520028205 520060973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22805)) 520060973 520093741 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520060973 520093741).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22805 520060973 520093741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519962669 520028205).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 519962669 ≤ 519995437)
    (by decide : 519995437 ≤ 520028205) block0 block1

theorem join_0_1 : (twinPrimeSegment 520028205 520093741).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 520028205 ≤ 520060973)
    (by decide : 520060973 ≤ 520093741) block2 block3

theorem join_1_0 : (twinPrimeSegment 519962669 520093741).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 519962669 ≤ 520028205)
    (by decide : 520028205 ≤ 520093741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519962669 520093741).card = 439 := join_1_0

end S247C15
end Sude.GeneratedTwinScan
