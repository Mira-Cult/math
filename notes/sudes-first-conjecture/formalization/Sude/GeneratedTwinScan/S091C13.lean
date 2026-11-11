import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13877)) 192544813 192577581 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192544813 192577581).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13877 192544813 192577581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13878)) 192577581 192610349 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192577581 192610349).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13878 192577581 192610349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13879)) 192610349 192643117 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 192610349 192643117).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13879 192610349 192643117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13880)) 192643117 192675885 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 192643117 192675885).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13880 192643117 192675885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192544813 192610349).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 192544813 ≤ 192577581)
    (by decide : 192577581 ≤ 192610349) block0 block1

theorem join_0_1 : (twinPrimeSegment 192610349 192675885).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 192610349 ≤ 192643117)
    (by decide : 192643117 ≤ 192675885) block2 block3

theorem join_1_0 : (twinPrimeSegment 192544813 192675885).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 192544813 ≤ 192610349)
    (by decide : 192610349 ≤ 192675885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192544813 192675885).card = 496 := join_1_0

end S091C13
end Sude.GeneratedTwinScan
