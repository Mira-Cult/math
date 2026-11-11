import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15513)) 240648237 240681005 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240648237 240681005).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15513 240648237 240681005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15514)) 240681005 240713773 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240681005 240713773).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15514 240681005 240713773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15516)) 240713773 240746541 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240713773 240746541).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15516 240713773 240746541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15517)) 240746541 240779309 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240746541 240779309).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15517 240746541 240779309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240648237 240713773).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 240648237 ≤ 240681005)
    (by decide : 240681005 ≤ 240713773) block0 block1

theorem join_0_1 : (twinPrimeSegment 240713773 240779309).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 240713773 ≤ 240746541)
    (by decide : 240746541 ≤ 240779309) block2 block3

theorem join_1_0 : (twinPrimeSegment 240648237 240779309).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 240648237 ≤ 240713773)
    (by decide : 240713773 ≤ 240779309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240648237 240779309).card = 502 := join_1_0

end S114C12
end Sude.GeneratedTwinScan
