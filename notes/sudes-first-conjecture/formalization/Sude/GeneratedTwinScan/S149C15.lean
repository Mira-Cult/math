import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17733)) 314441773 314474541 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314441773 314474541).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17733 314441773 314474541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17734)) 314474541 314507309 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314474541 314507309).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17734 314474541 314507309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17735)) 314507309 314540077 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314507309 314540077).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17735 314507309 314540077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17736)) 314540077 314572845 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314540077 314572845).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17736 314540077 314572845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314441773 314507309).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 314441773 ≤ 314474541)
    (by decide : 314474541 ≤ 314507309) block0 block1

theorem join_0_1 : (twinPrimeSegment 314507309 314572845).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 314507309 ≤ 314540077)
    (by decide : 314540077 ≤ 314572845) block2 block3

theorem join_1_0 : (twinPrimeSegment 314441773 314572845).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 314441773 ≤ 314507309)
    (by decide : 314507309 ≤ 314572845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314441773 314572845).card = 470 := join_1_0

end S149C15
end Sude.GeneratedTwinScan
