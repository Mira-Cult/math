import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17677)) 312475693 312508461 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312475693 312508461).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17677 312475693 312508461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17678)) 312508461 312541229 = 89 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312508461 312541229).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17678 312508461 312541229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17679)) 312541229 312573997 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312541229 312573997).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17679 312541229 312573997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17680)) 312573997 312606765 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312573997 312606765).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17680 312573997 312606765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312475693 312541229).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 312475693 ≤ 312508461)
    (by decide : 312508461 ≤ 312541229) block0 block1

theorem join_0_1 : (twinPrimeSegment 312541229 312606765).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 312541229 ≤ 312573997)
    (by decide : 312573997 ≤ 312606765) block2 block3

theorem join_1_0 : (twinPrimeSegment 312475693 312606765).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 312475693 ≤ 312541229)
    (by decide : 312541229 ≤ 312606765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312475693 312606765).card = 418 := join_1_0

end S149C00
end Sude.GeneratedTwinScan
