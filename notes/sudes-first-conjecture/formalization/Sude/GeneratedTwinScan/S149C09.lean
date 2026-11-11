import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17711)) 313655341 313688109 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 313655341 313688109).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17711 313655341 313688109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17712)) 313688109 313720877 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313688109 313720877).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17712 313688109 313720877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17713)) 313720877 313753645 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313720877 313753645).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17713 313720877 313753645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17714)) 313753645 313786413 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 313753645 313786413).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17714 313753645 313786413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 313655341 313720877).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 313655341 ≤ 313688109)
    (by decide : 313688109 ≤ 313720877) block0 block1

theorem join_0_1 : (twinPrimeSegment 313720877 313786413).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 313720877 ≤ 313753645)
    (by decide : 313753645 ≤ 313786413) block2 block3

theorem join_1_0 : (twinPrimeSegment 313655341 313786413).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 313655341 ≤ 313720877)
    (by decide : 313720877 ≤ 313786413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 313655341 313786413).card = 434 := join_1_0

end S149C09
end Sude.GeneratedTwinScan
