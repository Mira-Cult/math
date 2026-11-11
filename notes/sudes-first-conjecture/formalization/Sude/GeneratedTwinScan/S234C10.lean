import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22182)) 492044333 492077101 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492044333 492077101).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22182 492044333 492077101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22183)) 492077101 492109869 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492077101 492109869).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22183 492077101 492109869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22184)) 492109869 492142637 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492109869 492142637).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22184 492109869 492142637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22185)) 492142637 492175405 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492142637 492175405).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22185 492142637 492175405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492044333 492109869).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 492044333 ≤ 492077101)
    (by decide : 492077101 ≤ 492109869) block0 block1

theorem join_0_1 : (twinPrimeSegment 492109869 492175405).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 492109869 ≤ 492142637)
    (by decide : 492142637 ≤ 492175405) block2 block3

theorem join_1_0 : (twinPrimeSegment 492044333 492175405).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 492044333 ≤ 492109869)
    (by decide : 492109869 ≤ 492175405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492044333 492175405).card = 416 := join_1_0

end S234C10
end Sude.GeneratedTwinScan
