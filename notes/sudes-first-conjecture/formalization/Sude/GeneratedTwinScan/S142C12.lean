import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17303)) 299368493 299401261 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 299368493 299401261).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17303 299368493 299401261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17304)) 299401261 299434029 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299401261 299434029).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17304 299401261 299434029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17305)) 299434029 299466797 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299434029 299466797).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17305 299434029 299466797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17306)) 299466797 299499565 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299466797 299499565).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17306 299466797 299499565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 299368493 299434029).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 299368493 ≤ 299401261)
    (by decide : 299401261 ≤ 299434029) block0 block1

theorem join_0_1 : (twinPrimeSegment 299434029 299499565).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 299434029 ≤ 299466797)
    (by decide : 299466797 ≤ 299499565) block2 block3

theorem join_1_0 : (twinPrimeSegment 299368493 299499565).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 299368493 ≤ 299434029)
    (by decide : 299434029 ≤ 299499565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 299368493 299499565).card = 492 := join_1_0

end S142C12
end Sude.GeneratedTwinScan
