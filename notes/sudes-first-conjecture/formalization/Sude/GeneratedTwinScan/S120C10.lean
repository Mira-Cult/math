import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15906)) 252969005 253001773 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 252969005 253001773).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15906 252969005 253001773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15907)) 253001773 253034541 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253001773 253034541).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15907 253001773 253034541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15908)) 253034541 253067309 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253034541 253067309).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15908 253034541 253067309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15909)) 253067309 253100077 = 87 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253067309 253100077).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15909 253067309 253100077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 252969005 253034541).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 252969005 ≤ 253001773)
    (by decide : 253001773 ≤ 253034541) block0 block1

theorem join_0_1 : (twinPrimeSegment 253034541 253100077).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 253034541 ≤ 253067309)
    (by decide : 253067309 ≤ 253100077) block2 block3

theorem join_1_0 : (twinPrimeSegment 252969005 253100077).card = 405 := by
  simpa using combineTwinPrimeSegments (by decide : 252969005 ≤ 253034541)
    (by decide : 253034541 ≤ 253100077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 252969005 253100077).card = 405 := join_1_0

end S120C10
end Sude.GeneratedTwinScan
