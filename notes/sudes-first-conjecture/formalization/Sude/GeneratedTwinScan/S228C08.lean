import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21891)) 479199277 479232045 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 479199277 479232045).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21891 479199277 479232045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21892)) 479232045 479264813 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 479232045 479264813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21892 479232045 479264813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21892)) 479264813 479297581 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 479264813 479297581).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21892 479264813 479297581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21893)) 479297581 479330349 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 479297581 479330349).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21893 479297581 479330349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 479199277 479264813).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 479199277 ≤ 479232045)
    (by decide : 479232045 ≤ 479264813) block0 block1

theorem join_0_1 : (twinPrimeSegment 479264813 479330349).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 479264813 ≤ 479297581)
    (by decide : 479297581 ≤ 479330349) block2 block3

theorem join_1_0 : (twinPrimeSegment 479199277 479330349).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 479199277 ≤ 479264813)
    (by decide : 479264813 ≤ 479330349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 479199277 479330349).card = 441 := join_1_0

end S228C08
end Sude.GeneratedTwinScan
