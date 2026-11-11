import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17917)) 320995373 321028141 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320995373 321028141).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17917 320995373 321028141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17918)) 321028141 321060909 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321028141 321060909).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17918 321028141 321060909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17919)) 321060909 321093677 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321060909 321093677).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17919 321060909 321093677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17920)) 321093677 321126445 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 321093677 321126445).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17920 321093677 321126445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320995373 321060909).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 320995373 ≤ 321028141)
    (by decide : 321028141 ≤ 321060909) block0 block1

theorem join_0_1 : (twinPrimeSegment 321060909 321126445).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 321060909 ≤ 321093677)
    (by decide : 321093677 ≤ 321126445) block2 block3

theorem join_1_0 : (twinPrimeSegment 320995373 321126445).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 320995373 ≤ 321060909)
    (by decide : 321060909 ≤ 321126445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320995373 321126445).card = 413 := join_1_0

end S153C01
end Sude.GeneratedTwinScan
