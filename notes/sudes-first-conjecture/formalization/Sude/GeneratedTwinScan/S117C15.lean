import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15727)) 247332909 247365677 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247332909 247365677).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15727 247332909 247365677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15728)) 247365677 247398445 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 247365677 247398445).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15728 247365677 247398445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15729)) 247398445 247431213 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247398445 247431213).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15729 247398445 247431213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15730)) 247431213 247463981 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247431213 247463981).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15730 247431213 247463981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247332909 247398445).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 247332909 ≤ 247365677)
    (by decide : 247365677 ≤ 247398445) block0 block1

theorem join_0_1 : (twinPrimeSegment 247398445 247463981).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 247398445 ≤ 247431213)
    (by decide : 247431213 ≤ 247463981) block2 block3

theorem join_1_0 : (twinPrimeSegment 247332909 247463981).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 247332909 ≤ 247398445)
    (by decide : 247398445 ≤ 247463981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247332909 247463981).card = 459 := join_1_0

end S117C15
end Sude.GeneratedTwinScan
