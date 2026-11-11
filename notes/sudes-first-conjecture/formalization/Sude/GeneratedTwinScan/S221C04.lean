import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21541)) 463994925 464027693 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463994925 464027693).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21541 463994925 464027693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21542)) 464027693 464060461 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464027693 464060461).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21542 464027693 464060461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21542)) 464060461 464093229 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464060461 464093229).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21542 464060461 464093229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21543)) 464093229 464125997 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464093229 464125997).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21543 464093229 464125997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463994925 464060461).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 463994925 ≤ 464027693)
    (by decide : 464027693 ≤ 464060461) block0 block1

theorem join_0_1 : (twinPrimeSegment 464060461 464125997).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 464060461 ≤ 464093229)
    (by decide : 464093229 ≤ 464125997) block2 block3

theorem join_1_0 : (twinPrimeSegment 463994925 464125997).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 463994925 ≤ 464060461)
    (by decide : 464060461 ≤ 464125997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463994925 464125997).card = 415 := join_1_0

end S221C04
end Sude.GeneratedTwinScan
