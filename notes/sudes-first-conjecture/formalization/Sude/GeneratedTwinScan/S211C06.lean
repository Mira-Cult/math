import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21055)) 443285549 443318317 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443285549 443318317).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21055 443285549 443318317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21055)) 443318317 443351085 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443318317 443351085).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21055 443318317 443351085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21056)) 443351085 443383853 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443351085 443383853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21056 443351085 443383853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21057)) 443383853 443416621 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443383853 443416621).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21057 443383853 443416621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443285549 443351085).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 443285549 ≤ 443318317)
    (by decide : 443318317 ≤ 443351085) block0 block1

theorem join_0_1 : (twinPrimeSegment 443351085 443416621).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 443351085 ≤ 443383853)
    (by decide : 443383853 ≤ 443416621) block2 block3

theorem join_1_0 : (twinPrimeSegment 443285549 443416621).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 443285549 ≤ 443351085)
    (by decide : 443351085 ≤ 443416621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443285549 443416621).card = 447 := join_1_0

end S211C06
end Sude.GeneratedTwinScan
