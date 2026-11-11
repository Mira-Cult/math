import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19212)) 369098797 369131565 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369098797 369131565).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19212 369098797 369131565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19213)) 369131565 369164333 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369131565 369164333).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19213 369131565 369164333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19214)) 369164333 369197101 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369164333 369197101).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19214 369164333 369197101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19215)) 369197101 369229869 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369197101 369229869).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19215 369197101 369229869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369098797 369164333).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 369131565)
    (by decide : 369131565 ≤ 369164333) block0 block1

theorem join_0_1 : (twinPrimeSegment 369164333 369229869).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 369164333 ≤ 369197101)
    (by decide : 369197101 ≤ 369229869) block2 block3

theorem join_1_0 : (twinPrimeSegment 369098797 369229869).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 369164333)
    (by decide : 369164333 ≤ 369229869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369098797 369229869).card = 436 := join_1_0

end S176C00
end Sude.GeneratedTwinScan
