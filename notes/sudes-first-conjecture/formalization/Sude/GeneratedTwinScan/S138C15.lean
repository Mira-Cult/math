import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17070)) 291373101 291405869 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291373101 291405869).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17070 291373101 291405869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17071)) 291405869 291438637 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291405869 291438637).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17071 291405869 291438637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17072)) 291438637 291471405 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291438637 291471405).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17072 291438637 291471405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17073)) 291471405 291504173 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291471405 291504173).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17073 291471405 291504173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291373101 291438637).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 291373101 ≤ 291405869)
    (by decide : 291405869 ≤ 291438637) block0 block1

theorem join_0_1 : (twinPrimeSegment 291438637 291504173).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 291438637 ≤ 291471405)
    (by decide : 291471405 ≤ 291504173) block2 block3

theorem join_1_0 : (twinPrimeSegment 291373101 291504173).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 291373101 ≤ 291438637)
    (by decide : 291438637 ≤ 291504173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291373101 291504173).card = 440 := join_1_0

end S138C15
end Sude.GeneratedTwinScan
