import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16947)) 287178797 287211565 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287178797 287211565).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16947 287178797 287211565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16948)) 287211565 287244333 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287211565 287244333).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16948 287211565 287244333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16949)) 287244333 287277101 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287244333 287277101).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16949 287244333 287277101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16950)) 287277101 287309869 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287277101 287309869).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16950 287277101 287309869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287178797 287244333).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 287178797 ≤ 287211565)
    (by decide : 287211565 ≤ 287244333) block0 block1

theorem join_0_1 : (twinPrimeSegment 287244333 287309869).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 287244333 ≤ 287277101)
    (by decide : 287277101 ≤ 287309869) block2 block3

theorem join_1_0 : (twinPrimeSegment 287178797 287309869).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 287178797 ≤ 287244333)
    (by decide : 287244333 ≤ 287309869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287178797 287309869).card = 462 := join_1_0

end S136C15
end Sude.GeneratedTwinScan
