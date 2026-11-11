import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13174)) 173539373 173572141 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173539373 173572141).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13174 173539373 173572141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13175)) 173572141 173604909 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173572141 173604909).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13175 173572141 173604909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13177)) 173604909 173637677 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173604909 173637677).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13177 173604909 173637677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13178)) 173637677 173670445 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 173637677 173670445).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13178 173637677 173670445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173539373 173604909).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 173539373 ≤ 173572141)
    (by decide : 173572141 ≤ 173604909) block0 block1

theorem join_0_1 : (twinPrimeSegment 173604909 173670445).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 173604909 ≤ 173637677)
    (by decide : 173637677 ≤ 173670445) block2 block3

theorem join_1_0 : (twinPrimeSegment 173539373 173670445).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 173539373 ≤ 173604909)
    (by decide : 173604909 ≤ 173670445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173539373 173670445).card = 474 := join_1_0

end S082C12
end Sude.GeneratedTwinScan
