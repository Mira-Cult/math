import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20776)) 431620141 431652909 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431620141 431652909).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20776 431620141 431652909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20777)) 431652909 431685677 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431652909 431685677).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20777 431652909 431685677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20777)) 431685677 431718445 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431685677 431718445).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20777 431685677 431718445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20778)) 431718445 431751213 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431718445 431751213).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20778 431718445 431751213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431620141 431685677).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 431620141 ≤ 431652909)
    (by decide : 431652909 ≤ 431685677) block0 block1

theorem join_0_1 : (twinPrimeSegment 431685677 431751213).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 431685677 ≤ 431718445)
    (by decide : 431718445 ≤ 431751213) block2 block3

theorem join_1_0 : (twinPrimeSegment 431620141 431751213).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 431620141 ≤ 431685677)
    (by decide : 431685677 ≤ 431751213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431620141 431751213).card = 462 := join_1_0

end S205C13
end Sude.GeneratedTwinScan
