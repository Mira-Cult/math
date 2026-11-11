import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15002)) 225050669 225083437 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 225050669 225083437).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15002 225050669 225083437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15003)) 225083437 225116205 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 225083437 225116205).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15003 225083437 225116205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15004)) 225116205 225148973 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 225116205 225148973).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15004 225116205 225148973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15006)) 225148973 225181741 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 225148973 225181741).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15006 225148973 225181741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 225050669 225116205).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 225050669 ≤ 225083437)
    (by decide : 225083437 ≤ 225116205) block0 block1

theorem join_0_1 : (twinPrimeSegment 225116205 225181741).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 225116205 ≤ 225148973)
    (by decide : 225148973 ≤ 225181741) block2 block3

theorem join_1_0 : (twinPrimeSegment 225050669 225181741).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 225050669 ≤ 225116205)
    (by decide : 225116205 ≤ 225181741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 225050669 225181741).card = 464 := join_1_0

end S107C05
end Sude.GeneratedTwinScan
