import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14190)) 201326637 201359405 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 201326637 201359405).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14190 201326637 201359405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14191)) 201359405 201392173 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 201359405 201392173).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14191 201359405 201392173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14192)) 201392173 201424941 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 201392173 201424941).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14192 201392173 201424941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14193)) 201424941 201457709 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 201424941 201457709).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14193 201424941 201457709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 201326637 201392173).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 201359405)
    (by decide : 201359405 ≤ 201392173) block0 block1

theorem join_0_1 : (twinPrimeSegment 201392173 201457709).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 201392173 ≤ 201424941)
    (by decide : 201424941 ≤ 201457709) block2 block3

theorem join_1_0 : (twinPrimeSegment 201326637 201457709).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 201392173)
    (by decide : 201392173 ≤ 201457709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 201326637 201457709).card = 493 := join_1_0

end S096C00
end Sude.GeneratedTwinScan
