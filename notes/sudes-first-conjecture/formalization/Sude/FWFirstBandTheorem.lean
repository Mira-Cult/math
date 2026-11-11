import Sude.FWT75AnalyticSupply
import Sude.FastTwinFullPool

/-! Proof of `HasSquare n` across the entire FW and EW regimes (`19485 ≤ n ≤ 35733`)
from only the exempt published analytic inputs, with the twin-prime seed pool
discharged by the kernel-checked `FastTwinFullPool` certificate (`3,650,551` seeds). -/
namespace Sude
noncomputable section

set_option autoImplicit false

/-- Complete `HasSquare n` theorem across `19485 ≤ n ≤ 35733`, `Odd n`, from
    only the exempt published analytic hypotheses (`MVBrunTitchmarsh`,
    `BMORFiniteTheta`, `BMORExplicitFormulaImports`, `RSIndexUpper`,
    `RSIndexLower`, `RSIndexLowerSharp`, `RSIndexUpperSharp`). -/
theorem fw_and_ew_hasSquare
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (imp : BMORExplicitFormulaImports)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n) :
    HasSquare n := by
  apply fw_first_band_hasSquare_of_seeds mv bmor imp upper lower sharp upperSharp
    hnlo hnhi hodd finiteTwinSeeds
  · intro p hp
    exact ((mem_finiteTwinSeeds p).mp hp).2.2.2
  · intro p hp
    obtain ⟨h43, hp1, hp2, _⟩ := (mem_finiteTwinSeeds p).mp hp
    exact ⟨h43, hp1, hp2⟩
  · have h365 : 3650551 ≤ finiteTwinSeeds.card := finiteTwinSeeds_at_least_3650551
    omega

/-- First-band specialization (`19485 ≤ n ≤ 21248`, `Odd n`). -/
theorem fw_first_band_hasSquare
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (imp : BMORExplicitFormulaImports)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n) :
    HasSquare n :=
  fw_and_ew_hasSquare mv bmor imp upper lower sharp upperSharp hnlo (by omega) hodd

end
end Sude
