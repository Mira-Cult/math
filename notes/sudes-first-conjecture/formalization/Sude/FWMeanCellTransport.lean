import Sude.FWMeanFunctions

/-! Pure ordered-field transport of correlated mean bounds to rational
cell endpoints. All count and error estimates are explicit hypotheses. -/
namespace Sude
noncomputable section

/-- Transport scaled correlated mean estimates through a positive logarithm
cell. Here `q` is the scaled pool count; `d,e` are the two count-error
charges, `ell` is the Li(4) charge, and `t` is the final-sum endpoint
charge. This lemma neither imports BMOR nor assumes a target mean bound. -/
theorem fw_mean_cell_transport {a u b c W q m d e ell t : ℝ}
    (ha : 0 < a) (hau : a ≤ u) (hub : u ≤ b) (hW : 0 < W)
    (hq : 0 < q) (hqlo : fwMeanA u - c ≤ q) (hqhi : q ≤ fwMeanB u + c)
    (hd : d ≤ c) (he : e ≤ c) (hell : ell ≤ 4*b / W^2)
    (ht : t ≤ fwMeanB u / W)
    (hqlower : 0 < fwMeanA b - c)
    (hlower : 0 ≤ fwMeanA (2*b)/2 - 2*c - 4*b/W^2)
    (hupper : 0 ≤ fwMeanB (2*a)/2 + 2*c + fwMeanB a/W)
    (hmeanlo : (fwMeanA (2*u)/2 - d - e - ell)/q ≤ m)
    (hmeanhi : m ≤ (fwMeanB (2*u)/2 + d + e + t)/q) :
    (fwMeanA (2*b)/2 - 2*c - 4*b/W^2) / (fwMeanB a+c) ≤ m ∧
      m ≤ (fwMeanB (2*a)/2 + 2*c + fwMeanB a/W) / (fwMeanA b-c) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hb : 0 < b := lt_of_lt_of_le hu hub
  have hAbu : fwMeanA b ≤ fwMeanA u := fwMeanA_antitoneOn hu hb hub
  have hBua : fwMeanB u ≤ fwMeanB a := fwMeanB_antitoneOn ha hu hau
  have hA2 : fwMeanA (2*b) ≤ fwMeanA (2*u) :=
    fwMeanA_antitoneOn (show 2*u ∈ Set.Ioi 0 by change 0 < 2*u; positivity)
      (show 2*b ∈ Set.Ioi 0 by change 0 < 2*b; positivity) (by linarith)
  have hB2 : fwMeanB (2*u) ≤ fwMeanB (2*a) :=
    fwMeanB_antitoneOn (show 2*a ∈ Set.Ioi 0 by change 0 < 2*a; positivity)
      (show 2*u ∈ Set.Ioi 0 by change 0 < 2*u; positivity) (by linarith)
  have htw : fwMeanB u / W ≤ fwMeanB a / W :=
    div_le_div_of_nonneg_right hBua hW.le
  have hqendlo : fwMeanA b - c ≤ q := by linarith
  have hqendhi : q ≤ fwMeanB a + c := by linarith
  have hnlo : fwMeanA (2*b)/2 - 2*c - 4*b/W^2 ≤
      fwMeanA (2*u)/2 - d - e - ell := by linarith
  have hnhi : fwMeanB (2*u)/2 + d + e + t ≤
      fwMeanB (2*a)/2 + 2*c + fwMeanB a/W := by linarith
  constructor
  · calc
      _ ≤ (fwMeanA (2*b)/2 - 2*c - 4*b/W^2) / q :=
        div_le_div_of_nonneg_left hlower hq hqendhi
      _ ≤ (fwMeanA (2*u)/2 - d - e - ell) / q :=
        div_le_div_of_nonneg_right hnlo hq.le
      _ ≤ m := hmeanlo
  · calc
      m ≤ (fwMeanB (2*u)/2 + d + e + t) / q := hmeanhi
      _ ≤ (fwMeanB (2*a)/2 + 2*c + fwMeanB a/W) / q :=
        div_le_div_of_nonneg_right hnhi hq.le
      _ ≤ _ := div_le_div_of_nonneg_left hupper hqlower hqendlo

end
end Sude
