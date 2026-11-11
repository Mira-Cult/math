import Sude.Statement
import Sude.BMORPublishedExplicitFormula
import Sude.FC2KBandTheorem
import Sude.FWFirstBandTheorem
import Sude.UpperTailTheorem

/-!
# Sude's First Theorem (Lean-Checked Proof Relative to Explicit Exempt Inputs)

Assembles the complete Lean-checked proof of Sude's First Theorem
(`∀ n, 0 < n → Odd n → Sude.HasSquare n`, and the value-bijection corollary
`Sude.sude_first_theorem_values` via `Sude.hasSquare_iff_values`) relative to
explicitly enumerated exempt inputs only:

1. **Finite small-order witness (`0 < n < 2000`, odd `n`)**:
   - `FiniteWitness` (`Sude/Statement.lean`)

2. **Rosser–Schoenfeld (1962)**, *Illinois J. Math.* 6, 64–94:
   - `RSPrimeCountLowerSharp`: Theorem 2, equation `(3.3)`, p. 69
   - `RSPrimeCountUpperSharp`: Theorem 2, equation `(3.4)`, p. 69
   - `RSPrimeCountLower`: Theorem 2 Corollary 1, equation `(3.5)`, p. 69
   - `RSPrimeCountUpper`: Theorem 2 Corollary 1, equation `(3.6)`, p. 69
   - `RSIndexLowerSharp`: Theorem 3, equation `(3.10)`, p. 69
   - `RSIndexUpperSharp`: Theorem 3, equation `(3.11)`, p. 69
   - `RSIndexLower`: Theorem 3 Corollary, equation `(3.12)`, p. 69
   - `RSIndexUpper`: Theorem 3 Corollary, equation `(3.13)`, p. 69
   - `RSThetaUpper`: Theorem 4, equation `(3.15)`, p. 70

3. **Bennett–Martin–O'Bryant–Rechnitzer (2018)**, *Illinois J. Math.* 62, 427–532:
   - `BMORFiniteTheta`: Theorem 1.9 theta conjunct and `(1.18)`, pp. 434–435
   - `BMORProp2_1`: Proposition 2.1, equations `(2.3)`–`(2.7)`, pp. 438–439
   - `BMORProp2_5`: Proposition 2.5, equation `(2.10)`, p. 441
   - `BMORProp2_7`: Definition 2.6 & Proposition 2.7, p. 441
   - `BMORProp4_34`: Definition 3.1 (p. 451) & Proposition 4.34, pp. 478–479

4. **Montgomery–Vaughan (1973)**, *Mathematika* 20, 119–134:
   - `MVBrunTitchmarsh`: Theorem 2, equation `(1.10)`, p. 121

All internal numerical certificates (including the 8,742-order FTT Lucas target
table, FPF prefix sieves, and the 3,650,551-pair twin-prime pool), explicit-formula
Stieltjes summation and zero-sum reductions (`bmorExplicitFormulaImports_of_published`),
and all three tail bands (`2001 ≤ n ≤ 19483` in `fc2k_hasSquare`,
`19485 ≤ n ≤ 35733` in `fw_and_ew_hasSquare`, and `35735 ≤ n` in
`upper_tail_hasSquare`) are proved inside Lean without `TailObligation`,
`BMORFinitePiFour`, or any controller/certificate premise.
-/

set_option autoImplicit false

namespace Sude

noncomputable section

/-- Complete proof of `TailObligation` (`∀ n, 2001 ≤ n → Odd n → HasSquare n`) from the
15 flat verbatim published analytic inputs alone. -/
theorem tail_hasSquare
    (rs_pi_lower_sharp : RSPrimeCountLowerSharp)
    (rs_pi_upper_sharp : RSPrimeCountUpperSharp)
    (rs_pi_lower : RSPrimeCountLower)
    (rs_pi_upper : RSPrimeCountUpper)
    (rs_idx_lower_sharp : RSIndexLowerSharp)
    (rs_idx_upper_sharp : RSIndexUpperSharp)
    (rs_idx_lower : RSIndexLower)
    (rs_idx_upper : RSIndexUpper)
    (rs_theta_upper : RSThetaUpper)
    (bmor_theta : BMORFiniteTheta)
    (bmor_prop2_1 : BMORProp2_1)
    (bmor_prop2_5 : BMORProp2_5)
    (bmor_prop2_7 : BMORProp2_7)
    (bmor_prop4_34 : BMORProp4_34)
    (mv_bt : MVBrunTitchmarsh) :
    TailObligation := by
  let rs : RSPrimeCountImports :=
    { lower_sharp := rs_pi_lower_sharp
      upper_sharp := rs_pi_upper_sharp
      lower := rs_pi_lower
      upper := rs_pi_upper }
  let pub : BMORPublishedExplicitFormula :=
    { prop2_1 := bmor_prop2_1
      prop2_5 := bmor_prop2_5
      prop2_7 := bmor_prop2_7
      prop4_34 := bmor_prop4_34 }
  let imp : BMORExplicitFormulaImports :=
    bmorExplicitFormulaImports_of_published pub rs_theta_upper
  intro n hn hodd
  by_cases h1 : n ≤ 19483
  · exact fc2k_hasSquare bmor_theta imp rs rs_idx_upper rs_idx_lower_sharp
      rs_idx_upper_sharp hn h1 hodd
  · by_cases h2 : n ≤ 35733
    · have hn19485 : 19485 ≤ n := by
        obtain ⟨k, hk⟩ := hodd
        omega
      exact fw_and_ew_hasSquare mv_bt bmor_theta imp rs_idx_upper rs_idx_lower
        rs_idx_lower_sharp rs_idx_upper_sharp hn19485 h2 hodd
    · have hn35735 : 35735 ≤ n := by
        obtain ⟨k, hk⟩ := hodd
        omega
      exact upper_tail_hasSquare bmor_theta imp mv_bt rs rs_idx_lower
        rs_idx_lower_sharp rs_idx_upper hn35735 hodd

/-- **Sude's First Theorem** (rank-equivalence formulation, `Sude.HasSquare n`),
proved in Lean relative to `FiniteWitness` (`0 < n < 2000`, odd `n`) and the
15 verbatim published analytic inputs from Rosser–Schoenfeld (1962),
Bennett–Martin–O'Bryant–Rechnitzer (2018), and Montgomery–Vaughan (1973). -/
theorem sude_first_theorem
    (finite : FiniteWitness)
    (rs_pi_lower_sharp : RSPrimeCountLowerSharp)
    (rs_pi_upper_sharp : RSPrimeCountUpperSharp)
    (rs_pi_lower : RSPrimeCountLower)
    (rs_pi_upper : RSPrimeCountUpper)
    (rs_idx_lower_sharp : RSIndexLowerSharp)
    (rs_idx_upper_sharp : RSIndexUpperSharp)
    (rs_idx_lower : RSIndexLower)
    (rs_idx_upper : RSIndexUpper)
    (rs_theta_upper : RSThetaUpper)
    (bmor_theta : BMORFiniteTheta)
    (bmor_prop2_1 : BMORProp2_1)
    (bmor_prop2_5 : BMORProp2_5)
    (bmor_prop2_7 : BMORProp2_7)
    (bmor_prop4_34 : BMORProp4_34)
    (mv_bt : MVBrunTitchmarsh) :
    ∀ n, 0 < n → Odd n → HasSquare n :=
  compose_finite_and_open_tail finite
    (tail_hasSquare
      rs_pi_lower_sharp rs_pi_upper_sharp rs_pi_lower rs_pi_upper
      rs_idx_lower_sharp rs_idx_upper_sharp rs_idx_lower rs_idx_upper
      rs_theta_upper bmor_theta
      bmor_prop2_1 bmor_prop2_5 bmor_prop2_7 bmor_prop4_34
      mv_bt)

/-- **Sude's First Theorem** (value-bijection formulation, `Cell n ≃ pool n`),
derived via `hasSquare_iff_values` from `sude_first_theorem`. -/
theorem sude_first_theorem_values
    (finite : FiniteWitness)
    (rs_pi_lower_sharp : RSPrimeCountLowerSharp)
    (rs_pi_upper_sharp : RSPrimeCountUpperSharp)
    (rs_pi_lower : RSPrimeCountLower)
    (rs_pi_upper : RSPrimeCountUpper)
    (rs_idx_lower_sharp : RSIndexLowerSharp)
    (rs_idx_upper_sharp : RSIndexUpperSharp)
    (rs_idx_lower : RSIndexLower)
    (rs_idx_upper : RSIndexUpper)
    (rs_theta_upper : RSThetaUpper)
    (bmor_theta : BMORFiniteTheta)
    (bmor_prop2_1 : BMORProp2_1)
    (bmor_prop2_5 : BMORProp2_5)
    (bmor_prop2_7 : BMORProp2_7)
    (bmor_prop4_34 : BMORProp4_34)
    (mv_bt : MVBrunTitchmarsh) :
    ∀ n, 0 < n → Odd n → ∃ b : Cell n ≃ pool n, ValuesValid b := by
  intro n hpos hodd
  exact (hasSquare_iff_values n).mp
    (sude_first_theorem finite
      rs_pi_lower_sharp rs_pi_upper_sharp rs_pi_lower rs_pi_upper
      rs_idx_lower_sharp rs_idx_upper_sharp rs_idx_lower rs_idx_upper
      rs_theta_upper bmor_theta
      bmor_prop2_1 bmor_prop2_5 bmor_prop2_7 bmor_prop4_34
      mv_bt n hpos hodd)

end

end Sude
