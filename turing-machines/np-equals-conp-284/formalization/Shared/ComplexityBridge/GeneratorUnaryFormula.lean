import Shared.ComplexityBridge.TM2UnaryRange
import Shared.ComplexityBridge.GeneratorFamilyBridge
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecificLimits.Normed
import Shared.ComplexityBridge.ClockBounds

/-! Correct the witness-length cost boundary. A binary length alone permits
an exponentially large CNF; the new interface includes a unary budget and
returns a fixed empty formula for lengths outside that budget. -/
namespace Shared.ComplexityBridge.GeneratorUnaryFormula
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.BoundedHardness

/-- Historical unbounded binary-length function. It is retained for source
provenance, but is not used as a hypothesis for machine endpoints. -/
def unaryPairFormula (program : Program) (z : (List Bool × List Bool) × Nat) : Formula :=
  Shared.ComplexityBridge.CircuitPairWitness.pairFormula program z.1.1 z.2 z.1.2.length

/-- Historical, overly strong proposition from commit e62bcf4. Its binary
witness-length input does not pay for a formula that grows linearly in the
numeric length. It is retained only for compatibility and is not assumed by
any endpoint in this module. -/
def UnaryPairFormulaPolyTime : Prop :=
  ∀ program : Program, ComplexityTheory.IsPolyTime (unaryPairFormula program)

/-- Every constructed formula contains at least two shape clauses for each
witness bit. This bound is on canonical output bits, not on a symbolic cost. -/
theorem pairFormula_output_lower (program : Program) (x : List Bool) (n fuel : Nat) :
    2*n ≤ (BitstringEncoding.bitEncode (Shared.ComplexityBridge.CircuitPairWitness.pairFormula program x n fuel)).length := by
  have h := Shared.ComplexityBridge.CNF.list_length_le_bitEncode
    (Shared.ComplexityBridge.CircuitPairWitness.pairFormula program x n fuel)
  have hlen : 2*n ≤ (Shared.ComplexityBridge.CircuitPairWitness.pairFormula program x n fuel).length := by
    simp only [Shared.ComplexityBridge.CircuitPairWitness.pairFormula,
      Shared.ComplexityBridge.CircuitPairWitness.constrainedFormula,List.length_append,
      Shared.ComplexityBridge.CircuitPairWitness.shapeClauses_length]
    omega
  exact le_trans hlen h

/-- The historical binary input can have linear encoded length while the
output already has exponentially many bits, even with empty public input and
zero fuel. -/
theorem binary_length_gap (program : Program) (k : Nat) :
    (BitstringEncoding.bitEncode ((([] : List Bool),([] : List Bool)),2^k)).length = k+4 ∧
    2*(2^k) ≤ (BitstringEncoding.bitEncode (unaryPairFormula program ((([] : List Bool),([] : List Bool)),2^k))).length := by
  constructor
  · change (BitstringEncoding.delimit
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode ([] : List Bool)) ++ BitstringEncoding.bitEncode ([] : List Bool)) ++
        BitstringEncoding.bitEncode (2^k : Nat)).length = k+4
    have he : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    have hn : BitstringEncoding.bitEncode (2^k : Nat) = (2^k : Nat).bits :=
      Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits (2^k)
    rw [he,hn]
    simp only [List.append_nil,BitstringEncoding.delimit,List.length_append,List.length_cons,List.length_nil,
      Nat.size_eq_bits_len,Nat.size_pow]
    omega
  · exact pairFormula_output_lower program [] (2^k) 0


/-- An exponential eventually exceeds every fixed power of the encoded input
length. -/
theorem exists_exponential_exceeds (d : Nat) : ∃ k : Nat, (k+6)^d < 2^k := by
  have hsmall := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (r := (2 : ℝ)) (by norm_num)).bound
    (show (0 : ℝ) < 1/128 by norm_num)
  obtain ⟨n,hn,hn6⟩ := (hsmall.and (Filter.eventually_ge_atTop 6)).exists
  let k := n-6
  have he : n = k+6 := by dsimp [k]; omega
  have hn' : (n : ℝ)^d ≤ (1/128 : ℝ)*(2 : ℝ)^n := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)^d),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)^n)] using hn
  have hp : (2 : ℝ)^n = 64*(2 : ℝ)^k := by rw [he,pow_add]; norm_num [mul_comm]
  rw [hp] at hn'
  have hpos : (0 : ℝ) < (2 : ℝ)^k := by positivity
  have hlt : ((k+6 : Nat) : ℝ)^d < (2 : ℝ)^k := by
    have hncast : (n : ℝ) = ((k+6 : Nat) : ℝ) := by exact_mod_cast he
    rw [hncast] at hn'
    linarith
  exact ⟨k,by exact_mod_cast hlt⟩

/-- The previous unbounded binary-input polynomial-time hypothesis is false
for every fixed program. This rules it out as a meaningful conditional bridge. -/
theorem unbounded_not_isPolyTime (program : Program) :
    ¬ ComplexityTheory.IsPolyTime (unaryPairFormula program) := by
  intro h
  obtain ⟨p,hp⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.output_length_poly (unaryPairFormula program) h
  obtain ⟨d,hd⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  obtain ⟨k,hk⟩ := exists_exponential_exceeds d
  have hgap := binary_length_gap program k
  have hupper := hp ((([] : List Bool),([] : List Bool)),2^k)
  rw [hgap.1] at hupper
  have hpoly := hd (k+4)
  have hlower := hgap.2
  have hshift : k+4+2 = k+6 := by omega
  rw [hshift] at hpoly
  omega

theorem not_UnaryPairFormulaPolyTime : ¬ UnaryPairFormulaPolyTime := by
  intro h
  exact unbounded_not_isPolyTime [] (h [])

/-- The binary witness length is checked against an explicit unary budget.
Out-of-budget inputs return the empty formula; the family bridge proves that
this fallback is never used for its enumerated witness lengths. -/
def boundedPairFormula (program : Program) (z : ((List Bool × List Bool) × List Bool) × Nat) : Formula :=
  if z.2 < z.1.2.length then
    Shared.ComplexityBridge.CircuitPairWitness.pairFormula program z.1.1.1 z.2 z.1.1.2.length
  else []

/-- Remaining obligation: an actual finite polynomial-time machine for the
bounded constructor, measured in the full encoded public input, unary fuel,
unary witness budget and binary witness length, including the fixed
out-of-budget branch. The program is fixed independently of the input. -/
def BoundedPairFormulaPolyTime : Prop :=
  ∀ program : Program, ComplexityTheory.IsPolyTime (boundedPairFormula program)

/-- A bounded single-formula machine, applied across the proved witness
range, constructs the exact formula family. -/
theorem pairFamily_of_boundedFormula (hformula : BoundedPairFormulaPolyTime) :
    Shared.ComplexityBridge.GeneratorFamilyBridge.PairFamilyPolyTime := by
  intro program bound time
  let fuel : List Bool → List Bool := fun x => List.replicate (commonFuel bound time x) true
  let budget : List Bool → List Bool := fun x => List.replicate (bound.eval x.length+1) true
  let ctx : List Bool → (List Bool × List Bool) × List Bool := fun x => ((x,fuel x),budget x)
  let indices : List Bool → List Nat := fun x => List.range (bound.eval x.length+1)
  let request : List Bool → ((List Bool × List Bool) × List Bool) × List Nat := fun x => (ctx x,indices x)
  have hi : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hf : ComplexityTheory.IsPolyTime fuel := Shared.ComplexityBridge.TM2UnaryPolynomialIO.commonFuel_isPolyTime bound time
  have hb : ComplexityTheory.IsPolyTime budget := Shared.ComplexityBridge.TM2UnaryPolynomialIO.witnessCount_isPolyTime bound
  have hc : ComplexityTheory.IsPolyTime ctx := Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime _ _
    (Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime _ _ hi hf) hb
  have hn : ComplexityTheory.IsPolyTime indices := Shared.ComplexityBridge.TM2UnaryRange.polynomialRange_isPolyTime bound
  have hreq : ComplexityTheory.IsPolyTime request := Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime ctx indices hc hn
  have hm := Shared.ComplexityBridge.TM2ContextMapGeneric.contextMap_isPolyTime (boundedPairFormula program) (hformula program)
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp request
    (Shared.ComplexityBridge.TM2ContextMapGeneric.contextMap (boundedPairFormula program)) hreq hm
  change ComplexityTheory.IsPolyTime (fun x => Shared.ComplexityBridge.GeneratorFamilyBridge.pairFamily program bound time x)
  have he : (fun x => Shared.ComplexityBridge.TM2ContextMapGeneric.contextMap (boundedPairFormula program) (request x)) =
      (fun x => Shared.ComplexityBridge.GeneratorFamilyBridge.pairFamily program bound time x) := by
    funext x
    simp only [Shared.ComplexityBridge.TM2ContextMapGeneric.contextMap,request,ctx,indices,fuel,budget,
      Shared.ComplexityBridge.GeneratorFamilyBridge.pairFamily]
    apply List.map_congr_left
    intro n hn
    have hlt : n < bound.eval x.length+1 := by simpa using hn
    simp [boundedPairFormula,hlt]
  rw [←he]
  exact h

theorem generator_of_boundedFormula (hformula : BoundedPairFormulaPolyTime) : GeneratorPolyTime :=
  Shared.ComplexityBridge.GeneratorFamilyBridge.generator_of_pairFamily (pairFamily_of_boundedFormula hformula)

theorem pnp_exists_of_boundedFormula (hformula : BoundedPairFormulaPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.Beeping.ControllerBinaryGenerator.pnp_exists_of_generator (generator_of_boundedFormula hformula)

theorem npconp_exists_of_boundedFormula (hformula : BoundedPairFormulaPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.Beeping.ControllerBinaryGenerator.npconp_exists_of_generator (generator_of_boundedFormula hformula)

namespace Fixtures
example : boundedPairFormula [] ((([],[]),[true]),1) = [] := rfl
example : boundedPairFormula [] ((([],[]),[true]),0) =
    Shared.ComplexityBridge.CircuitPairWitness.pairFormula [] [] 0 0 := rfl
end Fixtures

end Shared.ComplexityBridge.GeneratorUnaryFormula
