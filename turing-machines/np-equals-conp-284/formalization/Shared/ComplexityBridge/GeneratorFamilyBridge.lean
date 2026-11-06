import Shared.ComplexityBridge.TM2DisjoinPoly
import Shared.ComplexityBridge.TM2Serialize
import Shared.ComplexityBridge.TM2EmptyConstant
import Shared.Beeping.ControllerBinaryGenerator

/-! Reduce the remaining bounded-verifier generator obligation to its exact
unproved formula-family construction. Disjunction and output serialization
are now supplied by compiled canonical finite-machine proofs. -/
namespace Shared.ComplexityBridge.GeneratorFamilyBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CNFDisjunction
open Shared.ComplexityBridge.BoundedHardness


/-- The fixed public-input part of the pair encoding is itself constructed by
finite canonical polynomial-time machines; it carries no witness answer. -/
theorem pairPrefix_isPolyTime : ComplexityTheory.IsPolyTime
    Shared.ComplexityBridge.CircuitPairWitness.pairPrefix := by
  let mkPair : List Bool → List Bool × List Bool := fun x => (x,[])
  have hi : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have he : ComplexityTheory.IsPolyTime (fun _ : List Bool => ([] : List Bool)) := by
    apply Shared.ComplexityBridge.TM2EmptyConstant.isPolyTime
    rfl
  have hp : ComplexityTheory.IsPolyTime mkPair := Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime _ _ hi he
  have hs : ComplexityTheory.IsPolyTime (BitstringEncoding.bitEncode : List Bool × List Bool → List Bool) :=
    Shared.ComplexityBridge.TM2Serialize.isPolyTime
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp mkPair BitstringEncoding.bitEncode hp hs
  have he : (fun x : List Bool => BitstringEncoding.bitEncode (x,([] : List Bool))) =
      Shared.ComplexityBridge.CircuitPairWitness.pairPrefix := by
    funext x
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ [] = _
    simp [Shared.ComplexityBridge.CircuitPairWitness.pairPrefix]
  change ComplexityTheory.IsPolyTime (fun x => BitstringEncoding.bitEncode (x,([] : List Bool))) at h
  rw [he] at h
  exact h

def pairFamily (program : Program) (bound time : Polynomial Nat) (x : List Bool) : List Formula :=
  (List.range (bound.eval x.length+1)).map fun n =>
    Shared.ComplexityBridge.CircuitPairWitness.pairFormula program x n (commonFuel bound time x)

/-- Exact outstanding quantitative obligation: generate the entire list of
bounded-verifier formulas, for a fixed program and fixed polynomials, from
all raw bitstrings. The list encoding and all machine costs are canonical. -/
def PairFamilyPolyTime : Prop :=
  ∀ (program : Program) (bound time : Polynomial Nat), ComplexityTheory.IsPolyTime (pairFamily program bound time)

theorem reduction_eq (program : Program) (bound time : Polynomial Nat) (x : List Bool) :
    reduction program bound time x = BitstringEncoding.bitEncode (disjoin (pairFamily program bound time x)) := rfl

/-- Once the family construction is implemented in polynomial time, the
actual reduction follows using the proved disjunction and serialization
machines. This does not prove the family hypothesis. -/
theorem generator_of_pairFamily (hfamily : PairFamilyPolyTime) : GeneratorPolyTime := by
  intro program bound time
  let family := pairFamily program bound time
  have hf : ComplexityTheory.IsPolyTime family := hfamily program bound time
  have hd : ComplexityTheory.IsPolyTime disjoin := Shared.ComplexityBridge.TM2DisjoinPoly.disjoin_isPolyTime
  have hs : ComplexityTheory.IsPolyTime (BitstringEncoding.bitEncode : Formula → List Bool) :=
    Shared.ComplexityBridge.TM2Serialize.isPolyTime
  have h₁ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp family disjoin hf hd
  have h₂ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (fun x => disjoin (family x))
    (BitstringEncoding.bitEncode : Formula → List Bool) h₁ hs
  change ComplexityTheory.IsPolyTime (fun x => reduction program bound time x)
  simpa [family,reduction_eq] using h₂

/-- The two existential machine endpoints remain distinct and conditional on
one explicit formula-family implementation obligation. No record table is bound. -/
theorem pnp_exists_of_pairFamily (hfamily : PairFamilyPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.Beeping.ControllerBinaryGenerator.pnp_exists_of_generator (generator_of_pairFamily hfamily)

theorem npconp_exists_of_pairFamily (hfamily : PairFamilyPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.Beeping.ControllerBinaryGenerator.npconp_exists_of_generator (generator_of_pairFamily hfamily)
end Shared.ComplexityBridge.GeneratorFamilyBridge
