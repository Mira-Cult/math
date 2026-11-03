import Shared.ComplexityBridge.GeneratorUnaryFormula
import Shared.ComplexityBridge.TM2UnaryRange
import Shared.ComplexityBridge.TM2NumeralPairCompare
import Shared.ComplexityBridge.TM2UnaryValidation
import Shared.ComplexityBridge.TM2Complement
import Shared.ComplexityBridge.TM2Serialize

/-! An actual polynomial-time budget guard for a binary witness length.
The range enumeration is bounded by the unary token count and all list and
bitstring serialization costs are included in the canonical TM2 proofs. -/
namespace Shared.ComplexityBridge.TM2BoundedWitnessGuard

open Shared.ComplexityBridge

def numericNe (p : Nat × Nat) : Bool := p.1 != p.2

theorem numericNe_isPolyTime : ComplexityTheory.IsPolyTime numericNe := by
  let encode : Nat → List Bool := BitstringEncoding.bitEncode
  let prep : Nat × Nat → List Bool × List Bool := fun p => (encode p.1,encode p.2)
  have he : ComplexityTheory.IsPolyTime encode := TM2Serialize.isPolyTime
  have hf : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => p.1) := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => p.2) := TM2GuardAllStep.second_isPolyTime
  have hp : ComplexityTheory.IsPolyTime prep := TM2GuardAllStep.pair_isPolyTime _ _
    (TM2Compose.isPolyTime_comp (fun p : Nat × Nat => p.1) encode hf he)
    (TM2Compose.isPolyTime_comp (fun p : Nat × Nat => p.2) encode hs he)
  have hc := TM2Complement.pair_complement TM2NumeralPairCompare.answer TM2NumeralPairCompare.answer_isPolyTime
  have ht := TM2Compose.isPolyTime_comp prep (fun p => !TM2NumeralPairCompare.answer p) hp hc
  have hEq : (fun p => !TM2NumeralPairCompare.answer (prep p)) = numericNe := by
    funext p
    apply Bool.eq_iff_iff.mpr
    have h : TM2NumeralPairCompare.answer (prep p) = true ↔ p.1 = p.2 := by
      rw [TM2NumeralPairCompare.answer_correct]
      change Computability.decodeNat (Computability.encodeNat p.1) =
        Computability.decodeNat (Computability.encodeNat p.2) ↔ _
      simp
    cases hval : TM2NumeralPairCompare.answer (prep p) <;> simp_all [numericNe]
  rw [←hEq]
  exact ht

/-- A binary length is below the number of unary tokens. The token values do
not matter. The range is enumerated explicitly, including zero. -/
def guard (p : List Bool × Nat) : Bool :=
  !((List.range p.1.length).map (fun n => numericNe (p.2,n))).all id

theorem guard_correct (tokens : List Bool) (n : Nat) :
    guard (tokens,n) = true ↔ n < tokens.length := by
  simp [guard,numericNe]

/-- Finite TM2 program for the guard. The binary integer is never expanded
unless it already lies in the unary-sized enumerated range. -/
theorem guard_isPolyTime : ComplexityTheory.IsPolyTime guard := by
  let budget : List Bool × Nat → List Bool := fun p => p.1
  let value : List Bool × Nat → Nat := fun p => p.2
  let indices : List Bool × Nat → List Nat := fun p => TM2UnaryRange.rangeFromTokens (budget p)
  let request : List Bool × Nat → Nat × List Nat := fun p => (value p, indices p)
  let tests : List Bool × Nat → List Bool := fun p => TM2ContextMapGeneric.contextMap numericNe (request p)
  let any : List Bool → Bool := fun xs => !(xs.all id)
  have hb : ComplexityTheory.IsPolyTime budget := TM2PairFirst.first_isPolyTime
  have hv : ComplexityTheory.IsPolyTime value := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices :=
    TM2Compose.isPolyTime_comp budget TM2UnaryRange.rangeFromTokens hb TM2UnaryRange.rangeFromTokens_isPolyTime
  have hr : ComplexityTheory.IsPolyTime request := TM2GuardAllStep.pair_isPolyTime value indices hv hi
  have hm := TM2ContextMapGeneric.contextMap_isPolyTime numericNe numericNe_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tests := TM2Compose.isPolyTime_comp request
    (TM2ContextMapGeneric.contextMap numericNe) hr hm
  have ha : ComplexityTheory.IsPolyTime any := by
    have h : ComplexityTheory.IsPolyTime (fun xs : List Bool => xs.all id) := by
      simpa only [Shared.Codes.UnaryRequestValidation.unaryCheck_correct] using TM2UnaryValidation.unaryCheck_isPolyTime
    exact TM2Complement.p_complement (fun xs => xs.all id) h
  have h := TM2Compose.isPolyTime_comp tests any ht ha
  have he : (fun p => any (tests p)) = guard := by
    funext p
    rfl
  rw [←he]
  exact h

/-- Guard for the exact bounded-generator input, including the public input
and unary fuel fields. Their encoded traversal is charged by the projection
and pairing machines. -/
def generatorGuard (z : ((List Bool × List Bool) × List Bool) × Nat) : Bool :=
  guard (z.1.2,z.2)

theorem generatorGuard_correct (z : ((List Bool × List Bool) × List Bool) × Nat) :
    generatorGuard z = true ↔ z.2 < z.1.2.length := guard_correct z.1.2 z.2

theorem generatorGuard_isPolyTime : ComplexityTheory.IsPolyTime generatorGuard := by
  let first : ((List Bool × List Bool) × List Bool) × Nat → (List Bool × List Bool) × List Bool := fun z => z.1
  let second : ((List Bool × List Bool) × List Bool) × Nat → Nat := fun z => z.2
  let getBudget : (List Bool × List Bool) × List Bool → List Bool := fun z => z.2
  let budget : ((List Bool × List Bool) × List Bool) × Nat → List Bool := fun z => getBudget (first z)
  let request : ((List Bool × List Bool) × List Bool) × Nat → List Bool × Nat := fun z => (budget z,second z)
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hg : ComplexityTheory.IsPolyTime getBudget := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime budget := TM2Compose.isPolyTime_comp first getBudget hf hg
  have hr : ComplexityTheory.IsPolyTime request := TM2GuardAllStep.pair_isPolyTime budget second hb hs
  have h := TM2Compose.isPolyTime_comp request guard hr guard_isPolyTime
  change ComplexityTheory.IsPolyTime (fun z : ((List Bool × List Bool) × List Bool) × Nat => guard (z.1.2,z.2))
  exact h

/-- The machine-computable guard selects exactly the branch used by the
bounded formula constructor. -/
theorem boundedPairFormula_guard (program : Shared.Codes.FinitePrograms.Program)
    (z : ((List Bool × List Bool) × List Bool) × Nat) :
    GeneratorUnaryFormula.boundedPairFormula program z =
      if generatorGuard z then
        CircuitPairWitness.pairFormula program z.1.1.1 z.2 z.1.1.2.length
      else [] := by
  by_cases h : z.2 < z.1.2.length
  · have hg : generatorGuard z = true := (generatorGuard_correct z).2 h
    simp [GeneratorUnaryFormula.boundedPairFormula,h,hg]
  · have hg : generatorGuard z = false := by
      cases he : generatorGuard z with
      | false => rfl
      | true => exact False.elim (h ((generatorGuard_correct z).1 he))
    simp [GeneratorUnaryFormula.boundedPairFormula,h,hg]

namespace Fixtures
example : guard ([],0) = false := rfl
example : guard ([false,true],0) = true := rfl
example : guard ([false,true],1) = true := rfl
example : guard ([false,true],2) = false := rfl
example : guard ([false,true],3) = false := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BoundedWitnessGuard
