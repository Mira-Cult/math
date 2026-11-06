import Shared.ComplexityBridge.TM2BitstringWhole
import Shared.ComplexityBridge.TM2Whole

/-! The executable, clocked bitstring evaluator is sound for the public
polynomial-time class. All time bounds count TM2 statement blocks. -/

set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BitstringPoly
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2Combined
open Shared.ComplexityBridge.TM2FiniteReverse Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2StackBound
open Shared.ComplexityBridge.TM2BitstringOutput
open Shared.Codes.TM2Program Shared.Codes.TM2StatementExecution
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability

/-- A successful comparison exposes the actual validated numeric execution.
Malformed descriptors, timeouts, and invalid output cannot satisfy it. -/
theorem successful_numeric_result (c : Shared.Codes.TM2Candidate.Candidate)
    (bits output : List Bool) (heval : Evaluator.evaluate c bits = some output) :
    let d := inputDataOfRaw c.1.2.2
    ∃ p, decodeProgram c.1.1 = some p ∧ validInputData d = true ∧ d.main < p.length ∧
      programValid p d.stackCount d.states d.symbols = true ∧
      ∃ start r, buildStart d bits = some start ∧
        run p ((bits.length+2)^c.1.2.1) start = .halted r ∧
        extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.label,r.memory) = some output := by
  let d := inputDataOfRaw c.1.2.2
  have hv : Evaluator.descriptorValid c = true := by
    cases hv : Evaluator.descriptorValid c with
    | false => simp [Evaluator.evaluate,hv] at heval
    | true => rfl
  have hc : Shared.Codes.TM2CheckedCandidate.candidateValid c = true := by
    simp only [Evaluator.descriptorValid,Bool.and_eq_true] at hv ⊢
    exact hv.1.1.1.1
  have hdata : validInputData d = true := by
    cases hd : validInputData d with
    | true => rfl
    | false =>
      have hin : buildRaw (c.1.2.2,bits) = none := by
        rw [← inputRaw_ofRaw c.1.2.2,buildRaw_eq]
        simp [buildStart,hd,d]
      have := Evaluator.invalid_input_rejected c bits hin
      rw [this] at heval
      contradiction
  cases hpdecode : decodeProgram c.1.1 with
  | none => simp [Shared.Codes.TM2CheckedCandidate.candidateValid,hpdecode] at hc
  | some p =>
    have hp : programValid p d.stackCount d.states d.symbols = true := by
      simpa [Shared.Codes.TM2CheckedCandidate.candidateValid,hpdecode,d,inputDataOfRaw] using hc
    let start : Result := ⟨some d.main, d.initialState,
      (List.replicate d.stackCount []).set d.inputStack
        (bits.map (inputBit d.falseSymbol d.trueSymbol))⟩
    have hs : buildStart d bits = some start := by simp [buildStart,hdata,start]
    have hin : buildRaw (c.1.2.2,bits) = some (resultRaw start) := by
      rw [← inputRaw_ofRaw c.1.2.2,buildRaw_eq,hs]
      rfl
    have he : (runEncoded ((c.1.1,(bits.length+2)^c.1.2.1), resultRaw start)).bind
        (fun v => if v.1 then extractMemory (c.2.1,c.2.2.1,c.2.2.2,v.2.1,v.2.2.2) else none) = some output := by
      simpa [Evaluator.evaluate,hv,hin] using heval
    rw [runEncoded_of_decode c.1.1 p _ start hpdecode] at he
    cases hr : run p ((bits.length+2)^c.1.2.1) start with
    | invalid => simp [hr,outcomeRaw] at he
    | timeout r => simp [hr,outcomeRaw] at he
    | halted r =>
      have hout : extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.label,r.memory) = some output := by
        simpa [hr,outcomeRaw,resultRaw] using he
      have hmain : d.main < p.length := by
        by_contra hmain
        have hn : p[d.main]? = none := List.getElem?_eq_none (by omega)
        cases hf : (bits.length+2)^c.1.2.1 with
        | zero => simp [hf,run,start] at hr
        | succ n => simp [hf,run,start,hn] at hr
      exact ⟨p,rfl,hdata,hmain,hp,start,r,hs,hr,hout⟩

/-- Exact polynomial charged to the complete input, execution and output
path of a fixed candidate. -/
noncomputable def timePolynomial (stackCount exponent : Nat) (p : Program) : Polynomial Nat :=
  let n := Polynomial.X
  let clock := (n + Polynomial.C 2)^exponent
  let bound := n + clock * Polynomial.C (programDepth p)
  Polynomial.C 1 + (Polynomial.C 2*n + Polynomial.C 2 + clock) +
    (Polynomial.C 2*bound + Polynomial.C 2 +
      Polynomial.C (stackCount+1)*(bound+Polynomial.C 1)+Polynomial.C 1)

theorem timePolynomial_eval (stackCount exponent : Nat) (p : Program) (n : Nat) :
    (timePolynomial stackCount exponent p).eval n =
      1+(2*n+2+(n+2)^exponent)+
        (2*(n+(n+2)^exponent*programDepth p)+2+
          (stackCount+1)*(n+(n+2)^exponent*programDepth p+1)+1) := by
  simp [timePolynomial]

/-- Successful evaluation is reproduced by the same finite TM2 within the
explicit polynomial in the length of the supplied encoded input. -/
theorem successful_whole_run (c : Shared.Codes.TM2Candidate.Candidate) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p) (bits output : List Bool)
    (heval : Evaluator.evaluate c bits = some output) :
    let d := inputDataOfRaw c.1.2.2
    let w := Shared.ComplexityBridge.TM2BitstringWhole.machine d.stackCount d.states d.symbols p
      d.inputStack c.2.2.2 d.main d.initialState d.falseSymbol d.trueSymbol c.2.2.1
    ∃ t ≤ (timePolynomial d.stackCount c.1.2.1 p).eval bits.length,
      runSteps w.step t (Turing.initList w bits) = some (Turing.haltList w output) := by
  let d := inputDataOfRaw c.1.2.2
  obtain ⟨p',hd,hdata,hmain,hp,start,r,hs,hr,ho⟩ := successful_numeric_result c bits output heval
  have heq : p' = p := Option.some.inj (hd.symm.trans hdecode)
  subst p'
  obtain ⟨t,ht,htm⟩ := Shared.ComplexityBridge.TM2BitstringWhole.run_to_halt d p c.2.2.2
    c.2.1 c.2.2.1 bits ((bits.length+2)^c.1.2.1) start r output hdata hmain hp hs hr ho
  refine ⟨t,?_,htm⟩
  simpa [timePolynomial_eval] using ht

/-- The fixed whole machine has the canonical Boolean boundary alphabets. -/
def wholeAux (c : Shared.Codes.TM2Candidate.Candidate) (p : Program) : Turing.TM2ComputableAux Bool Bool where
  tm := let d := inputDataOfRaw c.1.2.2
    Shared.ComplexityBridge.TM2BitstringWhole.machine d.stackCount d.states d.symbols p
      d.inputStack c.2.2.2 d.main d.initialState d.falseSymbol d.trueSymbol c.2.2.1
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

/-- A uniformly successful fixed candidate computes the function in the
public complexity definition, for arbitrary encoded types. -/
theorem total_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (c : Shared.Codes.TM2Candidate.Candidate) (f : α → β)
    (h : ∀ a, Evaluator.evaluate c (BitstringEncoding.bitEncode a) =
      some (BitstringEncoding.bitEncode (f a))) : ComplexityTheory.IsPolyTime f := by
  classical
  by_cases hex : Nonempty α
  · obtain ⟨a⟩ := hex
    obtain ⟨p,hdecode,_⟩ := successful_numeric_result c _ _ (h a)
    let d := inputDataOfRaw c.1.2.2
    let w := wholeAux c p
    refine ⟨{ toTM2ComputableAux := w, time := timePolynomial d.stackCount c.1.2.1 p, outputsFun := ?_ }⟩
    intro x
    have hrun := successful_whole_run c p hdecode (BitstringEncoding.bitEncode x)
      (BitstringEncoding.bitEncode (f x)) (h x)
    let n := Classical.choose hrun
    have hn := Classical.choose_spec hrun
    refine ⟨⟨n,?_⟩,hn.1⟩
    have hr := hn.2
    rw [runSteps_iterate] at hr
    change (fun o => o.bind w.tm.step)^[n]
      (some (Turing.initList w.tm ((BitstringEncoding.bitEncode x).map id))) =
        some (Turing.haltList w.tm ((BitstringEncoding.bitEncode (f x)).map id))
    rw [List.map_id, List.map_id]
    exact hr
  · let w := wholeAux c []
    refine ⟨{ toTM2ComputableAux := w, time := 0, outputsFun := ?_ }⟩
    intro x
    exact (hex ⟨x⟩).elim

/-- Characterization of the public polynomial-time function class by the
executable fixed-candidate bitstring evaluator. -/
theorem candidate_iff_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) :
    (∃ c, ∀ a, Evaluator.evaluate c (BitstringEncoding.bitEncode a) =
      some (BitstringEncoding.bitEncode (f a))) ↔ ComplexityTheory.IsPolyTime f := by
  constructor
  · rintro ⟨c,h⟩; exact total_isPolyTime c f h
  · intro hf
    obtain ⟨c,_,h⟩ := Evaluator.canonicalPoly_covers f hf
    exact ⟨c,h⟩

end Shared.ComplexityBridge.TM2BitstringPoly
