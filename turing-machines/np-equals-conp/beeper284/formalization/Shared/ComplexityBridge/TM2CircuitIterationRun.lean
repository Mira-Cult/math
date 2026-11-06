import Shared.ComplexityBridge.TM2CircuitIterationSize

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-! A canonical polynomial clock for the finite circuit-unrolling fold.
The empty auxiliary list makes the fold boundary's framed initial state
exactly match the input parser's representation. -/
namespace Shared.ComplexityBridge.TM2CircuitIterationRun
open Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2CircuitIteration
open Shared.ComplexityBridge.TM2CircuitIterationSize
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program
open TM2FoldIO

abbrev Wrapped := Work × List Bool

def wrappedStep (p : Wrapped × Bool) : Wrapped := (advance p.1.1,[])

theorem wrappedStep_isPolyTime : ComplexityTheory.IsPolyTime wrappedStep := by
  let wrapped : Wrapped × Bool → Wrapped := fun p => p.1
  let work : Wrapped × Bool → Work := fun p => p.1.1
  let next : Wrapped × Bool → Work := fun p => advance (work p)
  let empty : Wrapped × Bool → List Bool := fun _ => []
  have hw : ComplexityTheory.IsPolyTime wrapped := TM2PairFirst.first_isPolyTime
  have hf : ComplexityTheory.IsPolyTime work := TM2Compose.isPolyTime_comp wrapped (fun p : Wrapped => p.1) hw TM2PairFirst.first_isPolyTime
  have hn : ComplexityTheory.IsPolyTime next := TM2Compose.isPolyTime_comp work advance hf advance_isPolyTime
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have h := TM2GuardAllStep.pair_isPolyTime next empty hn he
  change ComplexityTheory.IsPolyTime wrappedStep at h
  exact h

theorem wrapped_fold (w : Work) (xs : List Bool) :
    TM2PolynomialFold.fold wrappedStep (w,[]) xs = (TM2PolynomialFold.fold step w xs,[]) := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih =>
    change TM2PolynomialFold.fold wrappedStep (advance w,[]) xs =
      (TM2PolynomialFold.fold step (advance w) xs,[])
    exact ih (advance w)

theorem prefix_size (w : Work) (xs pref tail : List Bool) (b : Bool) (hs : xs = pref++b::tail) :
    (BitstringEncoding.bitEncode (TM2PolynomialFold.fold wrappedStep (w,[]) pref)).length ≤
      200*((BitstringEncoding.bitEncode (w,xs)).length+1)^4+1 := by
  let N := (BitstringEncoding.bitEncode (w,xs)).length
  have hp : (BitstringEncoding.bitEncode (w,pref)).length ≤ N := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode w)++BitstringEncoding.bitEncode pref).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode w)++BitstringEncoding.bitEncode xs).length
    rw [hs,TM2ListAppend.list_encoding_append]
    simp only [List.length_append]
    omega
  have h := fold_state_size w pref
  have hm : ((BitstringEncoding.bitEncode (w,pref)).length+1)^4 ≤ (N+1)^4 :=
    Nat.pow_le_pow_left (by omega) 4
  rw [wrapped_fold,pair_encoding_length]
  dsimp only [Prod.fst,Prod.snd]
  have he : (BitstringEncoding.bitEncode ([] : List Bool)).length = 0 := rfl
  rw [he]
  dsimp [N] at hm
  omega

theorem bounded_step :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ B : Polynomial Nat,
      ∀ (w : Work) (xs pref : List Bool) (b : Bool) (tail : List Bool), xs = pref++b::tail →
        let state := TM2PolynomialFold.fold wrappedStep (w,[]) pref
        let size := B.eval (BitstringEncoding.bitEncode (w,xs)).length
        ∃ n ≤ size,
          runSteps core.tm.step n
            (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,b)).map core.inputAlphabet.symm)) =
            some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (wrappedStep (state,b))).map core.outputAlphabet.symm)) ∧
          (BitstringEncoding.bitEncode state).length ≤ size ∧
          (BitstringEncoding.bitEncode b).length ≤ size ∧
          (BitstringEncoding.bitEncode (state,b)).length ≤ size ∧
          (BitstringEncoding.bitEncode (wrappedStep (state,b))).length ≤ size := by
  obtain ⟨r,hr⟩ := TM2MapSizeBounds.output_length_poly wrappedStep wrappedStep_isPolyTime
  obtain ⟨core⟩ := wrappedStep_isPolyTime
  let Q : Polynomial Nat := Polynomial.C 400*(Polynomial.X+Polynomial.C 1)^4+Polynomial.C 4
  let B : Polynomial Nat := Q+core.time.comp Q+r.comp Q
  refine ⟨core.toTM2ComputableAux,B,?_⟩
  intro w xs pref b tail hsplit
  let N := (BitstringEncoding.bitEncode (w,xs)).length
  let state := TM2PolynomialFold.fold wrappedStep (w,[]) pref
  have hstate := prefix_size w xs pref tail b hsplit
  have hpair : (BitstringEncoding.bitEncode (state,b)).length ≤ Q.eval N := by
    rw [pair_encoding_length,bool_encoding_length]
    simp only [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    dsimp [state,N] at *
    omega
  have hout : (BitstringEncoding.bitEncode (wrappedStep (state,b))).length ≤ r.eval (Q.eval N) :=
    le_trans (hr (state,b)) (TM2Compose.polynomial_eval_mono r hpair)
  let run := core.outputsFun (state,b)
  have htime : run.steps ≤ core.time.eval (Q.eval N) :=
    le_trans run.steps_le_m (TM2Compose.polynomial_eval_mono core.time hpair)
  have hB : B.eval N = Q.eval N+core.time.eval (Q.eval N)+r.eval (Q.eval N) := by
    simp [B,Polynomial.eval_add,Polynomial.eval_comp]
  change ∃ n ≤ B.eval N, runSteps core.tm.step n
    (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,b)).map core.inputAlphabet.symm)) =
    some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (wrappedStep (state,b))).map core.outputAlphabet.symm)) ∧ _
  refine ⟨run.steps,?_,?_,?_,?_,?_,?_⟩
  · rw [hB]; omega
  · rw [runSteps_iterate]; exact run.evals_in_steps
  · change (BitstringEncoding.bitEncode state).length ≤ B.eval N
    rw [hB]
    have hh := bool_encoding_length b
    rw [pair_encoding_length,hh] at hpair
    dsimp only [Prod.fst,Prod.snd] at hpair
    omega
  · change (BitstringEncoding.bitEncode b).length ≤ B.eval N
    rw [hB]
    have hh := bool_encoding_length b
    rw [pair_encoding_length,hh] at hpair
    dsimp only [Prod.fst,Prod.snd] at hpair
    omega
  · change (BitstringEncoding.bitEncode (state,b)).length ≤ B.eval N
    rw [hB]; omega
  · change (BitstringEncoding.bitEncode (wrappedStep (state,b))).length ≤ B.eval N
    rw [hB]; omega

theorem loop_done :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (w : Work) (xs : List Bool), ∃ t ≤ P.eval (BitstringEncoding.bitEncode (w,xs)).length,
        runSteps (TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
            (TM2ContextMapCall.srcEmbed core.tm
              (TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (w,([] : List Bool))) [] [] [] [] (BitstringEncoding.bitEncode xs))
              (Turing.initList core.tm []).stk)) =
        some (TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
          (TM2ContextMapCall.srcEmbed core.tm
            (TM2ContextMapSplit.cfg (.inr .done) none
              (BitstringEncoding.bitEncode (TM2PolynomialFold.fold step w xs,([] : List Bool))) [] [] [] [] [])
            (Turing.initList core.tm []).stk)) := by
  obtain ⟨core,B,hB⟩ := bounded_step
  let P : Polynomial Nat := Polynomial.X*(Polynomial.C 16*B+Polynomial.C 16)+Polynomial.C 1
  refine ⟨core,P,?_⟩
  intro w xs
  let N := (BitstringEncoding.bitEncode (w,xs)).length
  obtain ⟨t,ht,hr⟩ := TM2PolynomialFold.loop_done wrappedStep core (w,([] : List Bool)) xs (B.eval N) (hB w xs)
  have hc : xs.length ≤ N := by
    have hh := CNF.list_length_le_bitEncode xs
    change xs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode w)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append]; omega
  have hm := Nat.mul_le_mul_right (16*B.eval N+16) hc
  refine ⟨t,?_,?_⟩
  · change t ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  · simpa [wrapped_fold] using hr

def foldResult (p : Work × List Bool) : Wrapped := (TM2PolynomialFold.fold step p.1 p.2,[])

/-- Complete finite run with initial parsing and final stack cleanup charged. -/
theorem fold_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (w : Work) (xs : List Bool),
      ∃ t ≤ P.eval (BitstringEncoding.bitEncode (w,xs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.bitEncode (w,xs))) =
        some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
          (BitstringEncoding.bitEncode (foldResult (w,xs)))) := by
  obtain ⟨core,p,hp⟩ := loop_done
  let q : Polynomial Nat := Polynomial.C 100*(Polynomial.X+Polynomial.C 1)^4
  let P : Polynomial Nat := p+Polynomial.C 4*q+Polynomial.C 4*Polynomial.X+Polynomial.C 8
  refine ⟨core,P,?_⟩
  intro w xs
  let bits := BitstringEncoding.bitEncode w
  let tail := BitstringEncoding.bitEncode xs
  let result := BitstringEncoding.bitEncode (foldResult (w,xs))
  let N := (BitstringEncoding.bitEncode (w,xs)).length
  obtain ⟨n,hn,hr⟩ := hp w xs
  let start := TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (TM2ContextMapCall.srcEmbed core.tm
      (TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.delimit bits) [] [] [] [] tail)
      (Turing.initList core.tm []).stk)
  let finish := TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (TM2ContextMapCall.srcEmbed core.tm
      (TM2ContextMapSplit.cfg (.inr .done) none result [] [] [] [] [])
      (Turing.initList core.tm []).stk)
  have he : BitstringEncoding.bitEncode (w,([] : List Bool)) = BitstringEncoding.delimit (BitstringEncoding.bitEncode w) := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode w) ++ [] = _
    simp
  rw [he] at hr
  change runSteps (Source core.tm core.inputAlphabet core.outputAlphabet).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := TM2UnaryTransfer.run_to_stable_lift
    (Source core.tm core.inputAlphabet core.outputAlphabet).step (machine core.tm core.inputAlphabet core.outputAlphabet).step
    (embed core.tm core.inputAlphabet core.outputAlphabet) (terminal core.tm core.inputAlphabet core.outputAlphabet)
    (stable core.tm core.inputAlphabet core.outputAlphabet) (core_step core.tm core.inputAlphabet core.outputAlphabet)
    n start finish (by rfl) hr
  have hbits : bits.length ≤ N := pair_first_size (w,xs)
  have hresult : result.length ≤ 2*q.eval N+1 := by
    have hh := fold_state_size w xs
    change (BitstringEncoding.bitEncode (TM2PolynomialFold.fold step w xs,([] : List Bool))).length ≤ _
    rw [pair_encoding_length]
    have he : (BitstringEncoding.bitEncode ([] : List Bool)).length = 0 := rfl
    rw [he]
    dsimp [q,N] at *
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
    omega
  refine ⟨(4*bits.length+3)+d+(2*result.length+3),?_,?_⟩
  · change (4*bits.length+3)+d+(2*result.length+3) ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    dsimp [N] at *
    omega
  · change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      ((4*bits.length+3)+d+(2*result.length+3))
      (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.delimit bits++tail)) = _
    rw [show (4*bits.length+3)+d+(2*result.length+3) =
      (4*bits.length+3)+(d+(2*result.length+3)) by omega,runSteps_add,load_run]
    change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      (d+(2*result.length+3)) (embed core.tm core.inputAlphabet core.outputAlphabet start) = _
    rw [runSteps_add,hs]
    exact cleanup_run core.tm core.inputAlphabet core.outputAlphabet result

theorem foldResult_isPolyTime : ComplexityTheory.IsPolyTime foldResult := by
  obtain ⟨core,p,hp⟩ := fold_run
  refine ⟨{
    tm := machine core.tm core.inputAlphabet core.outputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro z
  rcases z with ⟨w,xs⟩
  classical
  let t := Nat.find (hp w xs)
  have ht := (Nat.find_spec (hp w xs)).1
  have hr := (Nat.find_spec (hp w xs)).2
  refine ⟨⟨t,?_⟩,ht⟩
  rw [runSteps_iterate] at hr
  change (fun o => o.bind (machine core.tm core.inputAlphabet core.outputAlphabet).step)^[t]
    (some (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (w,xs)).map id))) =
    some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (foldResult (w,xs))).map id))
  simpa only [List.map_id] using hr

/-- The complete circuit-copy fold is canonical polynomial-time on every
encoded request, including malformed circuit values. -/
theorem fold_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Work × List Bool => TM2PolynomialFold.fold step p.1 p.2) := by
  have h := TM2Compose.isPolyTime_comp foldResult (fun p : Wrapped => p.1)
    foldResult_isPolyTime TM2PairFirst.first_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Work × List Bool => TM2PolynomialFold.fold step p.1 p.2) at h
  exact h

/-- The gate-list and reference-list outputs of the total fold. -/
def gatesWorker (p : Work × List Bool) : List CircuitCNF.Gate :=
  (TM2PolynomialFold.fold step p.1 p.2).2.2.2

def refsWorker (p : Work × List Bool) : List Nat :=
  (TM2PolynomialFold.fold step p.1 p.2).2.2.1

theorem workers_isPolyTime : ComplexityTheory.IsPolyTime gatesWorker ∧ ComplexityTheory.IsPolyTime refsWorker := by
  let run : Work × List Bool → Work := fun p => TM2PolynomialFold.fold step p.1 p.2
  let state : Work × List Bool → State := fun p => (run p).2
  let tail : Work × List Bool → List Nat × List CircuitCNF.Gate := fun p => (state p).2
  have hs : ComplexityTheory.IsPolyTime state := TM2Compose.isPolyTime_comp run (fun w : Work => w.2) fold_isPolyTime TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp state (fun s : State => s.2) hs TM2GuardAllStep.second_isPolyTime
  constructor
  · have h := TM2Compose.isPolyTime_comp tail (fun p : List Nat × List CircuitCNF.Gate => p.2) ht TM2GuardAllStep.second_isPolyTime
    exact h
  · have h := TM2Compose.isPolyTime_comp tail (fun p : List Nat × List CircuitCNF.Gate => p.1) ht TM2PairFirst.first_isPolyTime
    exact h

/-- Under the stated validity and output bounds, the workers return exactly
the existing unroller's gates and final references. -/
theorem workers_correct (tokens : List Bool) (gates : List CircuitCNF.Gate) (outputs : List Nat)
    (base : Nat) (inputs : List Nat) (clock : List Bool)
    (hv : CircuitCNF.validGates tokens.length gates)
    (ho : ∀ o ∈ outputs, o < tokens.length+gates.length) :
    gatesWorker ((((tokens,gates),outputs),(base,inputs,[])),clock) =
      CircuitRelocate.unroll tokens.length gates outputs base inputs clock.length ∧
    refsWorker ((((tokens,gates),outputs),(base,inputs,[])),clock) =
      CircuitRelocate.finalRefs tokens.length gates outputs base inputs clock.length := by
  have h := fold_correct tokens gates outputs (base,inputs,[]) hv ho clock
  constructor
  · change (TM2PolynomialFold.fold step (((tokens,gates),outputs),(base,inputs,[])) clock).2.2.2 = _
    rw [h]
    simpa using CircuitRelocateComputability.unroll_iterate (tokens.length,gates,outputs) (base,inputs,[]) clock.length
  · change (TM2PolynomialFold.fold step (((tokens,gates),outputs),(base,inputs,[])) clock).2.2.1 = _
    rw [h]
    exact CircuitRelocateComputability.finalRefs_iterate (tokens.length,gates,outputs) (base,inputs,[]) clock.length

end Shared.ComplexityBridge.TM2CircuitIterationRun
