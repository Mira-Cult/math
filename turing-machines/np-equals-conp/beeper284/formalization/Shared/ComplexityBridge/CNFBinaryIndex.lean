import Shared.ComplexityBridge.CNFBinaryIncrement
import Shared.ComplexityBridge.CNFDisjunction
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

/-! Finite binary TM2 implementations of the even-variable and odd-selector
index maps used by CNF disjunction. -/
namespace Shared.ComplexityBridge.CNFBinaryIndex
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | scratch | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
inductive Label where | start | scan | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.start,.scan,.restore] (by intro l; cases l <;> simp)

def program (odd : Bool) : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .start => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan)))
        (if odd then .push .output (fun _ => true) (.load (fun _ => none) .halt)
         else .load (fun _ => none) .halt))
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.push .output (fun _ => odd) (.load (fun _ => none) .halt)))

def machine (odd : Bool) : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .start
  σ := Option Bool
  initialState := none
  m := program odd

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (odd : Bool) (l : Label) (v : Option Bool) (input scratch output : List Bool) : (machine odd).Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem start_cons (odd : Bool) (v : Option Bool) (b : Bool) (bits scratch out : List Bool) :
    (machine odd).step (cfg odd .start v (b::bits) scratch out) =
      some (cfg odd .scan (some b) bits (b::scratch) out) := by
  change some (Cfg.mk (some Label.scan) (some b)
    (Function.update (Function.update (stackVals (b::bits) scratch out) .input bits) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_cons (odd : Bool) (v : Option Bool) (b : Bool) (bits scratch out : List Bool) :
    (machine odd).step (cfg odd .scan v (b::bits) scratch out) =
      some (cfg odd .scan (some b) bits (b::scratch) out) := by
  change some (Cfg.mk (some Label.scan) (some b)
    (Function.update (Function.update (stackVals (b::bits) scratch out) .input bits) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_empty (odd : Bool) (v : Option Bool) (scratch out : List Bool) :
    (machine odd).step (cfg odd .scan v [] scratch out) = some (cfg odd .restore none [] scratch out) := by
  change some (Cfg.mk (some Label.restore) (none : Option Bool) (Function.update (stackVals [] scratch out) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (odd : Bool) (v : Option Bool) (b : Bool) (scratch out : List Bool) :
    (machine odd).step (cfg odd .restore v [] (b::scratch) out) =
      some (cfg odd .restore (some b) [] scratch (b::out)) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals [] (b::scratch) out) .scratch scratch) .output (b::out))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_empty (odd : Bool) (v : Option Bool) (out : List Bool) :
    (machine odd).step (cfg odd .restore v [] [] out) = some (Turing.haltList (machine odd) (odd::out)) := by
  change some (Cfg.mk (none : Option Label) (none : Option Bool)
    (Function.update (Function.update (stackVals [] [] out) .scratch []) .output (odd::out))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,machine]

theorem start_empty (odd : Bool) :
    (machine odd).step (cfg odd .start none [] [] []) =
      some (Turing.haltList (machine odd) (if odd then [true] else [])) := by
  cases odd <;> simp [machine,program,cfg,stackVals,Turing.TM2.step,Turing.TM2.stepAux,Turing.haltList,Function.update]
  all_goals funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_run (odd : Bool) (bits scratch out : List Bool) (v : Option Bool) :
    runSteps (machine odd).step (bits.length+1) (cfg odd .scan v bits scratch out) =
      some (cfg odd .restore none [] (bits.reverse++scratch) out) := by
  induction bits generalizing scratch v with
  | nil => exact scan_empty odd v scratch out
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,scan_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (odd : Bool) (scratch out : List Bool) (v : Option Bool) :
    runSteps (machine odd).step (scratch.length+1) (cfg odd .restore v [] scratch out) =
      some (Turing.haltList (machine odd) (odd::(scratch.reverse++out))) := by
  induction scratch generalizing out v with
  | nil => exact restore_empty odd v out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::out) (some b)

theorem initial_eq (odd : Bool) (bits : List Bool) :
    Turing.initList (machine odd) bits = cfg odd .start none bits [] [] := by
  change Cfg.mk (some Label.start) none _ = Cfg.mk (some Label.start) none (stackVals bits [] [])
  congr 1; funext k; cases k <;> simp [machine,stackVals]

/-- From the actual initial stack, the finite table handles all nonempty raw
    bitlists, restoring their order and prefixing the chosen low bit. -/
theorem run_nonempty (odd b : Bool) (bits : List Bool) :
    runSteps (machine odd).step (2*(bits.length+1)+2) (Turing.initList (machine odd) (b::bits)) =
      some (Turing.haltList (machine odd) (odd::b::bits)) := by
  have hs := scan_run odd bits [b] [] (some b)
  have hr := restore_run odd (bits.reverse++[b]) [] none
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_nil,
    List.reverse_reverse,List.length_append,List.length_reverse,List.length_cons,List.length_nil] at hr
  rw [initial_eq]
  have hn : 2*(bits.length+1)+2 = ((bits.length+1)+(bits.length+2))+1 := by omega
  rw [hn,runSteps_front,start_cons]
  simp only [Option.bind_some]
  rw [runSteps_add,hs]
  simpa [Nat.add_assoc] using hr

theorem run_empty (odd : Bool) :
    runSteps (machine odd).step 1 (Turing.initList (machine odd) []) =
      some (Turing.haltList (machine odd) (if odd then [true] else [])) := by
  rw [initial_eq]
  simpa [runSteps] using start_empty odd

/-- The input and output are the canonical little-endian natural encodings;
    the zero case avoids inventing a leading zero. -/
theorem run_encoded (odd : Bool) (n : Nat) :
    ∃ steps ≤ 2*n.bits.length+2,
      runSteps (machine odd).step steps (Turing.initList (machine odd) n.bits) =
        some (Turing.haltList (machine odd) (BitstringEncoding.bitEncode (2*n+if odd then 1 else 0))) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1,by simp,?_⟩
    have he : BitstringEncoding.bitEncode (2*0+if odd then 1 else 0) =
        (if odd then [true] else []) := by cases odd <;> rfl
    rw [he]
    exact run_empty odd
  · have hbits : n.bits ≠ [] := by
      rw [Shared.ComplexityBridge.CNFEncodingComputability.bits_unfold n hn]
      simp
    cases hb : n.bits with
    | nil => contradiction
    | cons b bits =>
      refine ⟨2*(bits.length+1)+2,?_,?_⟩
      · simp only [List.length_cons]; omega
      · have hr := run_nonempty odd b bits
        have he : BitstringEncoding.bitEncode (2*n+if odd then 1 else 0) = odd::n.bits := by
          change Computability.encodeNat (2*n+if odd then 1 else 0) = _
          rw [Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits]
          cases odd <;> simp [Nat.bit0_bits n hn,Nat.bit1_bits]
        simpa [hb,he] using hr

/-- Each map is polynomial-time under the public natural-number encoding. -/
noncomputable def timeMachine (odd : Bool) : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Nat → List Bool)
    (BitstringEncoding.bitEncode : Nat → List Bool) (fun n => 2*n+if odd then 1 else 0) where
  tm := machine odd
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun n := by
    let run := run_encoded odd n
    let steps := Classical.choose run
    have h := Classical.choose_spec run
    refine ⟨⟨steps,?_⟩,?_⟩
    · have hr := h.2
      rw [runSteps_iterate] at hr
      have he : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
      change (fun o => o.bind (machine odd).step)^[steps]
        (some (Turing.initList (machine odd) ((BitstringEncoding.bitEncode n).map id))) =
        some (Turing.haltList (machine odd) ((BitstringEncoding.bitEncode (2*n+if odd then 1 else 0)).map id))
      rw [List.map_id,List.map_id,he]
      exact hr
    · have he : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,he]
      exact h.1

theorem double_isPolyTime : ComplexityTheory.IsPolyTime (fun n : Nat => 2*n) := by
  simpa using (show ComplexityTheory.IsPolyTime (fun n : Nat => 2*n+if false then 1 else 0) from ⟨timeMachine false⟩)

theorem selector_isPolyTime : ComplexityTheory.IsPolyTime Shared.ComplexityBridge.CNFDisjunction.selector := by
  change ComplexityTheory.IsPolyTime (fun n : Nat => 2*n+1)
  exact ⟨timeMachine true⟩

namespace Fixtures
example : runSteps (machine false).step 1 (Turing.initList (machine false) []) =
    some (Turing.haltList (machine false) []) := run_empty false
example : runSteps (machine true).step 1 (Turing.initList (machine true) []) =
    some (Turing.haltList (machine true) [true]) := run_empty true
example : runSteps (machine false).step 8 (Turing.initList (machine false) [true,true,true]) =
    some (Turing.haltList (machine false) [false,true,true,true]) := by
  simpa using run_nonempty false true [true,true]
example : (2*0+1 : Nat).bits = [true] := by decide
example : (2*3 : Nat).bits = [false,true,true] := by decide
end Fixtures
end Shared.ComplexityBridge.CNFBinaryIndex
