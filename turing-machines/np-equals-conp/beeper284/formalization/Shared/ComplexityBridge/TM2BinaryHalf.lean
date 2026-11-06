import Shared.ComplexityBridge.CNFBinaryIndex

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Binary division by two on the pinned little-endian natural encoding. -/
namespace Shared.ComplexityBridge.TM2BinaryHalf
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Stack := Shared.ComplexityBridge.CNFBinaryIndex.Stack
inductive Label where | skip | scan | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.skip,.scan,.restore] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .skip => .pop .input (fun _ h => h) (.goto (fun _ => .scan))
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .output (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .skip
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,Shared.ComplexityBridge.CNFBinaryIndex.stackVals input scratch output⟩

theorem skip_step (input : List Bool) :
    machine.step (cfg .skip none input [] []) = some (cfg .scan input.head? input.tail [] []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryIndex.stackVals,Function.update]

theorem scan_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .scan v (b::input) scratch output) = some (cfg .scan (some b) input (b::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryIndex.stackVals,Function.update]

theorem scan_nil (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .scan v [] scratch output) = some (cfg .restore none [] scratch output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryIndex.stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (scratch output : List Bool) :
    machine.step (cfg .restore v [] (b::scratch) output) = some (cfg .restore (some b) [] scratch (b::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryIndex.stackVals,Function.update]

theorem restore_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .restore v [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.CNFBinaryIndex.stackVals,Function.update,Turing.haltList,machine]

theorem scan_run (input scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (input.length+1) (cfg .scan v input scratch output) =
      some (cfg .restore none [] (input.reverse++scratch) output) := by
  induction input generalizing scratch v with
  | nil => exact scan_nil v scratch output
  | cons b input ih =>
    rw [List.length_cons,show input.length+1+1 = (input.length+1)+1 by omega,runSteps_front,scan_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact restore_nil v output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .skip none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,cfg,Shared.ComplexityBridge.CNFBinaryIndex.stackVals,Turing.initList]

theorem run_bits (input : List Bool) :
    runSteps machine.step (2*input.tail.length+3) (Turing.initList machine input) =
      some (Turing.haltList machine input.tail) := by
  have hs := scan_run input.tail [] [] input.head?
  simp only [List.append_nil] at hs
  have hr := restore_run input.tail.reverse [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  rw [initial_eq,show 2*input.tail.length+3 = 1+((input.tail.length+1)+(input.tail.length+1)) by omega,
    Nat.add_comm 1 _,runSteps_front,skip_step]
  change runSteps machine.step ((input.tail.length+1)+(input.tail.length+1)) _ = _
  rw [runSteps_add,hs]
  exact hr

noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Nat → List Bool) (BitstringEncoding.bitEncode : Nat → List Bool) Nat.div2 where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 3
  outputsFun n := by
    have he : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
    have ho : BitstringEncoding.bitEncode n.div2 = n.bits.tail := by
      change Computability.encodeNat n.div2 = n.bits.tail
      rw [Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits,Nat.div2_bits_eq_tail]
    let t := 2*n.bits.tail.length+3
    refine ⟨⟨t,?_⟩,?_⟩
    · have hr := run_bits n.bits
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode n).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode n.div2).map id))
      rw [he,ho,List.map_id,List.map_id]
      exact hr
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,he]
      have hh : n.bits.tail.length ≤ n.bits.length := by
        cases h : n.bits with
        | nil => simp
        | cons b bs => simp
      dsimp [t]; omega

theorem div2_isPolyTime : ComplexityTheory.IsPolyTime Nat.div2 := ⟨timeMachine⟩
namespace Fixtures
example : Nat.div2 0 = 0 := rfl
example : Nat.div2 7 = 3 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BinaryHalf
