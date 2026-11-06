import Shared.ComplexityBridge.CNFBinaryPairAdd

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A finite TM2 builds a literal's canonical `(Nat × Bool)` encoding from
its canonical natural-number variable index and a fixed polarity. -/
namespace Shared.ComplexityBridge.CNFLiteralConstructor
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | scan | restore deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scan,.restore] (by intro l; cases l <;> simp)

def program (sign : Bool) : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun _ => true)
          (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan))))
        (.push .output (fun _ => sign)
          (.push .output (fun _ => false) (.goto (fun _ => .restore)))))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => none) .halt))

def machine (sign : Bool) : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := Option Bool
  initialState := none
  m := program sign

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (sign : Bool) (l : Label) (v : Option Bool) (input scratch output : List Bool) : (machine sign).Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem scan_cons (sign : Bool) (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    (machine sign).step (cfg sign .scan v (b::input) scratch output) =
      some (cfg sign .scan (some b) input (b::true::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_nil (sign : Bool) (v : Option Bool) (scratch output : List Bool) :
    (machine sign).step (cfg sign .scan v [] scratch output) =
      some (cfg sign .restore none [] scratch (false::sign::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (sign : Bool) (v : Option Bool) (b : Bool) (scratch output : List Bool) :
    (machine sign).step (cfg sign .restore v [] (b::scratch) output) =
      some (cfg sign .restore (some b) [] scratch (b::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (sign : Bool) (v : Option Bool) (output : List Bool) :
    (machine sign).step (cfg sign .restore v [] [] output) = some (Turing.haltList (machine sign) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

def framedBits (bits : List Bool) : List Bool := bits.flatMap (fun b => [true,b])

theorem prefix_length (bits : List Bool) : (framedBits bits).length = 2*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [framedBits,ih]; omega

theorem delimit_prefix (bits : List Bool) : BitstringEncoding.delimit bits = framedBits bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [BitstringEncoding.delimit,framedBits,ih]

theorem scan_run (sign : Bool) (bits scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps (machine sign).step bits.length (cfg sign .scan v bits scratch output) =
      some (cfg sign .scan v' [] ((framedBits bits).reverse++scratch) output) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by simp [framedBits,runSteps]⟩
  | cons b bits ih =>
    obtain ⟨v',hr⟩ := ih (b::true::scratch) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,scan_cons]
    simpa [framedBits,List.reverse_cons,List.append_assoc] using hr

theorem restore_run (sign : Bool) (scratch output : List Bool) (v : Option Bool) :
    runSteps (machine sign).step (scratch.length+1) (cfg sign .restore v [] scratch output) =
      some (Turing.haltList (machine sign) (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact restore_nil sign v output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (sign : Bool) (bits : List Bool) :
    Turing.initList (machine sign) bits = cfg sign .scan none bits [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

theorem run (sign : Bool) (bits : List Bool) :
    runSteps (machine sign).step (3*bits.length+2) (Turing.initList (machine sign) bits) =
      some (Turing.haltList (machine sign) (BitstringEncoding.delimit bits ++ [sign])) := by
  obtain ⟨v,hs⟩ := scan_run sign bits [] [] none
  simp only [List.append_nil] at hs
  have hr := restore_run sign (framedBits bits).reverse [false,sign] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_assoc] at hr
  rw [prefix_length] at hr
  have hn : 3*bits.length+2 = bits.length+((2*bits.length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hs]
  change runSteps (machine sign).step ((2*bits.length+1)+1) (cfg sign .scan v [] (framedBits bits).reverse []) = _
  rw [runSteps_front,scan_nil]
  simpa [delimit_prefix,List.append_assoc] using hr

def literal (sign : Bool) (n : Nat) : Shared.ComplexityBridge.CNF.Literal := (n,sign)

theorem literal_encoding (sign : Bool) (n : Nat) :
    BitstringEncoding.bitEncode (literal sign n) = BitstringEncoding.delimit n.bits ++ [sign] := by
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode n) ++ BitstringEncoding.bitEncode sign = _
  have he : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
  rw [he]
  rfl

noncomputable def timeMachine (sign : Bool) : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Nat → List Bool)
    (BitstringEncoding.bitEncode : Shared.ComplexityBridge.CNF.Literal → List Bool) (literal sign) where
  tm := machine sign
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 2
  outputsFun n := by
    refine ⟨⟨3*n.bits.length+2,?_⟩,?_⟩
    · have hr := run sign n.bits
      rw [runSteps_iterate] at hr
      have hi : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
      change (fun o => o.bind (machine sign).step)^[3*n.bits.length+2]
        (some (Turing.initList (machine sign) ((BitstringEncoding.bitEncode n).map id))) =
        some (Turing.haltList (machine sign) ((BitstringEncoding.bitEncode (literal sign n)).map id))
      simpa [hi,literal_encoding] using hr
    · have hi : BitstringEncoding.bitEncode n = n.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
      simp [hi]

theorem literal_isPolyTime (sign : Bool) : ComplexityTheory.IsPolyTime (literal sign) := ⟨timeMachine sign⟩

/-- A selector literal appearing in `choices` has a finite polynomial-time
implementation under the pinned pair, numeral, and literal encodings. -/
theorem choice_literal_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Nat => (Shared.ComplexityBridge.CNFDisjunction.selector (p.1+p.2),true)) := by
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (fun p : Nat × Nat => Shared.ComplexityBridge.CNFDisjunction.selector (p.1+p.2))
    (literal true) Shared.ComplexityBridge.CNFBinaryPairAdd.selector_add_isPolyTime
    (literal_isPolyTime true)

/-- The leading negative selector literal in each guarded clause. -/
theorem guard_literal_isPolyTime : ComplexityTheory.IsPolyTime
    (fun i : Nat => (Shared.ComplexityBridge.CNFDisjunction.selector i,false)) := by
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    Shared.ComplexityBridge.CNFDisjunction.selector (literal false)
    Shared.ComplexityBridge.CNFBinaryIndex.selector_isPolyTime (literal_isPolyTime false)

/-- The indexed literal is exactly the entry emitted by the existing CNF
choice-clause definition. -/
theorem choice_lookup (start count i : Nat) (h : i < count) :
    (Shared.ComplexityBridge.CNFDisjunction.choices start count)[i]? =
      some (Shared.ComplexityBridge.CNFDisjunction.selector (start+i),true) := by
  simp [Shared.ComplexityBridge.CNFDisjunction.choices,h]

namespace Fixtures
example : runSteps (machine true).step 2 (Turing.initList (machine true) []) =
    some (Turing.haltList (machine true) [false,true]) := by
  simpa [BitstringEncoding.delimit] using run true []
example : runSteps (machine false).step 8 (Turing.initList (machine false) [true,false]) =
    some (Turing.haltList (machine false) [true,true,true,false,false,false]) := by
  simpa [BitstringEncoding.delimit] using run false [true,false]
end Fixtures

end Shared.ComplexityBridge.CNFLiteralConstructor
