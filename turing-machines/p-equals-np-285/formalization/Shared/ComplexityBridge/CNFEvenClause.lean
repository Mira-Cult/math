import Shared.ComplexityBridge.TM2ListUnaryLength
import Shared.ComplexityBridge.CNFChoiceEmitter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Finite-machine even renaming of CNF clause variables. On canonical
literals a nonzero binary numeral gains a low false bit; zero stays empty.
The machine transforms delimited literal blocks without decoding unbounded
natural numbers. -/
namespace Shared.ComplexityBridge.CNFEvenClause
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | head | first | bodyHead | bodyData | restore deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.head,.first,.bodyHead,.bodyData,.restore] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .head => .pop .input (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .first)) (.goto (fun _ => .restore)))
  | .first => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true)
          (.push .scratch (fun _ => true) (.push .scratch (fun _ => true)
            (.push .scratch (fun _ => true) (.push .scratch (fun _ => false)
              (.push .scratch (fun _ => true) (.push .scratch (fun _ => true)
                (.goto (fun _ => .bodyHead))))))))
          (.push .scratch (fun _ => true) (.push .scratch (fun _ => false) (.goto (fun _ => .bodyHead)))))
        (.goto (fun _ => .restore)))
  | .bodyHead => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true)
          (.push .scratch (fun _ => true) (.goto (fun _ => .bodyData)))
          (.push .scratch (fun _ => false) (.goto (fun _ => .head))))
        (.goto (fun _ => .restore)))
  | .bodyData => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .bodyHead)))
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
  main := .head
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem head_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .head v (b::input) scratch output) = some (cfg .first (some b) input scratch output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem head_nil (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .head v [] scratch output) = some (cfg .restore none [] scratch output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

def firstOut (b : Bool) : List Bool := if b then [true,true,true,false,true,true] else [true,false]

theorem first_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .first v (b::input) scratch output) =
      some (cfg .bodyHead (some b) input ((firstOut b).reverse++scratch) output) := by
  cases b <;> change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update,firstOut]

theorem body_true (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .bodyHead v (true::input) scratch output) =
      some (cfg .bodyData (some true) input (true::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem body_false (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .bodyHead v (false::input) scratch output) =
      some (cfg .head (some false) input (false::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .bodyData v (b::input) scratch output) =
      some (cfg .bodyHead (some b) input (b::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (scratch output : List Bool) :
    machine.step (cfg .restore v [] (b::scratch) output) =
      some (cfg .restore (some b) [] scratch (b::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .restore v [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

theorem body_run (bits tail scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (2*bits.length+1) (cfg .bodyHead v (BitstringEncoding.delimit bits++tail) scratch output) =
      some (cfg .head (some false) tail ((BitstringEncoding.delimit bits).reverse++scratch) output) := by
  induction bits generalizing scratch v with
  | nil => simpa [BitstringEncoding.delimit,runSteps] using body_false v tail scratch output
  | cons b bits ih =>
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(bits.length+1)+1 = (2*bits.length+1+1)+1 := by omega
    rw [hn,runSteps_front,body_true]
    change runSteps machine.step (2*bits.length+1+1) (cfg .bodyData (some true) (b::(BitstringEncoding.delimit bits++tail)) (true::scratch) output) = _
    rw [runSteps_front,data_cons]
    simpa [BitstringEncoding.delimit,List.reverse_cons,List.append_assoc] using ih (b::true::scratch) (some b)

def transformed (b : Bool) (bits : List Bool) : List Bool :=
  if b then true::false::true::bits else false::bits

theorem transformed_delimit (b : Bool) (bits : List Bool) :
    BitstringEncoding.delimit (transformed b bits) = firstOut b ++ BitstringEncoding.delimit bits := by
  cases b <;> rfl

theorem block_run (b : Bool) (bits tail scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (2*(bits.length+1)+1)
      (cfg .head v (BitstringEncoding.delimit (b::bits)++tail) scratch output) =
      some (cfg .head (some false) tail ((BitstringEncoding.delimit (transformed b bits)).reverse++scratch) output) := by
  simp only [BitstringEncoding.delimit,List.cons_append]
  have hn : 2*(bits.length+1)+1 = (2*bits.length+1+1)+1 := by omega
  rw [hn,runSteps_front,head_cons]
  change runSteps machine.step (2*bits.length+1+1) (cfg .first (some true) (b::(BitstringEncoding.delimit bits++tail)) scratch output) = _
  rw [runSteps_front,first_cons]
  simpa [transformed_delimit,List.reverse_append,List.append_assoc] using body_run bits tail ((firstOut b).reverse++scratch) output (some b)

/-- A literal's encoding is nonempty. The stream transformation is exactly
canonical even-variable renaming, including variable zero. -/
theorem literal_transform (n : Nat) (sign : Bool) :
    ∃ b bits, BitstringEncoding.bitEncode (n,sign) = b::bits ∧
      BitstringEncoding.bitEncode (evenLiteral (n,sign)) = transformed b bits := by
  have he (m : Nat) : BitstringEncoding.bitEncode (m,sign) =
      BitstringEncoding.delimit m.bits ++ [sign] := by
    change BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFLiteralConstructor.literal sign m) = _
    exact Shared.ComplexityBridge.CNFLiteralConstructor.literal_encoding sign m
  cases n with
  | zero =>
    refine ⟨false,[sign],?_,?_⟩
    · simpa [BitstringEncoding.delimit] using he 0
    · change BitstringEncoding.bitEncode (0,sign) = _
      simpa [transformed,BitstringEncoding.delimit] using he 0
  | succ n =>
    have hne : (n+1).bits ≠ [] := by
      intro h
      have hv := Shared.Codes.BinaryAdditionCanonical.value_bits (n+1)
      rw [h] at hv
      simp [Shared.Codes.BitNumeralCompare.value] at hv
    cases hb : (n+1).bits with
    | nil => exact False.elim (hne hb)
    | cons bit bits =>
      refine ⟨true,bit::(BitstringEncoding.delimit bits++[sign]),?_,?_⟩
      · rw [he,hb]; rfl
      · have hdouble : (2*(n+1)).bits = false::(n+1).bits := Nat.bit0_bits _ (by omega)
        change BitstringEncoding.bitEncode (2*(n+1),sign) = _
        rw [he,hdouble,hb]
        rfl

def transformPayload : List Bool → List Bool
  | [] => []
  | b::bits => transformed b bits

def framed (blocks : List (List Bool)) : List Bool := (blocks.map BitstringEncoding.delimit).flatten

theorem scan_blocks (blocks : List (List Bool)) (tail scratch output : List Bool) (v : Option Bool)
    (hne : ∀ b ∈ blocks, b ≠ []) :
    ∃ v', runSteps machine.step (framed blocks).length
      (cfg .head v (framed blocks++tail) scratch output) =
      some (cfg .head v' tail ((framed (blocks.map transformPayload)).reverse++scratch) output) := by
  induction blocks generalizing scratch v with
  | nil => exact ⟨v,by simp [framed,runSteps]⟩
  | cons block blocks ih =>
    have hn : block ≠ [] := hne block (by simp)
    cases block with
    | nil => contradiction
    | cons b bits =>
      have ht : ∀ x ∈ blocks, x ≠ [] := by intro x hx; exact hne x (by simp [hx])
      obtain ⟨v',hr⟩ := ih ((BitstringEncoding.delimit (transformed b bits)).reverse++scratch) (some false) ht
      refine ⟨v',?_⟩
      have hf : framed ((b::bits)::blocks) = BitstringEncoding.delimit (b::bits) ++ framed blocks := rfl
      have hl : (framed ((b::bits)::blocks)).length = (2*(bits.length+1)+1)+(framed blocks).length := by
        rw [hf,List.length_append,BitstringEncoding.length_delimit]; simp
      rw [hl,hf,List.append_assoc,runSteps_add,block_run]
      simpa [framed,transformPayload,List.reverse_append,List.append_assoc] using hr

theorem restore_run (scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact restore_nil v output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem transformed_frame_length (b : List Bool) :
    (BitstringEncoding.delimit (transformPayload b)).length ≤ (BitstringEncoding.delimit b).length+4 := by
  cases b with
  | nil => simp [transformPayload]
  | cons b bits => cases b <;> simp [transformPayload,transformed,BitstringEncoding.length_delimit] <;> omega

theorem framed_length_bound (blocks : List (List Bool)) :
    (framed (blocks.map transformPayload)).length ≤ 5*(framed blocks).length := by
  induction blocks with
  | nil => simp [framed]
  | cons b blocks ih =>
    have hb := transformed_frame_length b
    have hpos : 1 ≤ (BitstringEncoding.delimit b).length := by simp
    simp only [framed,List.map_cons,List.flatten_cons,List.length_append] at *
    omega

theorem literal_blocks_nonempty (c : Clause) :
    ∀ b ∈ c.map BitstringEncoding.bitEncode, b ≠ [] := by
  intro b hb
  obtain ⟨lit,_,rfl⟩ := List.mem_map.mp hb
  obtain ⟨n,s⟩ := lit
  obtain ⟨bit,rest,h,_⟩ := literal_transform n s
  rw [h]
  simp

theorem literal_blocks_correct (c : Clause) :
    framed ((c.map BitstringEncoding.bitEncode).map transformPayload) = BitstringEncoding.bitEncode (evenClause c) := by
  induction c with
  | nil => rfl
  | cons lit c ih =>
    obtain ⟨n,s⟩ := lit
    obtain ⟨b,bits,he,ht⟩ := literal_transform n s
    change BitstringEncoding.delimit (transformPayload (BitstringEncoding.bitEncode (n,s))) ++
      framed ((c.map BitstringEncoding.bitEncode).map transformPayload) =
      BitstringEncoding.delimit (BitstringEncoding.bitEncode (evenLiteral (n,s))) ++
        BitstringEncoding.bitEncode (evenClause c)
    rw [he,ht,ih]
    rfl

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .head none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

/-- The finite machine reads and renames every literal, preserves order, and
returns the canonical clause encoding. -/
theorem run_clause (c : Clause) :
    ∃ t ≤ 6*(BitstringEncoding.bitEncode c).length+2,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode c)) =
        some (Turing.haltList machine (BitstringEncoding.bitEncode (evenClause c))) := by
  let blocks := c.map BitstringEncoding.bitEncode
  let input := BitstringEncoding.bitEncode c
  let result := BitstringEncoding.bitEncode (evenClause c)
  have hi : framed blocks = input := rfl
  have ho : framed (blocks.map transformPayload) = result := literal_blocks_correct c
  have hl := framed_length_bound blocks
  rw [hi,ho] at hl
  obtain ⟨v,hs⟩ := scan_blocks blocks [] [] [] none (literal_blocks_nonempty c)
  rw [hi,ho] at hs
  simp only [List.append_nil] at hs
  change ∃ t ≤ 6*input.length+2, runSteps machine.step t (Turing.initList machine input) =
    some (Turing.haltList machine result)
  refine ⟨input.length+1+(result.length+1),by omega,?_⟩
  rw [initial_eq,show input.length+1+(result.length+1) = input.length+(1+(result.length+1)) by omega,runSteps_add,hs]
  change runSteps machine.step (1+(result.length+1)) (cfg .head v [] result.reverse []) = _
  rw [Nat.add_comm 1 _,runSteps_front,head_nil]
  simpa using restore_run result.reverse [] none

noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Clause → List Bool)
    (BitstringEncoding.bitEncode : Clause → List Bool) evenClause where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 6*Polynomial.X+Polynomial.C 2
  outputsFun c := by
    classical
    let t := Nat.find (run_clause c)
    have ht := (Nat.find_spec (run_clause c)).1
    have hr := (Nat.find_spec (run_clause c)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode c).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (evenClause c)).map id))
      simpa using hr
    · simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using ht

theorem evenClause_isPolyTime : ComplexityTheory.IsPolyTime evenClause := ⟨timeMachine⟩

/-- The single-literal operation has its own canonical machine proof. -/
theorem evenLiteral_isPolyTime : ComplexityTheory.IsPolyTime evenLiteral := by
  change ComplexityTheory.IsPolyTime
    (Shared.ComplexityBridge.TM2TypedPairMap.pairMap (γ := Bool) (fun n : Nat => 2*n))
  exact Shared.ComplexityBridge.TM2TypedPairMap.pairMap_isPolyTime _
    Shared.ComplexityBridge.CNFBinaryIndex.double_isPolyTime

namespace Fixtures
example : evenClause [(0,false),(1,true),(3,false)] = [(0,false),(2,true),(6,false)] := rfl
example : ∃ t ≤ 6*(BitstringEncoding.bitEncode ([(0,false),(1,true)] : Clause)).length+2,
    runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode ([(0,false),(1,true)] : Clause))) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode ([(0,false),(2,true)] : Clause))) := by
  simpa [evenClause,evenLiteral] using run_clause [(0,false),(1,true)]
end Fixtures

end Shared.ComplexityBridge.CNFEvenClause
