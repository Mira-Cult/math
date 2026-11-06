import Shared.ComplexityBridge.CNFBinaryAdd
import Shared.ComplexityBridge.TM2Undelimit
import Shared.ComplexityBridge.TM2UnaryTransfer
import Shared.ComplexityBridge.TM2GenericStackBound
import Shared.ComplexityBridge.CNFBinaryIndex
import Shared.ComplexityBridge.TM2Compose

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Load a delimited pair of binary numerals and add them on a finite TM2. -/
namespace Shared.ComplexityBridge.CNFBinaryPairAdd
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev U := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev A := Shared.ComplexityBridge.CNFBinaryAdd.machine
abbrev Key := Shared.ComplexityBridge.CNFBinaryAdd.Stack
abbrev UL := Shared.ComplexityBridge.TM2Undelimit.Label
abbrev UK := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev AL := Shared.ComplexityBridge.CNFBinaryAdd.Label
abbrev AS := Shared.ComplexityBridge.CNFBinaryAdd.State
abbrev Label := UL ⊕ AL
abbrev State := Option Bool ⊕ AS

def uState : State → Option Bool | .inl v => v | _ => none
def aState : State → AS | .inr v => v | _ => (false,none,none)
def uKey : UK → Key | .input => .right | .scratch => .scratch | .payload => .left

def uStacks (S : UK → List Bool) (extra : List Bool) : Key → List Bool
  | .left => S .payload | .right => S .input | .scratch => S .scratch | .output => extra
@[simp] theorem uStacks_apply (S : UK → List Bool) (extra : List Bool) (j : UK) :
    uStacks S extra (uKey j) = S j := by cases j <;> rfl

theorem uStacks_update (S : UK → List Bool) (extra : List Bool) (j : UK) (xs : List Bool) :
    uStacks (Function.update S j xs) extra = Function.update (uStacks S extra) (uKey j) xs := by
  funext k; cases j <;> cases k <;> simp [uStacks,uKey,Function.update]

def uEmbed (extra : List Bool) (q : U.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inl,.inl q.var,uStacks q.stk extra⟩

def aEmbed (q : A.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inr, if q.l.isSome then .inr q.var else .inl none,q.stk⟩

def liftU : U.Stmt → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (uKey j) (fun v => f (uState v)) (liftU q)
  | .peek j f q => .peek (uKey j) (fun v h => .inl (f (uState v) h)) (liftU q)
  | .pop j f q => .pop (uKey j) (fun v h => .inl (f (uState v) h)) (liftU q)
  | .load f q => .load (fun v => .inl (f (uState v))) (liftU q)
  | .branch f q r => .branch (fun v => f (uState v)) (liftU q) (liftU r)
  | .goto f => .goto (fun v => .inl (f (uState v)))
  | .halt => .halt

def liftA : A.Stmt → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (aState v)) (liftA q)
  | .peek j f q => .peek j (fun v h => .inr (f (aState v) h)) (liftA q)
  | .pop j f q => .pop j (fun v h => .inr (f (aState v) h)) (liftA q)
  | .load f q => .load (fun v => .inr (f (aState v))) (liftA q)
  | .branch f q r => .branch (fun v => f (aState v)) (liftA q) (liftA r)
  | .goto f => .goto (fun v => .inr (f (aState v)))
  | .halt => .load (fun _ => .inl none) .halt

theorem liftU_aux (q : U.Stmt) (v : Option Bool) (S : UK → List Bool) (extra : List Bool) :
    stepAux (liftU q) (.inl v) (uStacks S extra) = uEmbed extra (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftU,stepAux,uState,uStacks_apply]
    rw [←uStacks_update S extra j (f v::S j)]
    exact ih _ _
  | peek j f q ih =>
    simp only [liftU,stepAux,uState,uStacks_apply]
    exact ih _ _
  | pop j f q ih =>
    simp only [liftU,stepAux,uState,uStacks_apply]
    rw [←uStacks_update S extra j (S j).tail]
    exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftU,stepAux,uState,h,ihq,ihr]

theorem liftA_aux (q : A.Stmt) (v : AS) (S : Key → List Bool) :
    stepAux (liftA q) (.inr v) S = aEmbed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftA,stepAux,aState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .done => .load (fun _ => .inr (false,none,none)) (.goto (fun _ => .inr .readLeft))
  | .inl .reject => .pop .scratch (fun _ h => .inl h)
      (.branch (fun v => (uState v).isSome)
        (.goto (fun _ => .inl .reject)) (.load (fun _ => .inl none) .halt))
  | .inl l => liftU (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr l => liftA (Shared.ComplexityBridge.CNFBinaryAdd.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .right
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .header
  σ := State
  initialState := .inl none
  m := program

def uTerminal (q : U.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred uTerminal := fun _ => Classical.propDecidable _
theorem u_stable (q : U.Cfg) (h : uTerminal q) : U.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done ∨ l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem u_step (extra : List Bool) (q : U.Cfg) (h : ¬ uTerminal q) :
    machine.step (uEmbed extra q) = (U.step q).map (uEmbed extra) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (liftU (Shared.ComplexityBridge.TM2Undelimit.program _)) (.inl v) (uStacks S extra)) = _
        rw [liftU_aux]; rfl

theorem a_step (q : A.Cfg) : machine.step (aEmbed q) = (A.step q).map aEmbed := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftA (Shared.ComplexityBridge.CNFBinaryAdd.program l)) (.inr v) S) = _
      rw [liftA_aux]; rfl

theorem a_run (start finish : A.Cfg) (n : Nat) (h : runSteps A.step n start = some finish) :
    runSteps machine.step n (aEmbed start) = some (aEmbed finish) := by
  induction n generalizing finish with
  | zero =>
    change some start = some finish at h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    change (runSteps A.step n start).bind A.step = some finish at h
    cases hr : runSteps A.step n start with
    | none => rw [hr] at h; cases h
    | some mid =>
      rw [hr] at h
      change A.step mid = some finish at h
      change (runSteps machine.step n (aEmbed start)).bind _ = _
      rw [ih mid hr]
      change machine.step (aEmbed mid) = some (aEmbed finish)
      rw [a_step,h]
      rfl

theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits = uEmbed [] (Turing.initList U bits) := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 2
  funext k
  cases k <;> simp [machine,U,Shared.ComplexityBridge.TM2Undelimit.machine,Turing.initList,uEmbed,uStacks,uKey]

theorem dispatch (a b : List Bool) :
    machine.step (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a)) =
      some (aEmbed (Shared.ComplexityBridge.CNFBinaryAdd.cfg .readLeft (false,none,none) a b [] [])) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2

theorem halt_eq (xs : List Bool) : aEmbed (Turing.haltList A xs) = Turing.haltList machine xs := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 2

/-- The complete loader and adder halt on encoded bit-list pairs, in time
linear in their bit lengths. -/
theorem run_pair_bits (a b : List Bool) :
    ∃ t ≤ 3*a.length+2 + 1 + (3*max a.length b.length+4),
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.delimit a ++ b)) =
        some (Turing.haltList machine (Shared.Codes.BinaryAddition.addBits a b false)) := by
  let fin := Shared.ComplexityBridge.TM2Undelimit.cfg .done none b [] a
  have hl := Shared.ComplexityBridge.TM2Undelimit.valid_run a b
  change runSteps U.step (3*a.length+2) (Turing.initList U (BitstringEncoding.delimit a ++ b)) = some fin at hl
  obtain ⟨d,hd,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    U.step machine.step (uEmbed []) uTerminal u_stable (u_step []) _ _ fin (by exact Or.inl rfl) hl
  obtain ⟨n,hn,ha,_⟩ := Shared.ComplexityBridge.CNFBinaryAdd.run_add_bounded a b
  refine ⟨d+1+n,by omega,?_⟩
  rw [initial_eq,show d+1+n = d+(1+n) by omega,runSteps_add,hr]
  change runSteps machine.step (1+n) (uEmbed [] fin) = _
  rw [Nat.add_comm 1 n,runSteps_front]
  rw [dispatch]
  simpa [halt_eq] using a_run _ _ n ha

/-- The malformed-input path erases the partial payload before halting.
    The empty output is a specified fallback, not an acceptance signal. -/
theorem reject_cons (v : Option Bool) (b : Bool) (scratch : List Bool) :
    machine.step (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .reject v [] (b::scratch) [])) =
      some (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .reject (some b) [] scratch [])) := by
  change some (Cfg.mk _ _ (Function.update (uStacks (Shared.ComplexityBridge.TM2Undelimit.stackVals [] (b::scratch) []) []) Shared.ComplexityBridge.CNFBinaryAdd.Stack.scratch scratch)) = _
  congr 1; congr 1; funext k; cases k <;> simp [uEmbed,uStacks,Shared.ComplexityBridge.TM2Undelimit.cfg,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem reject_nil (v : Option Bool) :
    machine.step (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .reject v [] [] [])) =
      some (Turing.haltList machine []) := by
  change some (Cfg.mk _ _ (Function.update (uStacks (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] []) []) Shared.ComplexityBridge.CNFBinaryAdd.Stack.scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [uEmbed,uStacks,Shared.ComplexityBridge.TM2Undelimit.cfg,Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update,Turing.haltList,machine]

theorem reject_run (scratch : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1)
      (uEmbed [] (Shared.ComplexityBridge.TM2Undelimit.cfg .reject v [] scratch [])) =
        some (Turing.haltList machine []) := by
  induction scratch generalizing v with
  | nil => exact reject_nil v
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,reject_cons]
    exact ih (some b)

theorem parser_push_bound : Shared.ComplexityBridge.TM2GenericStackBound.tableBound U ≤ 1 := by
  classical
  unfold Shared.ComplexityBridge.TM2GenericStackBound.tableBound
  apply Finset.sup_le
  intro l _
  cases l <;> decide

/-- Every malformed delimiter is consumed, the partial work is erased, and
    the machine halts with the empty fallback in at most `3*length+3` blocks. -/
theorem malformed_run (input : List Bool) (h : BitstringEncoding.undelimit input = none) :
    ∃ t ≤ 3*input.length+3,
      runSteps machine.step t (Turing.initList machine input) = some (Turing.haltList machine []) := by
  obtain ⟨n,hn,scratch,hr⟩ := Shared.ComplexityBridge.TM2Undelimit.invalid_run input [] [] none h
  have hu : runSteps U.step n (Turing.initList U input) =
      some (Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []) := by
    simpa [Shared.ComplexityBridge.TM2Undelimit.initial_eq] using hr
  have hs := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length U input n
    (Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []) hu .scratch
  have hs' : scratch.length ≤ input.length+n := by
    change scratch.length ≤ input.length+n*Shared.ComplexityBridge.TM2GenericStackBound.tableBound U at hs
    have hd : n*Shared.ComplexityBridge.TM2GenericStackBound.tableBound U ≤ n := by
      simpa using Nat.mul_le_mul_left n parser_push_bound
    omega
  let fin := Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []
  obtain ⟨d,hd,he⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    U.step machine.step (uEmbed []) uTerminal u_stable (u_step []) n _ fin (by exact Or.inr rfl) hu
  refine ⟨d+(scratch.length+1),by omega,?_⟩
  rw [initial_eq,runSteps_add,he]
  exact reject_run scratch none

/-- Total raw execution: either the delimiter is malformed and gives the
fallback, or the two bit lists are added. This is a termination statement,
not a certificate that a raw output is a valid encoded numeral. -/
theorem raw_run (input : List Bool) :
    ∃ t ≤ 6*input.length+7, ∃ output,
      runSteps machine.step t (Turing.initList machine input) = some (Turing.haltList machine output) := by
  cases h : BitstringEncoding.undelimit input with
  | none =>
    obtain ⟨t,ht,hr⟩ := malformed_run input h
    exact ⟨t,by omega,[],hr⟩
  | some pair =>
    obtain ⟨a,b⟩ := pair
    have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound input a b h
    obtain ⟨t,ht,hr⟩ := run_pair_bits a b
    have hl : input.length = 2*a.length+1+b.length := by
      rw [←he,List.length_append,BitstringEncoding.length_delimit]
    refine ⟨t,by omega,Shared.Codes.BinaryAddition.addBits a b false,?_⟩
    simpa [he] using hr

/-- Google pair encoding delimits the first canonical numeral and then
appends the second. -/
theorem pair_encoding (a b : Nat) :
    BitstringEncoding.bitEncode (a,b) = BitstringEncoding.delimit a.bits ++ b.bits := by
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
    BitstringEncoding.bitEncode b = _
  have ha : BitstringEncoding.bitEncode a = a.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits a
  have hb : BitstringEncoding.bitEncode b = b.bits := Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits b
  rw [ha,hb]

def addPair (p : Nat × Nat) : Nat := p.1+p.2

theorem run_numeral_pair (a b : Nat) :
    ∃ t ≤ 3*(BitstringEncoding.bitEncode (a,b)).length+4,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode (a,b))) =
        some (Turing.haltList machine (BitstringEncoding.bitEncode (a+b))) := by
  obtain ⟨t,ht,hr⟩ := run_pair_bits a.bits b.bits
  refine ⟨t,?_,?_⟩
  · rw [pair_encoding, List.length_append, BitstringEncoding.length_delimit]
    omega
  · rw [pair_encoding]
    have he : BitstringEncoding.bitEncode (a+b) = (a+b).bits :=
      Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits (a+b)
    rw [he]
    simpa only [Shared.Codes.BinaryAdditionCanonical.addBits_numerals] using hr

/-- Addition on canonical Google-encoded natural pairs has a finite TM2
witness with a linear bound in the full encoded input length. -/
noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Nat × Nat → List Bool)
    (BitstringEncoding.bitEncode : Nat → List Bool) addPair where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 4
  outputsFun p := by
    classical
    rcases p with ⟨a,b⟩
    let t := Nat.find (run_numeral_pair a b)
    have ht := (Nat.find_spec (run_numeral_pair a b)).1
    have hr := (Nat.find_spec (run_numeral_pair a b)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode (a,b)).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (addPair (a,b))).map id))
      simpa [addPair] using hr
    · simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using ht

theorem addPair_isPolyTime : ComplexityTheory.IsPolyTime addPair := ⟨timeMachine⟩

/-- The actual selector expression in `choices start count` is computable
in polynomial time on a canonical pair of binary indices. -/
theorem selector_add_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Nat => Shared.ComplexityBridge.CNFDisjunction.selector (p.1+p.2)) := by
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp addPair
    Shared.ComplexityBridge.CNFDisjunction.selector addPair_isPolyTime
    Shared.ComplexityBridge.CNFBinaryIndex.selector_isPolyTime

namespace Fixtures
example : ∃ t ≤ 9, runSteps machine.step t
    (Turing.initList machine [true,false]) = some (Turing.haltList machine []) := by
  have h : BitstringEncoding.undelimit [true,false] = none := rfl
  simpa using malformed_run [true,false] h

example : ∃ t ≤ 7, runSteps machine.step t
    (Turing.initList machine (BitstringEncoding.bitEncode ((0,0) : Nat × Nat))) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (0 : Nat))) := by
  simpa [pair_encoding,BitstringEncoding.delimit] using run_numeral_pair 0 0
end Fixtures

end Shared.ComplexityBridge.CNFBinaryPairAdd
