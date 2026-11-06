import Shared.ComplexityBridge.TM2NumeralPairLoader
import Shared.ComplexityBridge.TM2GenericStackBound
import Shared.ComplexityBridge.TM2UnaryTransfer

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace Shared.ComplexityBridge.TM2NumeralPairCompare
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Key := Shared.ComplexityBridge.TM2NumeralPairLoader.Stack
abbrev Loader := Shared.ComplexityBridge.TM2NumeralPairLoader.machine
abbrev Compare := Shared.ComplexityBridge.TM2NumeralCompare.machine
abbrev LLabel := Shared.ComplexityBridge.TM2NumeralPairLoader.Label
abbrev CLabel := Shared.ComplexityBridge.TM2NumeralCompare.Label
abbrev CStack := Shared.ComplexityBridge.TM2NumeralCompare.Stack
abbrev CState := Shared.ComplexityBridge.TM2NumeralCompare.State
inductive CleanLabel where | left | right deriving DecidableEq
instance : Fintype CleanLabel := Fintype.ofList [.left,.right] (by intro l; cases l <;> simp)
abbrev Label := LLabel ⊕ (CLabel ⊕ CleanLabel)
abbrev State := Option Bool ⊕ (CState ⊕ (Bool × Option Bool))

def loaderState : State → Option Bool | .inl v => v | _ => none
def compareState : State → CState | .inr (.inl v) => v | _ => (none,none,none)
def cleanState : State → Bool × Option Bool | .inr (.inr v) => v | _ => (false,none)

def compareKey : CStack → Key | .left => .left | .right => .right
def compareStacks (S : CStack → List Bool) (other : Key → List Bool) : Key → List Bool
  | .left => S .left | .right => S .right | k => other k
@[simp] theorem compareStacks_apply (S : CStack → List Bool) (other : Key → List Bool) (j : CStack) :
    compareStacks S other (compareKey j) = S j := by cases j <;> rfl

theorem compare_update (S : CStack → List Bool) (other : Key → List Bool) (j : CStack) (xs : List Bool) :
    compareStacks (Function.update S j xs) other = Function.update (compareStacks S other) (compareKey j) xs := by
  funext k; cases j <;> cases k <;> simp [compareStacks,compareKey,Function.update]

def loaderEmbed (q : Loader.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inl,.inl q.var,q.stk⟩
def compareEmbed (other : Key → List Bool) (q : Compare.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inr (.inl q.var),compareStacks q.stk other⟩

def liftLoader : Stmt (fun _ : Key => Bool) LLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (loaderState v)) (liftLoader q)
  | .peek j f q => .peek j (fun v h => .inl (f (loaderState v) h)) (liftLoader q)
  | .pop j f q => .pop j (fun v h => .inl (f (loaderState v) h)) (liftLoader q)
  | .load f q => .load (fun v => .inl (f (loaderState v))) (liftLoader q)
  | .branch f q r => .branch (fun v => f (loaderState v)) (liftLoader q) (liftLoader r)
  | .goto f => .goto (fun v => .inl (f (loaderState v)))
  | .halt => .halt

def liftCompare : Stmt (fun _ : CStack => Bool) CLabel CState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (compareKey j) (fun v => f (compareState v)) (liftCompare q)
  | .peek j f q => .peek (compareKey j) (fun v h => .inr (.inl (f (compareState v) h))) (liftCompare q)
  | .pop j f q => .pop (compareKey j) (fun v h => .inr (.inl (f (compareState v) h))) (liftCompare q)
  | .load f q => .load (fun v => .inr (.inl (f (compareState v)))) (liftCompare q)
  | .branch f q r => .branch (fun v => f (compareState v)) (liftCompare q) (liftCompare r)
  | .goto f => .goto (fun v => .inr (.inl (f (compareState v))))
  | .halt => .halt

theorem liftLoader_aux (q : Loader.Stmt) (v : Option Bool) (S : Key → List Bool) :
    stepAux (liftLoader q) (.inl v) S = loaderEmbed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLoader,stepAux,loaderState,h,ihq,ihr]

theorem liftCompare_aux (q : Compare.Stmt) (v : CState) (S : CStack → List Bool) (other : Key → List Bool) :
    stepAux (liftCompare q) (.inr (.inl v)) (compareStacks S other) = compareEmbed other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftCompare,stepAux,compareState,compareStacks_apply]
    rw [← compare_update S other j (f v::S j)]
    exact ih _ _
  | peek j f q ih =>
    simp only [liftCompare,stepAux,compareState,compareStacks_apply]
    exact ih _ _
  | pop j f q ih =>
    simp only [liftCompare,stepAux,compareState,compareStacks_apply]
    rw [← compare_update S other j (S j).tail]
    exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftCompare,stepAux,compareState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .done => .load (fun _ => .inr (.inl (none,none,none))) (.goto (fun _ => .inr (.inl .scan)))
  | .inl l => liftLoader (Shared.ComplexityBridge.TM2NumeralPairLoader.program l)
  | .inr (.inl .accept) => .load (fun _ => .inr (.inr (true,none))) (.goto (fun _ => .inr (.inr .left)))
  | .inr (.inl .reject) => .load (fun _ => .inr (.inr (false,none))) (.goto (fun _ => .inr (.inr .left)))
  | .inr (.inl l) => liftCompare (Shared.ComplexityBridge.TM2NumeralCompare.program l)
  | .inr (.inr .left) => .pop .left (fun v h => .inr (.inr ((cleanState v).1,h)))
      (.branch (fun v => (cleanState v).2.isSome) (.goto (fun _ => .inr (.inr .left)))
        (.goto (fun _ => .inr (.inr .right))))
  | .inr (.inr .right) => .pop .right (fun v h => .inr (.inr ((cleanState v).1,h)))
      (.branch (fun v => (cleanState v).2.isSome) (.goto (fun _ => .inr (.inr .right)))
        (.push .input (fun v => (cleanState v).1) (.load (fun _ => .inl none) .halt)))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .input
  k₁ := .input
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .x0
  σ := State
  initialState := .inl none
  m := program

def loaderTerminal (q : Loader.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred loaderTerminal := fun _ => Classical.propDecidable _
theorem loader_stable (q : Loader.Cfg) (h : loaderTerminal q) : Loader.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2NumeralPairLoader.Label.done at h
    subst l
    rfl

theorem loader_step (q : Loader.Cfg) (h : ¬ loaderTerminal q) :
    machine.step (loaderEmbed q) = (Loader.step q).map loaderEmbed := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | x0 | x1 | x2 | x3 | x4 | x5 | y0 | y1 | y2 | restoreX | restoreY =>
        change some (stepAux (liftLoader (Shared.ComplexityBridge.TM2NumeralPairLoader.program _)) (.inl v) S) = _
        rw [liftLoader_aux]; rfl

def compareTerminal (q : Compare.Cfg) : Prop := q.l = some .accept ∨ q.l = some .reject
noncomputable instance : DecidablePred compareTerminal := fun _ => Classical.propDecidable _
theorem compare_stable (q : Compare.Cfg) (h : compareTerminal q) : Compare.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2NumeralCompare.Label.accept ∨ l = some Shared.ComplexityBridge.TM2NumeralCompare.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem compare_step (other : Key → List Bool) (q : Compare.Cfg) (h : ¬ compareTerminal q) :
    machine.step (compareEmbed other q) = (Compare.step q).map (compareEmbed other) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | accept => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | scan | checkLeft | checkRight =>
        change some (stepAux (liftCompare (Shared.ComplexityBridge.TM2NumeralCompare.program _)) (.inr (.inl v)) (compareStacks S other)) = _
        rw [liftCompare_aux]; rfl

theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits = loaderEmbed (Turing.initList Loader bits) := by rfl

theorem loader_dispatch (x y : List Bool) :
    machine.step (loaderEmbed (Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] x y)) =
      some (compareEmbed (fun _ => []) (Shared.ComplexityBridge.TM2NumeralCompare.cfg .scan (none,none,none) x y)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k <;> rfl

def cleanCfg (l : CleanLabel) (answer : Bool) (flag : Option Bool) (x y : List Bool) : machine.Cfg :=
  ⟨some (.inr (.inr l)),.inr (.inr (answer,flag)),
    Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals [] [] [] x y⟩

theorem compare_dispatch (q : Compare.Cfg) (answer : Bool)
    (h : q.l = some (if answer then .accept else .reject)) :
    machine.step (compareEmbed (fun _ => []) q) = some (cleanCfg .left answer none (q.stk .left) (q.stk .right)) := by
  cases q with
  | mk l v S =>
    cases answer <;> simp only [Bool.false_eq_true,if_false,if_true] at h <;> subst l <;>
      change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _) <;> congr 2 <;> funext k <;> cases k <;> rfl

theorem clean_left_cons (b answer : Bool) (flag : Option Bool) (x y : List Bool) :
    machine.step (cleanCfg .left answer flag (b::x) y) = some (cleanCfg .left answer (some b) x y) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals [] [] [] (b::x) y) .left x)) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals,Function.update]

theorem clean_left_nil (answer : Bool) (flag : Option Bool) (y : List Bool) :
    machine.step (cleanCfg .left answer flag [] y) = some (cleanCfg .right answer none [] y) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals [] [] [] [] y) .left [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals,Function.update]

theorem clean_right_cons (b answer : Bool) (flag : Option Bool) (y : List Bool) :
    machine.step (cleanCfg .right answer flag [] (b::y)) = some (cleanCfg .right answer (some b) [] y) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals [] [] [] [] (b::y)) .right y)) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals,Function.update]

theorem clean_right_nil (answer : Bool) (flag : Option Bool) :
    machine.step (cleanCfg .right answer flag [] []) = some (Turing.haltList machine [answer]) := by
  change some (Cfg.mk none (Sum.inl none : State)
    (Function.update (Function.update (Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals [] [] [] [] []) .right []) .input [answer])) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem clean_left_run (x y : List Bool) (answer : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step x.length (cleanCfg .left answer flag x y) = some (cleanCfg .left answer flag' [] y) := by
  induction x generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons b x ih =>
    obtain ⟨flag',h⟩ := ih (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clean_left_cons]
    exact h

theorem clean_right_run (y : List Bool) (answer : Bool) (flag : Option Bool) :
    ∃ flag', runSteps machine.step y.length (cleanCfg .right answer flag [] y) = some (cleanCfg .right answer flag' [] []) := by
  induction y generalizing flag with
  | nil => exact ⟨flag,rfl⟩
  | cons b y ih =>
    obtain ⟨flag',h⟩ := ih (some b)
    refine ⟨flag',?_⟩
    rw [List.length_cons,runSteps_front,clean_right_cons]
    exact h

theorem clean_run (x y : List Bool) (answer : Bool) :
    runSteps machine.step (x.length+y.length+2) (cleanCfg .left answer none x y) =
      some (Turing.haltList machine [answer]) := by
  obtain ⟨flag,hx⟩ := clean_left_run x y answer none
  obtain ⟨flag',hy⟩ := clean_right_run y answer none
  have ht : x.length+y.length+2 = x.length+(1+(y.length+1)) := by omega
  rw [ht,runSteps_add,hx]
  change runSteps machine.step (1+(y.length+1)) (cleanCfg .left answer flag [] y) = _
  rw [runSteps_add]
  change (machine.step (cleanCfg .left answer flag [] y)).bind (runSteps machine.step (y.length+1)) = _
  rw [clean_left_nil]
  change runSteps machine.step (y.length+1) (cleanCfg .right answer none [] y) = _
  rw [runSteps_add,hy]
  exact clean_right_nil answer flag'

/-- Computable bit-list equality after removing the decoder's representational ambiguity. -/
def answer (p : List Bool × List Bool) : Bool :=
  Shared.ComplexityBridge.NumeralNormalization.normalize p.1 ==
    Shared.ComplexityBridge.NumeralNormalization.normalize p.2

theorem answer_correct (x y : List Bool) :
    answer (x,y) = true ↔ Computability.decodeNat x = Computability.decodeNat y := by
  simp only [answer,beq_iff_eq]
  exact (Shared.ComplexityBridge.NumeralNormalization.decode_eq_iff_normalize_eq x y).symm

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 5 * Polynomial.X + Polynomial.C 8 + Polynomial.C 2 *
    ((Polynomial.X + Polynomial.C 2) * Polynomial.C (Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare))

/-- The loader, comparator and cleanup together are a finite machine whose
single Boolean output agrees with the pinned decoder on every pair. -/
theorem run_pair (x y : List Bool) :
    ∃ t ≤ timePolynomial.eval (BitstringEncoding.bitEncode (x,y)).length,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode (x,y))) =
        some (Turing.haltList machine [answer (x,y)]) := by
  let bits := BitstringEncoding.bitEncode (x,y)
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare
  let start := Shared.ComplexityBridge.TM2NumeralCompare.cfg .scan (none,none,none) x y
  let finish := Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] x y
  have hl := Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair x y
  change runSteps Loader.step (7*x.length+4*y.length+4) (Turing.initList Loader bits) = some finish at hl
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Loader.step machine.step loaderEmbed loaderTerminal loader_stable loader_step _ _ finish (by rfl) hl
  have ha' : a ≤ 2*bits.length+2 := le_trans ha (Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair_cost x y)
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2NumeralCompare.compare_progress x y
  change runSteps Compare.step n start = some q at hr
  have hqt : compareTerminal q := by
    unfold compareTerminal
    by_cases h : Computability.decodeNat x = Computability.decodeNat y
    · left; simpa [h] using hq
    · right; simpa [h] using hq
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Compare.step machine.step (compareEmbed (fun _ => [])) compareTerminal compare_stable
    (compare_step (fun _ => [])) n start q hqt hr
  have hqa : q.l = some (if answer (x,y) then .accept else .reject) := by
    by_cases h : Computability.decodeNat x = Computability.decodeNat y
    · have ha : answer (x,y) = true := (answer_correct x y).2 h
      simpa [h,ha] using hq
    · have ha : answer (x,y) = false := by
        cases hv : answer (x,y) with
        | false => rfl
        | true => exact False.elim (h ((answer_correct x y).1 hv))
      simpa [h,ha] using hq
  have hbits : bits.length = 6*x.length+1+3*y.length :=
    Shared.ComplexityBridge.bitstring_pair_encoded_length x y
  have hx : x.length ≤ bits.length := by omega
  have hy : y.length ≤ bits.length := by omega
  have hn' : n ≤ bits.length+2 := by have hm := max_le hx hy; omega
  have hmul : n*D ≤ (bits.length+2)*D := Nat.mul_le_mul_right D hn'
  have hleft := Shared.ComplexityBridge.TM2GenericStackBound.run_length Compare n start q hr .left
  have hright := Shared.ComplexityBridge.TM2GenericStackBound.run_length Compare n start q hr .right
  change (q.stk .left).length ≤ x.length+n*D at hleft
  change (q.stk .right).length ≤ y.length+n*D at hright
  have hs : (q.stk .left).length+(q.stk .right).length ≤ 2*bits.length+2*((bits.length+2)*D) := by omega
  let c := (q.stk .left).length+(q.stk .right).length+2
  have hc := clean_run (q.stk .left) (q.stk .right) (answer (x,y))
  refine ⟨a+1+b+1+c,?_,?_⟩
  · change a+1+b+1+c ≤ timePolynomial.eval bits.length
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    change a+1+b+1+c ≤ 5*bits.length+8+2*((bits.length+2)*D)
    dsimp [c]; omega
  · rw [initial_eq,show a+1+b+1+c = a+(1+(b+(1+c))) by omega,runSteps_add,har]
    change runSteps machine.step (1+(b+(1+c))) (loaderEmbed finish) = _
    rw [runSteps_add]
    change (machine.step (loaderEmbed finish)).bind (runSteps machine.step (b+(1+c))) = _
    rw [loader_dispatch]
    change runSteps machine.step (b+(1+c)) (compareEmbed (fun _ => []) start) = _
    rw [runSteps_add,hbr]
    change runSteps machine.step (1+c) (compareEmbed (fun _ => []) q) = _
    rw [runSteps_add]
    change (machine.step (compareEmbed (fun _ => []) q)).bind (runSteps machine.step c) = _
    rw [compare_dispatch q (answer (x,y)) hqa]
    exact hc

noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    (BitstringEncoding.bitEncode : Bool → List Bool) answer where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun p := by
    let t := Classical.choose (run_pair p.1 p.2)
    have ht := (Classical.choose_spec (run_pair p.1 p.2)).1
    have hr := (Classical.choose_spec (run_pair p.1 p.2)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode p).map id))) =
          some (Turing.haltList machine ((BitstringEncoding.bitEncode (answer p)).map id))
      rw [List.map_id,List.map_id]
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine (BitstringEncoding.bitEncode p))) =
          some (Turing.haltList machine [answer p])
      simpa [t] using hr
    · simpa using ht

/-- Equality of decoded variable names is a canonical polynomial-time Boolean
relation, with the actual pair encoding, input boundary and one-bit output. -/
theorem answer_isPolyTime : ComplexityTheory.IsPolyTime answer := ⟨timeMachine⟩

namespace Fixtures
example : (runSteps machine.step 9
    (Turing.initList machine (BitstringEncoding.bitEncode (([],[]) : List Bool × List Bool)))).map
    (fun q => (q.l.isNone,q.stk .input)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .input)) (runSteps machine.step 9
    (Turing.initList machine (BitstringEncoding.bitEncode (([],[]) : List Bool × List Bool)))) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 26
    (Turing.initList machine (BitstringEncoding.bitEncode ([false],[false,true])))).map
    (fun q => (q.l.isNone,q.stk .input)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .input)) (runSteps machine.step 26
    (Turing.initList machine (BitstringEncoding.bitEncode ([false],[false,true])))) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 13
    (Turing.initList machine (BitstringEncoding.bitEncode (([] : List Bool),[true])))).map
    (fun q => (q.l.isNone,q.stk .input)) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .input)) (runSteps machine.step 13
    (Turing.initList machine (BitstringEncoding.bitEncode (([] : List Bool),[true])))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2NumeralPairCompare
