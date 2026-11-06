import Shared.Codes.TM2CheckedCandidate
import Shared.ComplexityBridge.TM2Reification

namespace Shared.ComplexityBridge.TM2FiniteReverse
open Turing.TM2 Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution
open Shared.Codes.TM2StatementValidation Shared.Codes.FiniteTables Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2Reification

/-- One extra value provides a total default for malformed numeric entries.
Validated runs remain inside the original bounds. -/
def clip (n x : Nat) : Fin (n+1) :=
  if h : x < n+1 then ⟨x,h⟩ else ⟨0,by omega⟩

@[simp] theorem clip_val (n x : Nat) (h : x < n+1) : (clip n x).val = x := by simp [clip,h]

def readUnary (states outputs : Nat) (t : List Nat) (v : Fin (states+1)) : Fin (outputs+1) :=
  clip outputs ((lookup t v.val).getD 0)

def readBinary (states symbols : Nat) (t : List (List Nat))
    (v : Fin (states+1)) (head : Option (Fin (symbols+1))) : Fin (states+1) :=
  clip states ((lookup₂ t v.val (symbolIndex (head.map Fin.val))).getD 0)

def readBool (states : Nat) (t : List Nat) (v : Fin (states+1)) : Bool :=
  (lookup t v.val).getD 0 == 1

/-- Translate one finite numeric statement to the actual mathlib statement
syntax. Invalid indices/values are totalized to an extra finite default. -/
def finiteStmt (ks states symbols labels : Nat) : Code →
    Stmt (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1))
  | .halt => .halt
  | .goto t => .goto (readUnary states labels t)
  | .push k t q => .push (clip ks k) (readUnary states symbols t) (finiteStmt ks states symbols labels q)
  | .peek k t q => .peek (clip ks k) (readBinary states symbols t) (finiteStmt ks states symbols labels q)
  | .pop k t q => .pop (clip ks k) (readBinary states symbols t) (finiteStmt ks states symbols labels q)
  | .load t q => .load (readUnary states states t) (finiteStmt ks states symbols labels q)
  | .branch t a b => .branch (readBool states t) (finiteStmt ks states symbols labels a) (finiteStmt ks states symbols labels b)

def finiteProgram (ks states symbols : Nat) (p : List Code) (l : Fin (p.length+1)) :
    Stmt (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (p.length+1)) (Fin (states+1)) :=
  finiteStmt ks states symbols p.length ((p[l.val]?).getD .halt)

/-- A finite core machine. This is not yet the input/output-boundary wrapper
needed for a `TM2ComputableInPolyTime` witness. -/
def finiteCore (ks states symbols : Nat) (p : List Code) (inputStack outputStack initialLabel initialState : Nat) : Turing.FinTM2 where
  K := Fin (ks+1)
  k₀ := clip ks inputStack
  k₁ := clip ks outputStack
  Γ := fun _ => Fin (symbols+1)
  Λ := Fin (p.length+1)
  main := clip p.length initialLabel
  σ := Fin (states+1)
  initialState := clip states initialState
  m := finiteProgram ks states symbols p

theorem readUnary_valid {states outputs : Nat} {t : List Nat}
    (ht : unaryValid t states outputs = true) (v : Fin (states+1)) (hv : v.val < states) :
    (readUnary states outputs t v).val = (lookup t v.val).getD 0 ∧
      (readUnary states outputs t v).val < outputs := by
  obtain ⟨x,hx,hbound⟩ := unary_get ht hv
  simp only [readUnary, hx, Option.getD_some]
  rw [clip_val outputs x (by omega)]
  exact ⟨rfl,hbound⟩

theorem readBinary_valid {states symbols : Nat} {t : List (List Nat)}
    (ht : binaryValid t states (symbols+1) states = true) (v : Fin (states+1))
    (hv : v.val < states) (o : Option (Fin (symbols+1)))
    (ho : symbolIndex (o.map Fin.val) < symbols+1) :
    (readBinary states symbols t v o).val = (lookup₂ t v.val (symbolIndex (o.map Fin.val))).getD 0 ∧
      (readBinary states symbols t v o).val < states := by
  obtain ⟨x,hx,hbound⟩ := binary_get ht hv ho
  simp only [readBinary, hx, Option.getD_some]
  rw [clip_val states x (by omega)]
  exact ⟨rfl,hbound⟩

example : (clip 2 1).val = 1 := by decide
example : (clip 2 9).val = 0 := by decide
example : (readUnary 0 1 [1] ⟨0,by decide⟩).val = 1 := by decide

abbrev FStacks (ks symbols : Nat) := Fin (ks+1) → List (Fin (symbols+1))

def StackRel (ks symbols : Nat) (S : FStacks ks symbols) (T : Nat → List Nat) : Prop :=
  ∀ k, T k.val = (S k).map Fin.val

def Safe (ks symbols : Nat) (S : FStacks ks symbols) : Prop :=
  ∀ k x, x ∈ S k → x.val < symbols

def CfgRel (ks states symbols labels : Nat)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1)))
    (d : Cfg (fun _ : Nat => Nat) Nat Nat) : Prop :=
  d.l = c.l.map Fin.val ∧ d.var = c.var.val ∧ StackRel ks symbols c.stk d.stk

theorem rel_update {ks symbols : Nat} (S : FStacks ks symbols) (T : Nat → List Nat)
    (hr : StackRel ks symbols S T) (k : Fin (ks+1)) (xs : List (Fin (symbols+1))) :
    StackRel ks symbols (Function.update S k xs) (Function.update T k.val (xs.map Fin.val)) := by
  intro j
  by_cases hj : j = k
  · subst j; simp
  · have hval : j.val ≠ k.val := by intro h; exact hj (Fin.ext h)
    simpa [Function.update_of_ne hj, Function.update_of_ne hval] using hr j

theorem safe_update {ks symbols : Nat} (S : FStacks ks symbols) (hs : Safe ks symbols S)
    (k : Fin (ks+1)) (xs : List (Fin (symbols+1))) (hx : ∀ x ∈ xs, x.val < symbols) :
    Safe ks symbols (Function.update S k xs) := by
  intro j x hm
  by_cases hj : j = k
  · subst j; simp only [Function.update_self] at hm; exact hx x hm
  · simp only [Function.update_of_ne hj] at hm
    exact hs j x hm

theorem safe_head {ks symbols : Nat} (S : FStacks ks symbols) (hs : Safe ks symbols S)
    (k : Fin (ks+1)) : symbolIndex ((S k).head?.map Fin.val) < symbols+1 := by
  cases h : S k with
  | nil => simp [symbolIndex]
  | cons a xs =>
    have ha : a.val < symbols := hs k a (by simp [h])
    simp [symbolIndex]
    omega

theorem rel_head {ks symbols : Nat} (S : FStacks ks symbols) (T : Nat → List Nat)
    (hr : StackRel ks symbols S T) (k : Fin (ks+1)) :
    (T k.val).head? = (S k).head?.map Fin.val := by
  rw [hr k]
  cases S k <;> rfl

theorem rel_tail {ks symbols : Nat} (S : FStacks ks symbols) (T : Nat → List Nat)
    (hr : StackRel ks symbols S T) (k : Fin (ks+1)) :
    (T k.val).tail = ((S k).tail).map Fin.val := by
  rw [hr k]
  cases S k <;> rfl

/-- A validated numeric statement and its finite translation execute the
same complete TM2 statement block on related bounded configurations. -/
theorem finite_stepAux (ks states symbols labels : Nat) (q : Code)
    (hq : valid ks states symbols labels q = true)
    (v : Fin (states+1)) (S : FStacks ks symbols) (T : Nat → List Nat)
    (hv : v.val < states) (hs : Safe ks symbols S) (hr : StackRel ks symbols S T) :
    CfgRel ks states symbols labels (stepAux (finiteStmt ks states symbols labels q) v S)
      (stepAux (interpret q) v.val T) := by
  induction q generalizing v S T with
  | halt => simp [finiteStmt, interpret, stepAux, CfgRel, hr]
  | goto t =>
    have ht : unaryValid t states labels = true := hq
    obtain ⟨hval,hbound⟩ := readUnary_valid ht v hv
    simp [finiteStmt, interpret, stepAux, CfgRel, hval, hr]
  | load t q ih =>
    simp only [valid, Bool.and_eq_true] at hq
    obtain ⟨ht,hq⟩ := hq
    obtain ⟨hval,hbound⟩ := readUnary_valid ht v hv
    have hi := ih hq (readUnary states states t v) S T hbound hs hr
    simpa [finiteStmt, interpret, stepAux, hval] using hi
  | push k t q ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨⟨hk,ht⟩,hq⟩ := hq
    let i := clip ks k
    let z := readUnary states symbols t v
    have hidx : i.val = k := clip_val ks k (by omega)
    obtain ⟨hval,hbound⟩ := readUnary_valid ht v hv
    have hs' : Safe ks symbols (Function.update S i (z :: S i)) := by
      apply safe_update S hs i
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hbound
      · exact hs i x hx
    have hr' : StackRel ks symbols (Function.update S i (z :: S i))
        (Function.update T k (((lookup t v.val).getD 0) :: T k)) := by
      have h := rel_update S T hr i (z :: S i)
      have hz : z.val = (lookup t v.val).getD 0 := hval
      have hstack : (S i).map Fin.val = T k := by simpa [hidx] using (hr i).symm
      simpa [hidx, hz, hstack] using h
    have hi := ih hq v (Function.update S i (z :: S i))
      (Function.update T k (((lookup t v.val).getD 0) :: T k)) hv hs' hr'
    simpa [finiteStmt, interpret, stepAux, i, z] using hi
  | peek k t q ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨⟨hk,ht⟩,hq⟩ := hq
    let i := clip ks k
    have hidx : i.val = k := clip_val ks k (by omega)
    have hhead : (T k).head? = (S i).head?.map Fin.val := by simpa [hidx] using rel_head S T hr i
    obtain ⟨hval,hbound⟩ := readBinary_valid ht v (by simpa using hv) (S i).head? (safe_head S hs i)
    have hi := ih hq (readBinary states symbols t v (S i).head?) S T hbound hs hr
    simpa [finiteStmt, interpret, stepAux, i, hhead, hval] using hi
  | pop k t q ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨⟨hk,ht⟩,hq⟩ := hq
    let i := clip ks k
    have hidx : i.val = k := clip_val ks k (by omega)
    have hhead : (T k).head? = (S i).head?.map Fin.val := by simpa [hidx] using rel_head S T hr i
    obtain ⟨hval,hbound⟩ := readBinary_valid ht v hv (S i).head? (safe_head S hs i)
    have hs' : Safe ks symbols (Function.update S i (S i).tail) := by
      apply safe_update S hs i
      intro x hx
      exact hs i x (List.mem_of_mem_tail hx)
    have hr' : StackRel ks symbols (Function.update S i (S i).tail) (Function.update T k (T k).tail) := by
      have h := rel_update S T hr i (S i).tail
      have htail : ((S i).tail).map Fin.val = (T k).tail := by
        simpa [hidx] using (rel_tail S T hr i).symm
      simpa [hidx, htail] using h
    have hi := ih hq (readBinary states symbols t v (S i).head?) (Function.update S i (S i).tail)
      (Function.update T k (T k).tail) hbound hs' hr'
    simpa [finiteStmt, interpret, stepAux, i, hhead, hval] using hi
  | branch t a b iha ihb =>
    simp only [valid, Bool.and_eq_true] at hq
    obtain ⟨⟨ht,ha⟩,hb⟩ := hq
    obtain ⟨x,hx,hbound⟩ := unary_get ht hv
    have hcases : x = 0 ∨ x = 1 := by omega
    rcases hcases with rfl | rfl
    · have hi := ihb hb v S T hv hs hr
      simpa [finiteStmt, interpret, stepAux, readBool, hx] using hi
    · have hi := iha ha v S T hv hs hr
      simpa [finiteStmt, interpret, stepAux, readBool, hx] using hi

theorem stackFn_bounded {ks symbols : Nat} {s : Stacks} (hs : stacksValid ks symbols s)
    (k x : Nat) (hx : x ∈ stackFn s k) : x < symbols := by
  cases hk : s[k]? with
  | none => simp [stackFn, hk] at hx
  | some stk =>
    have hm : stk ∈ s := List.mem_of_getElem? hk
    have hx' : x ∈ stk := by simpa [stackFn, hk] using hx
    exact hs.2 stk hm x hx'

theorem safe_of_numeric {ks symbols : Nat} (S : FStacks ks symbols) (s : Stacks)
    (hs : stacksValid ks symbols s) (hr : StackRel ks symbols S (stackFn s)) : Safe ks symbols S := by
  intro k x hx
  have hm : x.val ∈ stackFn s k.val := by
    rw [hr k]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  exact stackFn_bounded hs k.val x.val hm

/-- Each validated numeric program block is mirrored by one finite-core TM2
step, retaining the original bounds and the full stack relation. -/
theorem finite_step (ks states symbols : Nat) (p : Program)
    (inputStack outputStack initialLabel initialState : Nat)
    (hp : programValid p ks states symbols = true)
    (c : (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).Cfg)
    (d : Result) (hc : resultValid ks states symbols p.length d)
    (hr : CfgRel ks states symbols p.length c (erase d))
    (l : Fin (p.length+1)) (hlabel : c.l = some l) :
    ∃ q c' r, p[l.val]? = some q ∧
      (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).step c = some c' ∧
      exec q d.state d.memory = some r ∧
      resultValid ks states symbols p.length r ∧ CfgRel ks states symbols p.length c' (erase r) := by
  have hlabel' : d.label = some l.val := by simpa [CfgRel, erase, hlabel] using hr.1
  have hstate : c.var.val < states := by
    have heq : d.state = c.var.val := hr.2.1
    rw [← heq]
    exact hc.1
  have hsafe : Safe ks symbols c.stk := safe_of_numeric c.stk d.memory hc.2.1 hr.2.2
  have hlt : l.val < p.length := hc.2.2 l.val hlabel'
  obtain ⟨q,hq,hqvalid⟩ := lookup_valid hp hlt
  obtain ⟨r,hexec,hvalid⟩ := exec_complete q ks states symbols p.length hqvalid d.state d.memory hc.1 hc.2.1
  have hblock := finite_stepAux ks states symbols p.length q hqvalid c.var c.stk (stackFn d.memory) hstate hsafe hr.2.2
  have hnum : stepAux (interpret q) c.var.val (stackFn d.memory) = erase r := by
    have heq : d.state = c.var.val := hr.2.1
    rw [← heq]
    exact exec_sound q d.state d.memory r hexec
  rw [hnum] at hblock
  let c' := stepAux (finiteStmt ks states symbols p.length q) c.var c.stk
  refine ⟨q,c',r,hq,?_,hexec,hvalid,hblock⟩
  · change Turing.TM2.step (finiteProgram ks states symbols p) c = some c'
    cases c with
    | mk label v S =>
      simp only at hlabel
      subst label
      simp [Turing.TM2.step, finiteProgram, hq, c']

/-- Construct a finite configuration from numeric data. The extra default
values keep the construction total even for unvalidated configurations. -/
def finiteConfig (ks states symbols labels : Nat) (d : Result) :
    Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1)) :=
  ⟨d.label.map (clip labels), clip states d.state,
    fun k => (stackFn d.memory k.val).map (clip symbols)⟩

/-- Valid numeric configurations have a related finite representation. -/
theorem finiteConfig_rel (ks states symbols labels : Nat) (d : Result)
    (hd : resultValid ks states symbols labels d) :
    CfgRel ks states symbols labels (finiteConfig ks states symbols labels d) (erase d) := by
  refine ⟨?_, ?_, ?_⟩
  · cases hl : d.label with
    | none => simp [finiteConfig, erase, hl]
    | some l =>
      have hlt : l < labels := hd.2.2 l hl
      simp [finiteConfig, erase, hl, clip_val labels l (by omega)]
  · simpa [finiteConfig, erase] using (clip_val states d.state (by have := hd.1; omega)).symm
  · intro k
    simp only [finiteConfig, erase, List.map_map]
    conv_lhs => rw [← List.map_id (stackFn d.memory k.val)]
    apply List.map_congr_left
    intro x hx
    exact (clip_val symbols x (by have := stackFn_bounded hd.2.1 k.val x hx; omega)).symm

open Shared.ComplexityBridge.TM2Symbols

/-- A bounded numeric execution is related to an execution of the finite
core, counting complete TM2 blocks. Invalid outcomes are excluded. -/
def finiteOutcome (ks states symbols : Nat) (p : Program)
    (inputStack outputStack initialLabel initialState fuel : Nat)
    (c : (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).Cfg) : Outcome → Prop
  | .invalid => False
  | .timeout r => ∃ c', runSteps (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).step fuel c = some c' ∧
      CfgRel ks states symbols p.length c' (erase r)
  | .halted r => ∃ n ≤ fuel, ∃ c', runSteps (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).step n c = some c' ∧
      CfgRel ks states symbols p.length c' (erase r) ∧ c'.l = none

/-- The finite core mirrors a validated bounded run with the same block count,
with early termination represented explicitly. -/
theorem finite_run (ks states symbols : Nat) (p : Program)
    (inputStack outputStack initialLabel initialState : Nat)
    (hp : programValid p ks states symbols = true) (fuel : Nat)
    (c : (finiteCore ks states symbols p inputStack outputStack initialLabel initialState).Cfg)
    (d : Result) (hc : resultValid ks states symbols p.length d)
    (hr : CfgRel ks states symbols p.length c (erase d)) :
    finiteOutcome ks states symbols p inputStack outputStack initialLabel initialState fuel c (run p fuel d) := by
  induction fuel generalizing c d with
  | zero =>
    cases hl : c.l with
    | none =>
      have hd : d.label = none := by simpa [CfgRel, erase, hl, Option.map] using hr.1
      simp only [run, hd, Option.isNone_none, ↓reduceIte, finiteOutcome]
      exact ⟨0, Nat.le_refl 0, c, rfl, hr, hl⟩
    | some l =>
      have hd : d.label = some l.val := by simpa [CfgRel, erase, hl, Option.map] using hr.1
      simp only [run, hd, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, finiteOutcome]
      exact ⟨c, rfl, hr⟩
  | succ n ih =>
    cases hl : c.l with
    | none =>
      have hd : d.label = none := by simpa [CfgRel, erase, hl, Option.map] using hr.1
      simp only [run, hd, finiteOutcome]
      exact ⟨0, Nat.zero_le _, c, rfl, hr, hl⟩
    | some l =>
      have hd : d.label = some l.val := by simpa [CfgRel, erase, hl, Option.map] using hr.1
      obtain ⟨q,c',r,hq,hs,he,hvalid,hrel⟩ := finite_step ks states symbols p inputStack outputStack initialLabel initialState hp c d hc hr l hl
      have h := ih c' r hvalid hrel
      have hh : finiteOutcome ks states symbols p inputStack outputStack initialLabel initialState (n+1) c (run p n r) := by
        cases hout : run p n r with
        | invalid => simp [hout, finiteOutcome] at h
        | timeout u =>
          simp only [hout, finiteOutcome] at h ⊢
          obtain ⟨c'', hsteps, hrel'⟩ := h
          refine ⟨c'', ?_, hrel'⟩
          rw [runSteps_front, hs]
          exact hsteps
        | halted u =>
          simp only [hout, finiteOutcome] at h ⊢
          obtain ⟨j, hj, c'', hsteps, hrel', hhalt⟩ := h
          refine ⟨j+1, by omega, c'', ?_, hrel', hhalt⟩
          rw [runSteps_front, hs]
          exact hsteps
      simpa [run, hd, hq, he] using hh

/-- A validated numeric start always has a concrete finite-core run relation;
no externally supplied configuration relation is needed. -/
theorem finite_run_from_config (ks states symbols : Nat) (p : Program)
    (inputStack outputStack initialLabel initialState : Nat)
    (hp : programValid p ks states symbols = true) (fuel : Nat)
    (d : Result) (hd : resultValid ks states symbols p.length d) :
    finiteOutcome ks states symbols p inputStack outputStack initialLabel initialState fuel
      (finiteConfig ks states symbols p.length d) (run p fuel d) :=
  finite_run ks states symbols p inputStack outputStack initialLabel initialState hp fuel
    (finiteConfig ks states symbols p.length d) d hd (finiteConfig_rel ks states symbols p.length d hd)

end Shared.ComplexityBridge.TM2FiniteReverse
