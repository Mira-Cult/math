import Shared.Codes.FinitePrograms
import Shared.Codes.TM2ProgramHalt
import Shared.Codes.FiniteProgramLink
import Shared.ComplexityBridge.FiniteVerifierCompiler
import Shared.ComplexityBridge.FiniteProgramRepairBridge

/-! A finite TM2 simulation of the shared finite-program evaluator. The two
working stackVals represent the cells to the left of the head and the current
cell followed by cells to its right. Source steps are complete TM2 statement
blocks, not primitive stack operations. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.FiniteProgramTM2
open Turing.TM2
open Shared.Codes.FinitePrograms Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program (runSteps_front runSteps_add)

inductive Stack where | left | right | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.left,.right,.output] (by intro s; cases s <;> simp)
inductive Label where | init | work | clearLeft | clearRight | bad deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.init,.work,.clearLeft,.clearRight,.bad] (by intro l; cases l <;> simp)

abbrev State (p : Program) := Fin (p.length+1) × Bool × Bool

def clip (p : Program) (n : Nat) : Fin (p.length+1) :=
  if h : n < p.length+1 then ⟨n,h⟩ else ⟨p.length,by omega⟩

@[simp] theorem clip_val (p : Program) (n : Nat) (h : n < p.length+1) : (clip p n).val = n := by simp [clip,h]

def selected (p : Program) (v : State p) : Option Row :=
  (p[v.1.val]?).map (fun rows => if v.2.1 then rows.2 else rows.1)

def next (p : Program) (v : State p) : Row :=
  (selected p v).getD (false,false,0,3)

def statement (p : Program) : Label → Stmt (fun _ : Stack => Bool) Label (State p)
  | .init => .peek .right (fun v h => (v.1,v.2.1,h.isSome))
      (.branch (fun v => v.2.2) (.load (fun v => (v.1,false,false)) (.goto (fun _ => .work)))
        (.push .right (fun _ => false) (.goto (fun _ => .work))))
  | .work => .pop .right (fun v h => (v.1,h.getD false,false))
      (.branch (fun v => (next p v).2.2.2 == 0)
        (.branch (fun v => (next p v).2.1)
          (.push .left (fun v => (next p v).1)
            (.load (fun v => (clip p (next p v).2.2.1,false,false))
              (.peek .right (fun v h => (v.1,false,h.isSome))
                (.branch (fun v => v.2.2)
                  (.load (fun v => (v.1,false,false)) (.goto (fun _ => .work)))
                  (.push .right (fun _ => false)
                    (.load (fun v => (v.1,false,false)) (.goto (fun _ => .work))))))))
          (.pop .left (fun v h => (v.1,v.2.1,h.getD false))
            (.push .right (fun v => (next p v).1)
              (.push .right (fun v => v.2.2)
                (.load (fun v => (clip p (next p v).2.2.1,false,false)) (.goto (fun _ => .work)))))))
        (.branch (fun v => (next p v).2.2.2 == 1 || (next p v).2.2.2 == 2)
          (.load (fun v => (clip p 0,(next p v).2.2.2 == 2,false)) (.goto (fun _ => .clearLeft)))
          (.goto (fun _ => .bad))))
  | .clearLeft => .peek .left (fun v h => (v.1,v.2.1,h.isSome))
      (.branch (fun v => v.2.2)
        (.pop .left (fun v _ => v) (.goto (fun _ => .clearLeft)))
        (.goto (fun _ => .clearRight)))
  | .clearRight => .peek .right (fun v h => (v.1,v.2.1,h.isSome))
      (.branch (fun v => v.2.2)
        (.pop .right (fun v _ => v) (.goto (fun _ => .clearRight)))
        (.push .output (fun v => v.2.1)
          (.load (fun _ => (clip p 0,false,false)) .halt)))
  | .bad => .goto (fun _ => .bad)

def machine (p : Program) : Turing.FinTM2 where
  K := Stack
  k₀ := .right
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .init
  σ := State p
  initialState := (clip p 0,false,false)
  m := statement p

def stackVals (L R O : List Bool) : Stack → List Bool
  | .left => L | .right => R | .output => O

def cfg (p : Program) (l : Label) (v : State p) (L R O : List Bool) : (machine p).Cfg :=
  ⟨some l,v,stackVals L R O⟩

def simCfg (p : Program) (q : Nat) (L : List Bool) (b : Bool) (R : List Bool) : (machine p).Cfg :=
  cfg p .work (clip p q,false,false) L (b::R) []

theorem initial_eq (p : Program) (xs : List Bool) :
    Turing.initList (machine p) xs = cfg p .init (clip p 0,false,false) [] xs [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ (stackVals [] xs [])
  congr 1; funext k; cases k <;> rfl

theorem init_step (p : Program) (xs : List Bool) :
    (machine p).step (Turing.initList (machine p) xs) =
      some (simCfg p 0 [] (xs.head?.getD false) xs.tail) := by
  rw [initial_eq]
  cases xs <;>
    simp [machine, Turing.FinTM2.step, Turing.TM2.step, statement, stepAux,
      simCfg, cfg, stackVals, Function.update] <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

/-- A successful continuing row is simulated in exactly one TM2 block.
The target next-state index must fit the finite control; this follows from
the table-validity invariant for reachable source runs. -/
theorem work_continue (p : Program) (q q' : Nat) (L R : List Bool) (b w dir : Bool)
    (hr : selected p (clip p q,b,false) = some (w,dir,q',0)) :
    (machine p).step (simCfg p q L b R) =
      some (simCfg p q' (moveTape (!dir) w (L,b,R)).1
        (moveTape (!dir) w (L,b,R)).2.1 (moveTape (!dir) w (L,b,R)).2.2) := by
  have hrs (z : Bool) : selected p (clip p q,b,z) = some (w,dir,q',0) := by
    simpa [selected] using hr
  cases dir <;> cases L <;> cases R <;>
    simp [machine, Turing.FinTM2.step, Turing.TM2.step, statement, stepAux, simCfg, cfg, stackVals,
      next, hrs, moveTape, Function.update] <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem work_result (p : Program) (q : Nat) (L R : List Bool) (b w dir result : Bool) (q' : Nat)
    (hr : selected p (clip p q,b,false) = some (w,dir,q',if result then 2 else 1)) :
    (machine p).step (simCfg p q L b R) =
      some (cfg p .clearLeft (clip p 0,result,false) L R []) := by
  cases result <;>
    simp [machine, Turing.FinTM2.step, Turing.TM2.step, statement, stepAux, simCfg, cfg, stackVals,
      next, hr, Function.update] <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]


theorem clearLeft_cons (p : Program) (out flag b : Bool) (L R : List Bool) :
    (machine p).step (cfg p .clearLeft (clip p 0,out,flag) (b::L) R []) =
      some (cfg p .clearLeft (clip p 0,out,true) L R []) := by
  simp [machine, Turing.FinTM2.step, Turing.TM2.step, statement, stepAux, cfg, stackVals]
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clearLeft_nil (p : Program) (out flag : Bool) (R : List Bool) :
    (machine p).step (cfg p .clearLeft (clip p 0,out,flag) [] R []) =
      some (cfg p .clearRight (clip p 0,out,false) [] R []) := by
  rfl

theorem clearRight_cons (p : Program) (out flag b : Bool) (R : List Bool) :
    (machine p).step (cfg p .clearRight (clip p 0,out,flag) [] (b::R) []) =
      some (cfg p .clearRight (clip p 0,out,true) [] R []) := by
  simp [machine, Turing.FinTM2.step, Turing.TM2.step, statement, stepAux, cfg, stackVals]
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem clearRight_nil (p : Program) (out flag : Bool) :
    (machine p).step (cfg p .clearRight (clip p 0,out,flag) [] [] []) =
      some (Turing.haltList (machine p) [out]) := by
  change some (Cfg.mk (none : Option Label) (clip p 0,false,false)
    (Function.update (stackVals [] [] []) .output [out])) = _
  congr 1; congr 1; funext k; cases k <;> rfl

theorem clearRight_run (p : Program) (out flag : Bool) (R : List Bool) :
    runSteps (machine p).step (R.length+1) (cfg p .clearRight (clip p 0,out,flag) [] R []) =
      some (Turing.haltList (machine p) [out]) := by
  induction R generalizing flag with
  | nil =>
    change (machine p).step (cfg p .clearRight (clip p 0,out,flag) [] [] []) = _
    exact clearRight_nil p out flag
  | cons b R ih =>
    rw [List.length_cons,show R.length+1+1 = (R.length+1)+1 by omega,runSteps_front,clearRight_cons]
    exact ih true

theorem clearLeft_run (p : Program) (out flag : Bool) (L R : List Bool) :
    runSteps (machine p).step (L.length+R.length+2)
      (cfg p .clearLeft (clip p 0,out,flag) L R []) =
      some (Turing.haltList (machine p) [out]) := by
  induction L generalizing flag with
  | nil =>
    rw [List.length_nil,zero_add,show R.length+2 = (R.length+1)+1 by omega,runSteps_front,clearLeft_nil]
    exact clearRight_run p out false R
  | cons b L ih =>
    rw [List.length_cons,show L.length+1+R.length+2 = (L.length+R.length+2)+1 by omega,
      runSteps_front,clearLeft_cons]
    exact ih true


/-- Canonical target boundary for a finite-program configuration. -/
def encodeCfg (p : Program) (c : Config) : (machine p).Cfg :=
  simCfg p c.1 c.2.1 c.2.2.1 c.2.2.2

theorem selected_row (p : Program) (c : Config) (hc : c.1 < p.length) :
    selected p (clip p c.1,c.2.2.1,false) = rowAt p c := by
  simp [selected,rowAt,clip_val p c.1 (by omega)]

theorem continue_step (p : Program) (c d : Config) (hc : c.1 < p.length)
    (h : Shared.Codes.FinitePrograms.step p c = some (.inr d)) :
    (machine p).step (encodeCfg p c) = some (encodeCfg p d) := by
  obtain ⟨q,L,b,R⟩ := c
  have hp : p[q]? = some p[q] := List.getElem?_eq_getElem hc
  let row : Row := if b then p[q].2 else p[q].1
  have hr : rowAt p (q,L,b,R) = some row := by simp [rowAt,hp,row]
  have hs : selected p (clip p q,b,false) = some row := by simpa using (selected_row p (q,L,b,R) hc).trans hr
  rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow p _ row hr] at h
  rcases row with ⟨w,dir,q',tag⟩
  cases tag with
  | zero =>
    simp only [executeRow,Option.some.injEq,Sum.inr.injEq] at h
    subst d
    exact work_continue p q q' L R b w dir hs
  | succ tag => cases tag with
    | zero => simp [executeRow] at h
    | succ tag => cases tag with
      | zero => simp [executeRow] at h
      | succ tag => simp [executeRow] at h

/-- Any in-range continuing source prefix is simulated at equal block count. -/
theorem run_continuing (p : Program) (hv : valid p = true) (c d : Config)
    (hc : c.1 < p.length) (n : Nat)
    (h : Shared.Codes.FinitePrograms.run p c n = some (.inr d)) :
    runSteps (machine p).step n (encodeCfg p c) = some (encodeCfg p d) := by
  induction n generalizing d with
  | zero =>
    simp only [run_zero,Option.some.injEq,Sum.inr.injEq] at h
    subst d
    rfl
  | succ n ih =>
    have hrange := Shared.Codes.FiniteProgramLink.run_in_range p hv c hc n
    simp only [run_succ] at h
    cases hr : Shared.Codes.FinitePrograms.run p c n with
    | none => simp [hr,advance] at h
    | some st =>
      cases st with
      | inl b => simp [hr,advance] at h
      | inr prev =>
        have hprev : prev.1 < p.length := by simpa [hr,Shared.Codes.FiniteProgramLink.InRange] using hrange
        have hstep : Shared.Codes.FinitePrograms.step p prev = some (.inr d) := by simpa [hr,advance] using h
        have hs := continue_step p prev d hprev hstep
        simp only [runSteps,ih prev hr,Option.bind_some,hs]


/-- Total represented tape size; the head cell is always explicit. -/
def tapeSize (c : Config) : Nat := c.2.1.length + c.2.2.2.length + 1

theorem moveTape_size (dir w b : Bool) (L R : List Bool) :
    (moveTape dir w (L,b,R)).1.length + (moveTape dir w (L,b,R)).2.2.length + 1 ≤
      L.length + R.length + 2 := by
  cases dir <;> cases L <;> cases R <;> simp [moveTape] <;> omega

theorem continue_size (p : Program) (c d : Config)
    (h : Shared.Codes.FinitePrograms.step p c = some (.inr d)) :
    tapeSize d ≤ tapeSize c + 1 := by
  obtain ⟨q,L,b,R⟩ := c
  cases hp : p[q]? with
  | none => simp [Shared.Codes.FinitePrograms.step,hp] at h
  | some pair =>
    let row := if b then pair.2 else pair.1
    have hr : rowAt p (q,L,b,R) = some row := by simp [rowAt,hp,row]
    rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow p _ row hr] at h
    rcases row with ⟨w,dir,q',tag⟩
    cases tag with
    | zero =>
      simp only [executeRow,Option.some.injEq,Sum.inr.injEq] at h
      subst d
      exact moveTape_size (!dir) w b L R
    | succ tag => cases tag with
      | zero => simp [executeRow] at h
      | succ tag => cases tag with
        | zero => simp [executeRow] at h
        | succ tag => simp [executeRow] at h

theorem run_continuing_size (p : Program) (c d : Config) (n : Nat)
    (h : Shared.Codes.FinitePrograms.run p c n = some (.inr d)) :
    tapeSize d ≤ tapeSize c + n := by
  induction n generalizing d with
  | zero => simp only [run_zero,Option.some.injEq,Sum.inr.injEq] at h; subst d; omega
  | succ n ih =>
    simp only [run_succ] at h
    cases hr : Shared.Codes.FinitePrograms.run p c n with
    | none => simp [hr,advance] at h
    | some st => cases st with
      | inl b => simp [hr,advance] at h
      | inr prev =>
        have hs : Shared.Codes.FinitePrograms.step p prev = some (.inr d) := by simpa [hr,advance] using h
        have hg := continue_size p prev d hs
        have hi := ih prev hr
        omega

theorem result_step (p : Program) (c : Config) (result : Bool) (hc : c.1 < p.length)
    (h : Shared.Codes.FinitePrograms.step p c = some (.inl result)) :
    ∃ L R, (machine p).step (encodeCfg p c) =
      some (cfg p .clearLeft (clip p 0,result,false) L R []) ∧
      L.length+R.length+1 = tapeSize c := by
  obtain ⟨q,L,b,R⟩ := c
  have hp : p[q]? = some p[q] := List.getElem?_eq_getElem hc
  let row : Row := if b then p[q].2 else p[q].1
  have hr : rowAt p (q,L,b,R) = some row := by simp [rowAt,hp,row]
  have hs : selected p (clip p q,b,false) = some row := by simpa using (selected_row p (q,L,b,R) hc).trans hr
  rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow p _ row hr] at h
  rcases row with ⟨w,dir,q',tag⟩
  cases tag with
  | zero => simp [executeRow] at h
  | succ tag => cases tag with
    | zero =>
      simp [executeRow] at h
      subst result
      exact ⟨L,R,work_result p q L R b w dir false q' hs,rfl⟩
    | succ tag => cases tag with
      | zero =>
        simp [executeRow] at h
        subst result
        exact ⟨L,R,work_result p q L R b w dir true q' hs,rfl⟩
      | succ tag => simp [executeRow] at h


/-- The first successful source result has a continuing predecessor. -/
theorem result_prefix (p : Program) (input : List Bool) (fuel : Nat) (b : Bool)
    (h : bounded p input fuel = some b) :
    ∃ n < fuel, ∃ c, Shared.Codes.FinitePrograms.run p (initial input) n = some (.inr c) ∧
      Shared.Codes.FinitePrograms.step p c = some (.inl b) := by
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result p input fuel b).1 h
  have hex : ∃ k, Shared.Codes.FinitePrograms.run p (initial input) k = some (.inl b) := ⟨t,hr⟩
  let first := Nat.find hex
  have hfirst : Shared.Codes.FinitePrograms.run p (initial input) first = some (.inl b) := Nat.find_spec hex
  have hle : first ≤ fuel := le_trans (Nat.find_min' hex hr) ht
  cases hf : first with
  | zero => simp [hf] at hfirst
  | succ n =>
    have hn : n < fuel := by omega
    have hlast : Shared.Codes.FinitePrograms.run p (initial input) (n+1) = some (.inl b) := by simpa [hf] using hfirst
    rw [run_succ] at hlast
    cases hp : Shared.Codes.FinitePrograms.run p (initial input) n with
    | none => simp [hp,advance] at hlast
    | some value => cases value with
      | inl b' =>
        have hb : b' = b := by simpa [hp,advance] using hlast
        subst b'
        have hmin := Nat.find_min hex (m := n) (by omega)
        exact False.elim (hmin hp)
      | inr c => exact ⟨n,hn,c,hp,by simpa [hp,advance] using hlast⟩

theorem initial_size (input : List Bool) : tapeSize (initial input) ≤ input.length+1 := by
  cases input <;> simp [tapeSize,initial] <;> omega

/-- Successful finite-program evaluation is simulated with one initial block,
one block per table transition, and a charged linear cleanup. -/
theorem bounded_simulation (p : Program) (hv : valid p = true) (input : List Bool)
    (fuel : Nat) (b : Bool) (h : bounded p input fuel = some b) :
    ∃ t ≤ input.length + 2*fuel + 4,
      runSteps (machine p).step t (Turing.initList (machine p) input) =
        some (Turing.haltList (machine p) [b]) := by
  obtain ⟨n,hn,c,hc,hs⟩ := result_prefix p input fuel b h
  have hq : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hv
  have hcrange := Shared.Codes.FiniteProgramLink.run_in_range p hv (initial input) (by simpa [initial] using hq) n
  have hcq : c.1 < p.length := by simpa [hc,Shared.Codes.FiniteProgramLink.InRange] using hcrange
  obtain ⟨L,R,hstep,hsize⟩ := result_step p c b hcq hs
  have hrun := run_continuing p hv (initial input) c (by simpa [initial] using hq) n hc
  have hgrowth := run_continuing_size p (initial input) c n hc
  have hi := initial_size input
  let time := 1+n+1+(L.length+R.length+2)
  refine ⟨time,?_,?_⟩
  · dsimp [time]; omega
  · change runSteps (machine p).step (1+n+1+(L.length+R.length+2))
      (Turing.initList (machine p) input) = _
    rw [show 1+n+1+(L.length+R.length+2) = 1+(n+(1+(L.length+R.length+2))) by omega,
      runSteps_add]
    change ((machine p).step (Turing.initList (machine p) input)).bind _ = _
    rw [init_step]
    change runSteps (machine p).step (n+(1+(L.length+R.length+2))) (encodeCfg p (initial input)) = _
    rw [runSteps_add,hrun]
    change runSteps (machine p).step (1+(L.length+R.length+2)) (encodeCfg p c) = _
    rw [runSteps_add]
    change ((machine p).step (encodeCfg p c)).bind _ = _
    rw [hstep]
    exact clearLeft_run p b false L R


/-- A fixed valid finite table with a polynomial clock gives a canonical TM2
machine, including the input and cleaned Boolean output boundaries. -/
noncomputable def polyTimeMachine {α : Type} [BitstringEncoding α] (p : Program) (clock : Polynomial Nat)
    (f : α → Bool) (hv : valid p = true)
    (correct : ∀ x, bounded p (BitstringEncoding.bitEncode x)
      (clock.eval (BitstringEncoding.bitEncode x).length) = some (f x)) :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α → List Bool)
      (BitstringEncoding.bitEncode : Bool → List Bool) f where
  tm := machine p
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + Polynomial.C 2 * clock + Polynomial.C 4
  outputsFun x := by
    let hex := bounded_simulation p hv (BitstringEncoding.bitEncode x)
      (clock.eval (BitstringEncoding.bitEncode x).length) (f x) (correct x)
    let t := Classical.choose hex
    have ht := (Classical.choose_spec hex).1
    have hr := (Classical.choose_spec hex).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind (machine p).step)^[t]
        (some (Turing.initList (machine p) ((BitstringEncoding.bitEncode x).map id))) =
        some (Turing.haltList (machine p) ((BitstringEncoding.bitEncode (f x)).map id))
      rw [List.map_id,List.map_id]
      change (fun o => o.bind (machine p).step)^[t]
        (some (Turing.initList (machine p) (BitstringEncoding.bitEncode x))) =
        some (Turing.haltList (machine p) [f x])
      exact hr
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      exact ht

theorem finite_isPolyTime {α : Type} [BitstringEncoding α] (p : Program) (clock : Polynomial Nat)
    (f : α → Bool) (hv : valid p = true)
    (correct : ∀ x, bounded p (BitstringEncoding.bitEncode x)
      (clock.eval (BitstringEncoding.bitEncode x).length) = some (f x)) :
    ComplexityTheory.IsPolyTime f := ⟨polyTimeMachine p clock f hv correct⟩

/-- For canonical polynomial-time Boolean pair relations, both directions
are now connected to the same finite binary-table evaluator and encoding. -/
theorem canonical_pair_iff_finite (R : (List Bool × List Bool) → Bool) :
    ComplexityTheory.IsPolyTime R ↔
      ∃ (p : Program) (clock : Polynomial Nat), valid p = true ∧ ∀ x w,
        bounded p (BitstringEncoding.bitEncode (x,w))
          (clock.eval (BitstringEncoding.bitEncode (x,w)).length) = some (R (x,w)) := by
  constructor
  · intro h
    exact (Shared.ComplexityBridge.FiniteProgramRepairBridge.finiteVerifierCompiler_iff_valid).mp
      Shared.ComplexityBridge.FiniteVerifierCompiler.canonical_finite_verifier_compiler R h
  · rintro ⟨p,clock,hv,h⟩
    apply finite_isPolyTime p clock R hv
    rintro ⟨x,w⟩
    exact h x w


namespace Fixtures
/-- The two possible input symbols return different Boolean values. -/
def readOnce : Program := [((false,false,0,1),(false,false,0,2))]

example : valid readOnce = true := by decide
example : bounded readOnce [] 0 = none := by decide
example : bounded readOnce [] 1 = some false := by decide
example : bounded readOnce [true] 1 = some true := by decide
example : ∃ t ≤ 6, runSteps (machine readOnce).step t (Turing.initList (machine readOnce) []) =
    some (Turing.haltList (machine readOnce) [false]) := by
  simpa using bounded_simulation readOnce (by decide) [] 1 false (by decide)
example : ∃ t ≤ 7, runSteps (machine readOnce).step t (Turing.initList (machine readOnce) [true]) =
    some (Turing.haltList (machine readOnce) [true]) := by
  simpa using bounded_simulation readOnce (by decide) [true] 1 true (by decide)

/-- A right move reaches an unrepresented blank, then the second row returns. -/
def rightBlank : Program := [((true,true,1,0),(true,true,1,0)),
  ((false,false,0,1),(false,false,0,2))]
example : valid rightBlank = true := by decide
example : bounded rightBlank [] 1 = none := by decide
example : bounded rightBlank [] 2 = some false := by decide
example : ∃ t ≤ 8, runSteps (machine rightBlank).step t (Turing.initList (machine rightBlank) []) =
    some (Turing.haltList (machine rightBlank) [false]) := by
  simpa using bounded_simulation rightBlank (by decide) [] 2 false (by decide)
/-- A left move from the origin also materializes an implicit blank. -/
def leftBlank : Program := [((true,false,1,0),(true,false,1,0)),
  ((false,false,0,2),(false,false,0,1))]
example : valid leftBlank = true := by decide
example : bounded leftBlank [] 1 = none := by decide
example : bounded leftBlank [] 2 = some true := by decide
example : ∃ t ≤ 8, runSteps (machine leftBlank).step t (Turing.initList (machine leftBlank) []) =
    some (Turing.haltList (machine leftBlank) [true]) := by
  simpa using bounded_simulation leftBlank (by decide) [] 2 true (by decide)
end Fixtures

end Shared.ComplexityBridge.FiniteProgramTM2
