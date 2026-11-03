import Shared.Codes.FiniteProgramPhaseProbe
set_option maxHeartbeats 3000000

/-! A six-phase controller whose interior probe outcome returns to state zero.
Its boundary outcome is still a terminal fixture for a future finalizer. -/
namespace Shared.Codes.FiniteProgramFirstBlocksController
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramPhaseProbe (phases phases_valid phases_length stride probe probe_segment dummy)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.PairReverseFirst (expanded)

def base (zero one : List Bool) : Program := phases zero one 6
def interior (zero one : List Bool) : Nat := 6*stride zero one+3
def boundary (zero one : List Bool) : Nat := 6*stride zero one+2

def program (zero one : List Bool) : Program :=
  let p := base zero one
  p.set (interior zero one) (branch p.length) ++ [bridge 0]

theorem base_length (zero one : List Bool) : (base zero one).length = 6*stride zero one+4 := by
  simp [base,phases_length,probe,Shared.Codes.FiniteProgramFirstBlockProbe.program]

theorem interior_bound (zero one : List Bool) : interior zero one < (base zero one).length := by
  simp [interior,base_length]

theorem base_stop (zero one : List Bool) (t : Tape) :
    step (base zero one) (interior zero one,t) = some (.inl false) := by
  have hc : ((3,t) : Config).1 < probe.length := by simp [probe,Shared.Codes.FiniteProgramFirstBlockProbe.program]
  have h := probe_segment zero one 6 (3,t) hc 1
  have hl : run probe (3,t) 1 = some (.inl false) := by
    cases ht : t.2.1 <;> simp [run,advance,step,probe,Shared.Codes.FiniteProgramFirstBlockProbe.program,dummy,ht]
  rw [hl] at h
  simpa [base,interior,shiftConfig,shiftStatus,run,advance] using h

theorem base_other (zero one : List Bool) (d : Config)
    (hd : d.1 < (base zero one).length) (hne : d.1 ≠ interior zero one) :
    step (base zero one) d = step (program zero one) d := by
  have hlookup : (program zero one)[d.1]? = (base zero one)[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,hlookup]

theorem interior_row (zero one : List Bool) :
    (program zero one)[interior zero one]? = some (branch (base zero one).length) := by
  have hs := interior_bound zero one
  simp [program,List.getElem?_append_left,hs]

theorem bridge_row (zero one : List Bool) :
    (program zero one)[(base zero one).length]? = some (bridge 0) := by simp [program]

theorem restart (zero one : List Bool) (b : Bool) (L R : List Bool) :
    run (program zero one) (interior zero one,tapeAt L (b::false::R)) 2 =
      some (.inr (0,tapeAt L (b::false::R))) := by
  have hs := interior_row zero one
  have hb := bridge_row zero one
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape]

/-- The patched table is valid for every fixed pair of code words. -/
theorem program_valid (zero one : List Bool) : valid (program zero one) = true := by
  let p := base zero one
  let m := p.length+1
  have hm : (program zero one).length = m := by simp [program,m,p]
  have hold : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    have hv := phases_valid zero one 6
    change valid p = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hbound : p.length ≤ m := by simp [m]
  have hp : ∀ r ∈ p.set (interior zero one) (branch p.length),
      validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with ho | he
    · obtain ⟨h₁,h₂⟩ := hold r ho
      exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₁,
        Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₂⟩
    · subst r
      have hb : p.length < m := by simp [m]
      simp [branch,validRow,hb]
  have hb : validRow m (bridge 0).1 = true ∧ validRow m (bridge 0).2 = true := by
    have hmpos : 0 < m := by simp [m]
    simp [bridge,validRow,hmpos]
  have hall : (program zero one).all
      (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ p.set (interior zero one) (branch p.length) ∨ r = bridge 0 := by
      simpa [program,p,List.mem_append] using hr
    rw [hm]
    rcases hr' with hp' | hb'
    · simpa only [Bool.and_eq_true] using hp r hp'
    · subst r; simpa only [Bool.and_eq_true] using hb
  have hn : (program zero one).isEmpty = false := by simp [program]
  change (!(program zero one).isEmpty && (program zero one).all
    (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2)) = true
  rw [hn,hall]
  rfl

-- The constructor-name linter exhausts its fixed heartbeat budget on this
-- dependent type; disabling it here does not affect kernel checking.
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- A phase-aligned group of six cycles either reaches the untouched
boundary row or returns to state zero when an earlier block exists. The
interior return uses two additional concrete table transitions. -/
theorem run_group (zero one : List Bool) (ps : List Bool) (hps : ps.length = 5) (b : Bool)
    (xs remaining L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((ps++[false]) ++ ((expanded remaining).reverse ++ false::false::L).tail) b xs).2) :
    let right := false::Shared.Codes.FiniteProgramBitShuttle.tagged (result zero one (ps++[false]) b xs).2 ++ [false,false,false]
    let source := (expanded remaining).reverse ++ false::false::L
    ∃ d, run (program zero one) c
        (totalCost zero one (ps++[false]) b xs+2+(if remaining.isEmpty then 0 else 2)) = some (.inr d) ∧
      d.1 = (if remaining.isEmpty then boundary zero one else 0) ∧ TapeRel d.2 (tapeLeft source right) := by
  dsimp only
  let right := false::Shared.Codes.FiniteProgramBitShuttle.tagged (result zero one (ps++[false]) b xs).2 ++ [false,false,false]
  let source := (expanded remaining).reverse ++ false::false::L
  let t := tapeLeft source right
  let duration := totalCost zero one (ps++[false]) b xs+2
  obtain ⟨mid,hm,hmid,htape⟩ := Shared.Codes.FiniteProgramPhaseProbe.six_to_boundary
    zero one ps hps b xs remaining L c hq ht
  have hc : c.1 < (base zero one).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _ (phases_valid zero one 6)
  have hp := Shared.Codes.FiniteProgramFirstEntry.first_entry
    (base zero one) (program zero one) c mid duration (interior zero one) false
    (phases_valid zero one 6) hc (base_stop zero one) (base_other zero one) hm
  cases he : remaining.isEmpty with
  | true =>
    have hd : mid.1 = boundary zero one := by simpa [he,boundary] using hmid
    refine ⟨mid,?_,?_,htape⟩
    · simpa [he,duration] using hp
    · simpa [he] using hd
  | false =>
    have hd : mid.1 = interior zero one := by simpa [he,interior] using hmid
    have hhead : source.head?.getD false = false :=
      Shared.Codes.FiniteProgramFirstBlockProbe.first_component_head remaining L
    have hshape : t = tapeAt source.tail (false::false::(Shared.Codes.FiniteProgramBitShuttle.tagged
        (result zero one (ps++[false]) b xs).2 ++ [false,false,false])) := by
      simp [t,tapeLeft,tapeAt,hhead,right,List.cons_append]
    have hrestart := restart zero one false source.tail
      (Shared.Codes.FiniteProgramBitShuttle.tagged (result zero one (ps++[false]) b xs).2 ++ [false,false,false])
    rw [← hshape] at hrestart
    have hrel := run_related (program zero one) mid (interior zero one,t) (by simpa using hd) htape 2
    rw [hrestart] at hrel
    cases hr : run (program zero one) mid 2 with
    | none => rw [hr] at hrel; exact False.elim hrel
    | some v => cases v with
      | inl out => rw [hr] at hrel; exact False.elim hrel
      | inr d =>
        rw [hr] at hrel
        have hdone : d.1 = 0 ∧ TapeRel d.2 t := hrel
        refine ⟨d,?_,?_,hdone.2⟩
        · simp only [Bool.false_eq_true,reduceIte]
          change run (program zero one) c (duration+2) = some (.inr d)
          rw [run_continue _ _ _ _ _ hp]
          exact hr
        · simpa [he] using hdone.1

def pred (b : Bool) : List Bool := [true,b,true,true,true,false]

def groupOutput (zero one : List Bool) (b : Bool) (xs : List Bool) : List Bool :=
  (result zero one (pred b) false xs).2

def groupCost (zero one : List Bool) (earlier : List Bool) (b : Bool) (xs : List Bool) : Nat :=
  totalCost zero one (pred b) false xs+2+(if earlier.isEmpty then 0 else 2)

def boundaryTape (remaining xs L : List Bool) : Tape :=
  tapeLeft ((expanded remaining).reverse ++ false::false::L)
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false])

theorem source_cons (remaining L : List Bool) :
    let source := (expanded remaining).reverse ++ false::false::L
    false::source.tail = source := by
  dsimp only
  let source := (expanded remaining).reverse ++ false::false::L
  have hn : source ≠ [] := by simp [source]
  have hh : source.head?.getD false = false :=
    Shared.Codes.FiniteProgramFirstBlockProbe.first_component_head remaining L
  cases he : source with
  | nil => exact False.elim (hn he)
  | cons a as =>
    simp [he] at hh
    subst a
    change false::source.tail = source
    rw [he]
    rfl

/-- The actual six-bit block supplies the five phase bits and final false
predecessor required by `run_group`. -/
theorem aligned (earlier : List Bool) (b : Bool) (xs L : List Bool) :
    (canonical (([true,b,true,true,true]++[false]) ++
      ((expanded earlier).reverse ++ false::false::L).tail) false xs).2 =
      boundaryTape (earlier++[b]) xs L := by
  have hs := source_cons earlier L
  simp [canonical,boundaryTape,tapeAt,tapeLeft,expanded,List.reverse_append,List.cons_append]
  simpa [expanded] using hs

/-- Process one actual encoded first-component block, returning to the
controller entry exactly when another block remains. -/
theorem run_block (zero one earlier : List Bool) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (boundaryTape (earlier++[b]) xs L)) :
    ∃ d, run (program zero one) c (groupCost zero one earlier b xs) = some (.inr d) ∧
      d.1 = (if earlier.isEmpty then boundary zero one else 0) ∧
      TapeRel d.2 (boundaryTape earlier (groupOutput zero one b xs) L) := by
  have ht' : TapeRel c.2 (canonical (([true,b,true,true,true]++[false]) ++
      ((expanded earlier).reverse ++ false::false::L).tail) false xs).2 := by
    rw [aligned]; exact ht
  have h := run_group zero one [true,b,true,true,true] (by simp) false xs earlier L c hq ht'
  simpa [pred,groupCost,groupOutput,boundaryTape] using h

/-- `todo` lists block data bits in reverse input order. -/
def loopOutput (zero one : List Bool) : List Bool → List Bool → List Bool
  | [], xs => xs
  | b::todo, xs => loopOutput zero one todo (groupOutput zero one b xs)

def loopCost (zero one : List Bool) : List Bool → List Bool → Nat
  | [], _ => 0
  | b::todo, xs => groupCost zero one todo.reverse b xs + loopCost zero one todo (groupOutput zero one b xs)

/-- The single concrete table processes every nonempty list of encoded
first-component blocks and reaches its boundary outcome. Each interior
probe returns to the same state-zero entry; no external phase decisions are
used during execution. -/
theorem run_blocks (zero one todo xs L : List Bool) (hne : todo ≠ []) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (boundaryTape todo.reverse xs L)) :
    ∃ d, run (program zero one) c (loopCost zero one todo xs) = some (.inr d) ∧
      d.1 = boundary zero one ∧ TapeRel d.2 (boundaryTape [] (loopOutput zero one todo xs) L) := by
  induction todo generalizing xs c with
  | nil => contradiction
  | cons b bs ih =>
    have ht' : TapeRel c.2 (boundaryTape (bs.reverse++[b]) xs L) := by simpa using ht
    obtain ⟨mid,hm,hmid,htape⟩ := run_block zero one bs.reverse b xs L c hq ht'
    cases bs with
    | nil =>
      refine ⟨mid,?_,?_,?_⟩
      · simpa [loopCost] using hm
      · simpa using hmid
      · simpa [loopOutput] using htape
    | cons p ps =>
      have hnon : (p::ps).reverse.isEmpty = false := by simp
      have hq' : mid.1 = 0 := by simpa [hnon] using hmid
      obtain ⟨last,hlast,hlastq,hlastt⟩ := ih (groupOutput zero one b xs) (by simp) mid hq' htape
      refine ⟨last,?_,hlastq,?_⟩
      · change run (program zero one) c
          (groupCost zero one (p::ps).reverse b xs +
            loopCost zero one (p::ps) (groupOutput zero one b xs)) = some (.inr last)
        rw [run_continue _ _ _ _ _ hm]
        exact hlast
      · simpa [loopOutput] using hlastt

theorem result_length_le (zero one remaining : List Bool) (b : Bool) (xs : List Bool) :
    (result zero one remaining b xs).2.length ≤
      xs.length+remaining.length*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one) := by
  induction remaining generalizing b xs with
  | nil => simp [result]
  | cons p ps ih =>
    have hb := Shared.Codes.FiniteProgramTaggedLoop.output_length_le zero one b xs
    have h := ih p (Shared.Codes.FiniteProgramTaggedLoop.output zero one b xs)
    simp only [result,List.length_cons,Nat.add_mul] at ⊢
    omega

theorem groupOutput_length_le (zero one : List Bool) (b : Bool) (xs : List Bool) :
    (groupOutput zero one b xs).length ≤
      xs.length+6*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one) := by
  have h := result_length_le zero one (pred b) false xs
  simpa [groupOutput,pred] using h

theorem groupCost_bound (zero one earlier : List Bool) (b : Bool) (xs : List Bool) :
    groupCost zero one earlier b xs ≤
      6*(16*(xs.length+6*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one)) +
        16*Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one+31)+4 := by
  have h := Shared.Codes.FiniteProgramTaggedLoop.totalCost_bound zero one (pred b) false xs
  simp only [pred,List.length_cons,List.length_nil] at h
  unfold groupCost
  simp only [pred]
  cases he : earlier.isEmpty <;> simp only [Bool.false_eq_true,reduceIte] <;> omega

/-- An explicit quadratic cost bound for the full nonempty-block scan. -/
theorem loopCost_bound (zero one todo xs : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    loopCost zero one todo xs ≤ todo.length *
      (6*(16*(xs.length+todo.length*gain+gain)+16*w+31)+4) := by
  induction todo generalizing xs with
  | nil => simp [loopCost]
  | cons b bs ih =>
    dsimp only
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    let k := bs.length
    let bound := 6*(16*(xs.length+(k+1)*gain+gain)+16*w+31)+4
    have hbuf : (groupOutput zero one b xs).length ≤ xs.length+gain := by
      simpa [gain,w] using groupOutput_length_le zero one b xs
    have hsize : (groupOutput zero one b xs).length+k*gain ≤ xs.length+(k+1)*gain := by
      rw [Nat.add_mul]
      omega
    have hlocal : groupCost zero one bs.reverse b xs ≤ bound := by
      have h := groupCost_bound zero one bs.reverse b xs
      dsimp [bound,gain,w] at *
      omega
    have hind : 6*(16*((groupOutput zero one b xs).length+k*gain+gain)+16*w+31)+4 ≤ bound := by
      dsimp [bound]
      omega
    have hrec := ih (groupOutput zero one b xs)
    change loopCost zero one bs (groupOutput zero one b xs) ≤
      k*(6*(16*((groupOutput zero one b xs).length+k*gain+gain)+16*w+31)+4) at hrec
    have hrec' : loopCost zero one bs (groupOutput zero one b xs) ≤ k*bound :=
      le_trans hrec (Nat.mul_le_mul_left k hind)
    change groupCost zero one bs.reverse b xs + loopCost zero one bs (groupOutput zero one b xs) ≤ (k+1)*bound
    calc
      _ ≤ bound+k*bound := Nat.add_le_add hlocal hrec'
      _ = (k+1)*bound := by simp [Nat.add_mul,Nat.add_comm]

theorem program_length (zero one : List Bool) :
    (program zero one).length = 245+18*zero.length+18*one.length := by
  simp [program,base,Shared.Codes.FiniteProgramPhaseProbe.six_phase_length]
  omega

namespace Fixtures
set_option maxRecDepth 8192 in
example : run (program [] []) (243,([],false,[false])) 2 =
    some (.inr (0,([],false,[false]))) := by decide
set_option maxRecDepth 8192 in
example : step (program [] []) (242,([],false,[])) = some (.inl false) := by decide
example : valid (program [false] [true]) = true := program_valid [false] [true]
example : (program [false] [true]).length = 281 := by simpa using program_length [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramFirstBlocksController
