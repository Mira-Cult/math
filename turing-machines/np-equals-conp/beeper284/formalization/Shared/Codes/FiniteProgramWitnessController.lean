import Shared.Codes.FiniteProgramWitnessPhases
import Shared.Codes.FiniteProgramFirstBlocksController
set_option maxHeartbeats 3000000
-- Avoid the constructor-name linter traversing expanded dependent machine types.
set_option linter.constructorNameAsVariable false

/-! A finite looping witness-block table. The marked-separator continuation
is left for the pair-input adapter. -/
namespace Shared.Codes.FiniteProgramWitnessController
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramWitnessPhases (phases phases_valid phases_length stride probe probe_segment dummy witnessTape witnessOutput witnessCost witnessPred run_witness_block)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)

def base (zero one : List Bool) : Program := phases zero one 3
def interior (zero one : List Bool) : Nat := 3*stride zero one+3
def boundary (zero one : List Bool) : Nat := 3*stride zero one+4

def program (zero one : List Bool) : Program :=
  let p := base zero one
  p.set (interior zero one) (branch p.length) ++ [bridge 0]

theorem base_length (zero one : List Bool) : (base zero one).length = 3*stride zero one+5 := by
  simp [base,phases_length,probe]

theorem interior_bound (zero one : List Bool) : interior zero one < (base zero one).length := by
  simp [interior,base_length]

theorem base_stop (zero one : List Bool) (t : Tape) :
    step (base zero one) (interior zero one,t) = some (.inl false) := by
  have hc : ((3,t) : Config).1 < probe.length := by simp [probe]
  have h := probe_segment zero one 3 (3,t) hc 1
  have hl : run probe (3,t) 1 = some (.inl false) := by
    cases ht : t.2.1 <;> simp [run,advance,step,probe,dummy,ht]
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
    have hv := phases_valid zero one 3
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


attribute [local irreducible] Shared.Codes.FinitePrograms.run

def groupOutput (zero one : List Bool) (b : Bool) (xs : List Bool) : List Bool :=
  witnessOutput zero one [] b xs

theorem output_independent (zero one earlier : List Bool) (b : Bool) (xs : List Bool) :
    witnessOutput zero one earlier b xs = groupOutput zero one b xs := by
  simp [witnessOutput,witnessPred,Shared.Codes.FiniteProgramTaggedLoop.result,groupOutput]

def groupCost (zero one earlier : List Bool) (b : Bool) (xs : List Bool) : Nat :=
  witnessCost zero one earlier b xs + (if earlier.isEmpty then 0 else 2)

/-- One encoded witness block runs to the separator or, after two charged
restart transitions, returns to state zero for the next block. -/
theorem run_block (zero one earlier : List Bool) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (witnessTape (earlier++[b]) xs L)) :
    ∃ d, run (program zero one) c (groupCost zero one earlier b xs) = some (.inr d) ∧
      d.1 = (if earlier.isEmpty then boundary zero one else 0) ∧
      TapeRel d.2 (witnessTape earlier (groupOutput zero one b xs) L) := by
  let t := witnessTape earlier (groupOutput zero one b xs) L
  let duration := witnessCost zero one earlier b xs
  obtain ⟨mid,hm,hmid,htape⟩ := run_witness_block zero one earlier b xs L c hq ht
  rw [output_independent] at htape
  have hc : c.1 < (base zero one).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _ (phases_valid zero one 3)
  have hp := Shared.Codes.FiniteProgramFirstEntry.first_entry
    (base zero one) (program zero one) c mid duration (interior zero one) false
    (phases_valid zero one 3) hc (base_stop zero one) (base_other zero one) hm
  cases he : earlier.isEmpty with
  | true =>
    have hd : mid.1 = boundary zero one := by simpa [he,boundary] using hmid
    refine ⟨mid,?_,?_,htape⟩
    · simpa [he,groupCost,duration] using hp
    · simpa [he] using hd
  | false =>
    have hd : mid.1 = interior zero one := by simpa [he,interior] using hmid
    let source := Shared.Codes.FiniteProgramWitnessPhases.witnessSource earlier L
    have hhead : source.head?.getD false = false := by
      simpa [source,Shared.Codes.FiniteProgramWitnessPhases.witnessSource,he] using
        Shared.Codes.FiniteProgramWitnessPhases.witness_boundary_head earlier L
    have hshape : t = tapeAt source.tail (false::false::(Shared.Codes.FiniteProgramBitShuttle.tagged
        (groupOutput zero one b xs) ++ [false,false,false])) := by
      simp [t,witnessTape,tapeLeft,tapeAt,hhead,source,List.cons_append]
    have hrestart := restart zero one false source.tail
      (Shared.Codes.FiniteProgramBitShuttle.tagged (groupOutput zero one b xs) ++ [false,false,false])
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
        · change run (program zero one) c (duration+(if earlier.isEmpty then 0 else 2)) = some (.inr d)
          rw [he]
          change run (program zero one) c (duration+2) = some (.inr d)
          rw [run_continue _ _ _ _ _ hp]
          exact hr
        · simpa [he] using hdone.1

/-- `todo` lists block data bits in reverse input order. -/
def loopOutput (zero one : List Bool) : List Bool → List Bool → List Bool
  | [], xs => xs
  | b::todo, xs => loopOutput zero one todo (groupOutput zero one b xs)

def loopCost (zero one : List Bool) : List Bool → List Bool → Nat
  | [], _ => 0
  | b::todo, xs => groupCost zero one todo.reverse b xs + loopCost zero one todo (groupOutput zero one b xs)

/-- The single concrete table processes every nonempty list of encoded
witness blocks and reaches its boundary outcome. Each interior
probe returns to the same state-zero entry; no external phase decisions are
used during execution. -/
theorem run_blocks (zero one todo xs L : List Bool) (hne : todo ≠ []) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (witnessTape todo.reverse xs L)) :
    ∃ d, run (program zero one) c (loopCost zero one todo xs) = some (.inr d) ∧
      d.1 = boundary zero one ∧ TapeRel d.2 (witnessTape [] (loopOutput zero one todo xs) L) := by
  induction todo generalizing xs c with
  | nil => contradiction
  | cons b bs ih =>
    have ht' : TapeRel c.2 (witnessTape (bs.reverse++[b]) xs L) := by simpa using ht
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

theorem groupOutput_length_le (zero one : List Bool) (b : Bool) (xs : List Bool) :
    (groupOutput zero one b xs).length ≤
      xs.length+3*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one) := by
  have h := Shared.Codes.FiniteProgramFirstBlocksController.result_length_le zero one
    (witnessPred [] b) false xs
  simpa [groupOutput,witnessOutput,witnessPred] using h

theorem groupCost_bound (zero one earlier : List Bool) (b : Bool) (xs : List Bool) :
    groupCost zero one earlier b xs ≤
      3*(16*(xs.length+3*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one)) +
        16*Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one+31)+4 := by
  have h := Shared.Codes.FiniteProgramWitnessPhases.witnessCost_bound zero one earlier b xs
  unfold groupCost
  cases he : earlier.isEmpty <;> simp only [Bool.false_eq_true,reduceIte] <;> omega

/-- An explicit quadratic cost bound for the full nonempty-block scan. -/
theorem loopCost_bound (zero one todo xs : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 3*(1+w)
    loopCost zero one todo xs ≤ todo.length *
      (3*(16*(xs.length+todo.length*gain+gain)+16*w+31)+4) := by
  induction todo generalizing xs with
  | nil => simp [loopCost]
  | cons b bs ih =>
    dsimp only
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 3*(1+w)
    let k := bs.length
    let bound := 3*(16*(xs.length+(k+1)*gain+gain)+16*w+31)+4
    have hbuf : (groupOutput zero one b xs).length ≤ xs.length+gain := by
      simpa [gain,w] using groupOutput_length_le zero one b xs
    have hsize : (groupOutput zero one b xs).length+k*gain ≤ xs.length+(k+1)*gain := by
      rw [Nat.add_mul]
      omega
    have hlocal : groupCost zero one bs.reverse b xs ≤ bound := by
      have h := groupCost_bound zero one bs.reverse b xs
      dsimp [bound,gain,w] at *
      omega
    have hind : 3*(16*((groupOutput zero one b xs).length+k*gain+gain)+16*w+31)+4 ≤ bound := by
      dsimp [bound]
      omega
    have hrec := ih (groupOutput zero one b xs)
    change loopCost zero one bs (groupOutput zero one b xs) ≤
      k*(3*(16*((groupOutput zero one b xs).length+k*gain+gain)+16*w+31)+4) at hrec
    have hrec' : loopCost zero one bs (groupOutput zero one b xs) ≤ k*bound :=
      le_trans hrec (Nat.mul_le_mul_left k hind)
    change groupCost zero one bs.reverse b xs + loopCost zero one bs (groupOutput zero one b xs) ≤ (k+1)*bound
    calc
      _ ≤ bound+k*bound := Nat.add_le_add hlocal hrec'
      _ = (k+1)*bound := by simp [Nat.add_mul,Nat.add_comm]

theorem program_length (zero one : List Bool) :
    (program zero one).length = 126+9*zero.length+9*one.length := by
  simp [program,base,Shared.Codes.FiniteProgramWitnessPhases.three_phase_length]
  omega

namespace Fixtures
/-- A two-block witness exercises the charged interior return. -/
example : ∃ d, run (program [] []) (0,witnessTape [false,true] [] [])
      (loopCost [] [] [true,false] []) = some (.inr d) ∧
    d.1 = boundary [] [] ∧ TapeRel d.2 (witnessTape [] (loopOutput [] [] [true,false] []) []) := by
  exact run_blocks [] [] [true,false] [] [] (by decide)
    (0,witnessTape [false,true] [] []) rfl rfl

example : valid (program [false] [true]) = true := program_valid [false] [true]
example : (program [false] [true]).length = 144 := by simpa using program_length [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramWitnessController
