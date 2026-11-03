import Shared.ComplexityBridge.PairReverseFirst
import Shared.Codes.FiniteProgramTapeEquiv
import Shared.Codes.FiniteProgramTaggedLoop

/-! A literal two-row boundary probe for a phase-aligned reverse scan of the
first component of the canonical pair encoding. It must be invoked only at
a first-component block boundary. -/
namespace Shared.Codes.FiniteProgramFirstBlockProbe
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.PairReverseFirst (expanded expanded_cons expanded_append)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (tape)

/-- Read one cell to the left and return. State 2 means a false predecessor;
state 3 means a true predecessor. Neither continuation is executed here. -/
def program (tail : Program) : Program :=
  [ ((false,false,1,0),(true,false,1,0)),
    ((false,true,2,0),(true,true,3,0)) ] ++ tail

/-- If the left cell is represented explicitly, probing restores the exact
tape and takes two finite-program transitions. -/
theorem probe (tail : Program) (a head : Bool) (L R : List Bool) :
    run (program tail) (0,(a::L,head,R)) 2 =
      some (.inr (if a then 3 else 2,(a::L,head,R))) := by
  cases a <;> cases head <;> simp [run,advance,step,program,moveTape]

/-- The initial all-blank left tape has a false predecessor; the additional
explicit blank is equivalent to the original tape. -/
theorem probe_empty_left (tail : Program) (head : Bool) (R : List Bool) :
    run (program tail) (0,([],head,R)) 2 =
      some (.inr (2,([false],head,R))) ∧ TapeRel ([false],head,R) ([],head,R) := by
  constructor
  · cases head <;> simp [run,advance,step,program,moveTape]
  · unfold TapeRel
    change (⟨head,Turing.ListBlank.mk [false],Turing.ListBlank.mk R⟩ : Turing.Tape Bool) =
      ⟨head,Turing.ListBlank.mk [],Turing.ListBlank.mk R⟩
    congr 1
    apply Quotient.sound
    exact Or.inr ⟨1,rfl⟩

/-- At the next first-component block boundary, the predecessor cell is true
exactly when an entire earlier block remains. The two false cells are the
explicit blank padding at the left boundary. -/
theorem first_component_boundary (tail : Program) (xs L R : List Bool) :
    let t := tapeLeft ((expanded xs).reverse ++ false::false::L) R
    run (program tail) (0,t) 2 = some (.inr (if xs.isEmpty then 2 else 3,t)) := by
  induction xs using List.reverseRecOn with
  | nil => simp [expanded,tapeLeft]; exact probe tail false false L R
  | append_singleton xs b ih =>
    rw [expanded_append,expanded_cons]
    simp only [expanded,List.flatMap_nil,List.append_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append]
    have hne : (xs ++ [b]).isEmpty = false := by cases xs <;> simp
    simp only [hne,Bool.false_eq_true,reduceIte,tapeLeft]
    exact probe tail true false _ R

/-- A blank-padded tape related to a phase-aligned boundary receives the same
outcome and remains related to its initial tape. -/
theorem first_component_boundary_related (tail : Program) (xs L R : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (tapeLeft ((expanded xs).reverse ++ false::false::L) R)) :
    ∃ d, run (program tail) c 2 = some (.inr d) ∧
      d.1 = (if xs.isEmpty then 2 else 3) ∧
      TapeRel d.2 (tapeLeft ((expanded xs).reverse ++ false::false::L) R) := by
  let t := tapeLeft ((expanded xs).reverse ++ false::false::L) R
  have h := run_related (program tail) c (0,t) (by simpa using hq) ht 2
  have hc := first_component_boundary tail xs L R
  change run (program tail) (0,t) 2 = some (.inr (if xs.isEmpty then 2 else 3,t)) at hc
  rw [hc] at h
  cases hs : run (program tail) c 2 with
  | none => rw [hs] at h; exact False.elim h
  | some v => cases v with
    | inl out => rw [hs] at h; exact False.elim h
    | inr d =>
      rw [hs] at h
      have hd : d.1 = (if xs.isEmpty then 2 else 3) ∧ TapeRel d.2 t := by
        exact h
      exact ⟨d,rfl,hd.1,hd.2⟩

theorem first_component_head (xs L : List Bool) :
    (((expanded xs).reverse ++ false::false::L).head?).getD false = false := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs b ih =>
    simp [expanded,List.reverse_append]

theorem last_predecessor (zero one : List Bool) (ps : List Bool) (b : Bool) (xs : List Bool) :
    (Shared.Codes.FiniteProgramTaggedLoop.result zero one (ps++[false]) b xs).1 = false := by
  induction ps generalizing b xs with
  | nil => rfl
  | cons p ps ih =>
    simpa [Shared.Codes.FiniteProgramTaggedLoop.result] using ih p (Shared.Codes.FiniteProgramTaggedLoop.output zero one b xs)

/-- Conditional operational handoff: after the loop processes the supplied
predecessors ending in a false cell, the separate probe table recognizes the
first-component boundary on the resulting blank-equivalent tape. A compiler
must still join these two tables and arrange the phase-aligned entry. -/
theorem cycles_then_probe (zero one : List Bool) (tail : Program) (ps : List Bool) (b : Bool)
    (xs remaining L : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramTaggedLoop.canonical
      ((ps++[false]) ++ ((expanded remaining).reverse ++ false::false::L).tail) b xs).2) :
    ∃ mid out,
      run (Shared.Codes.FiniteProgramTaggedLoop.program zero one) c
          (Shared.Codes.FiniteProgramTaggedLoop.totalCost zero one (ps++[false]) b xs) = some (.inr mid) ∧
      run (program tail) mid 2 = some (.inr out) ∧
      out.1 = (if remaining.isEmpty then 2 else 3) := by
  let source := (expanded remaining).reverse ++ false::false::L
  let res := Shared.Codes.FiniteProgramTaggedLoop.result zero one (ps++[false]) b xs
  obtain ⟨mid,hm,hmid,htape⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycles
    zero one (ps++[false]) b xs source.tail c hq ht
  have hbit : res.1 = false := last_predecessor zero one ps b xs
  change TapeRel mid.2 (Shared.Codes.FiniteProgramTaggedLoop.canonical source.tail res.1 res.2).2 at htape
  rw [hbit] at htape
  have hcfg : (Shared.Codes.FiniteProgramTaggedLoop.canonical source.tail false res.2).2 =
      tapeLeft source (false::Shared.Codes.FiniteProgramBitShuttle.tagged res.2 ++ [false,false,false]) := by
    have hh : source.head?.getD false = false := first_component_head remaining L
    simp [Shared.Codes.FiniteProgramTaggedLoop.canonical,
      Shared.ComplexityBridge.PairMarkedScanner.tapeAt,tapeLeft,hh,List.cons_append]
  rw [hcfg] at htape
  obtain ⟨out,ho,hout,_⟩ := first_component_boundary_related tail remaining L
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged res.2 ++ [false,false,false]) mid hmid htape
  exact ⟨mid,out,hm,ho,hout⟩

/-- Both outcome rows must be supplied and valid in the full table. -/
theorem valid_of_continuation (tail : Program) (hne : 2 ≤ tail.length)
    (htail : ∀ row ∈ tail, validRow (2+tail.length) row.1 = true ∧
      validRow (2+tail.length) row.2 = true) : valid (program tail) = true := by
  have hlen : (program tail).length = 2+tail.length := by simp [program]; omega
  have ht : tail.all (fun rows => validRow (2+tail.length) rows.1 &&
      validRow (2+tail.length) rows.2) = true := by
    rw [List.all_eq_true]
    intro rows hrows
    obtain ⟨h₁,h₂⟩ := htail rows hrows
    simp [h₁,h₂]
  unfold valid
  rw [hlen]
  simp only [program,List.cons_append,List.nil_append,List.isEmpty_cons,Bool.not_false,
    Bool.true_and,List.all_cons,ht,Bool.and_true]
  simp [validRow]
  omega

namespace Fixtures
example : run (program []) (0,([false,false],false,[true])) 2 =
    some (.inr (2,([false,false],false,[true]))) := by decide
example : run (program []) (0,([true,false],false,[true])) 2 =
    some (.inr (3,([true,false],false,[true]))) := by decide
example : valid (program [((false,true,0,1),(true,true,0,1)),((false,true,0,1),(true,true,0,1))]) = true := by decide
end Fixtures

end Shared.Codes.FiniteProgramFirstBlockProbe
