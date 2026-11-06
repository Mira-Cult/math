import Shared.Codes.FiniteProgramFirstEntryMany
import Shared.Codes.FiniteProgramFirstBlocksController
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Probe the first-component boundary, routing an empty component directly
to the scan exit and a nonempty component into the first-block loop. -/
namespace Shared.Codes.FiniteProgramFirstStart
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramFirstBlocksController (boundaryTape loopOutput loopCost)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev payload := Shared.Codes.FiniteProgramFirstBlocksController.program
abbrev boundary := Shared.Codes.FiniteProgramFirstBlocksController.boundary
abbrev probe := Shared.Codes.FiniteProgramPhaseProbe.probe

def pre (zero one : List Bool) : Program :=
  [ ((false,false,1,0),(true,false,1,0)),
    ((false,true,2,0),(true,true,3,0)),
    branch 4, branch 5, bridge (6+boundary zero one), bridge 6 ]

def program (zero one : List Bool) : Program := link (pre zero one) (payload zero one) []

theorem pre_length (zero one : List Bool) : (pre zero one).length = 6 := rfl

theorem program_length (zero one : List Bool) :
    (program zero one).length = 251+18*zero.length+18*one.length := by
  simp [program,link,pre_length,Shared.Codes.FiniteProgramFirstBlocksController.program_length]
  omega

theorem program_valid (zero one : List Bool) : valid (program zero one) = true := by
  let d := payload zero one
  let m := 6+d.length
  have hb : boundary zero one < d.length := by
    simp [d,boundary,Shared.Codes.FiniteProgramFirstBlocksController.boundary,
      Shared.Codes.FiniteProgramFirstBlocksController.program,
      Shared.Codes.FiniteProgramFirstBlocksController.base_length]
  have hm : (program zero one).length = m := by simp [program,link,pre_length,m,d]
  have hp : ∀ r ∈ pre zero one, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hall : (pre zero one).all (fun r => validRow m r.1 && validRow m r.2) = true := by
      have h4 : 4 < m := by dsimp [m]; omega
      have h5 : 5 < m := by dsimp [m]; omega
      have h6 : 6 < m := by dsimp [m]; omega
      have hbound : 6+boundary zero one < m := by dsimp [m]; omega
      simp [pre,branch,bridge,validRow,h4,h5,h6,hbound]
      omega
    rw [List.all_eq_true] at hall
    simpa only [Bool.and_eq_true] using hall r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hall : (program zero one).all
      (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre zero one ∨ r ∈ d.map (shiftPair 6) := by
      simpa [program,link,pre_length,d,List.mem_append] using hr
    rw [hm]
    rcases hr' with hpre | hmap
    · simpa only [Bool.and_eq_true] using hp r hpre
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hd r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 6 d.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 6 d.length h₂⟩
  have hn : (program zero one).isEmpty = false := by simp [program,link,pre]
  change (!(program zero one).isEmpty && (program zero one).all
    (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2)) = true
  rw [hn,hall]
  rfl

theorem probe_stop (j : Nat) (hj : j = 2 ∨ j = 3) (t : Tape) :
    step probe (j,t) = some (.inl false) := by
  rcases hj with rfl | rfl <;> cases h : t.2.1 <;>
    simp [step,probe,Shared.Codes.FiniteProgramPhaseProbe.probe,
      Shared.Codes.FiniteProgramFirstBlockProbe.program,Shared.Codes.FiniteProgramPhaseProbe.dummy,h]

theorem probe_other (zero one : List Bool) (d : Config) (hd : d.1 < probe.length)
    (h2 : d.1 ≠ 2) (h3 : d.1 ≠ 3) : step probe d = step (program zero one) d := by
  have hsmall : d.1 = 0 ∨ d.1 = 1 := by
    have hl : probe.length = 4 := by simp [probe,Shared.Codes.FiniteProgramPhaseProbe.probe,
      Shared.Codes.FiniteProgramFirstBlockProbe.program]
    omega
  rcases hsmall with hq | hq <;> cases d with
    | mk q t =>
      simp only at hq
      subst q
      cases ht : t.2.1 <;>
        simp [step,probe,Shared.Codes.FiniteProgramPhaseProbe.probe,
          Shared.Codes.FiniteProgramFirstBlockProbe.program,program,link,pre,ht]

theorem probe_run (zero one x xs L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (boundaryTape x xs L)) :
    ∃ d, run (program zero one) c 2 = some (.inr d) ∧
      d.1 = (if x.isEmpty then 2 else 3) ∧ TapeRel d.2 (boundaryTape x xs L) := by
  obtain ⟨d,hd,hstate,htape⟩ := Shared.Codes.FiniteProgramFirstBlockProbe.first_component_boundary_related
    [Shared.Codes.FiniteProgramPhaseProbe.dummy,Shared.Codes.FiniteProgramPhaseProbe.dummy]
    x L (false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false]) c hq ht
  have hp : run probe c 2 = some (.inr d) := hd
  have hc : c.1 < probe.length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty probe Shared.Codes.FiniteProgramPhaseProbe.probe_valid
  have hrun := Shared.Codes.FiniteProgramFirstEntry.first_entry_many probe (program zero one) c d 2 {2,3}
    Shared.Codes.FiniteProgramPhaseProbe.probe_valid hc
    (by
      intro q hq
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hq
      exact ⟨false,probe_stop q hq⟩)
    (by
      intro e he hn
      have h2 : e.1 ≠ 2 := by intro h; apply hn; simp [h]
      have h3 : e.1 ≠ 3 := by intro h; apply hn; simp [h]
      exact probe_other zero one e he h2 h3) hp
  exact ⟨d,hrun,hstate,htape⟩

theorem exit_empty (zero one : List Bool) (head : Bool) (L R : List Bool) :
    run (program zero one) (2,tapeAt L (head::false::R)) 2 =
      some (.inr (6+boundary zero one,tapeAt L (head::false::R))) := by
  cases head <;> simp [run,advance,step,program,link,pre,branch,bridge,tapeAt,moveTape]

theorem exit_nonempty (zero one : List Bool) (head : Bool) (L R : List Bool) :
    run (program zero one) (3,tapeAt L (head::false::R)) 2 =
      some (.inr (6,tapeAt L (head::false::R))) := by
  cases head <;> simp [run,advance,step,program,link,pre,branch,bridge,tapeAt,moveTape]

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (zero one : List Bool) : link (pre zero one) (payload zero one) [] = program zero one := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program pre

/-- The first-block payload handles its empty case at the boundary state in
zero steps; nonempty inputs run its established loop. -/
theorem payload_run (zero one x xs L : List Bool) (c : Config)
    (hq : c.1 = (if x.isEmpty then boundary zero one else 0))
    (ht : TapeRel c.2 (boundaryTape x xs L)) :
    ∃ d, run (payload zero one) c (loopCost zero one x.reverse xs) = some (.inr d) ∧
      d.1 = boundary zero one ∧ TapeRel d.2 (boundaryTape [] (loopOutput zero one x.reverse xs) L) := by
  cases x with
  | nil =>
    refine ⟨c,?_,?_,?_⟩
    · simp only [List.reverse_nil,Shared.Codes.FiniteProgramFirstBlocksController.loopCost,run_zero]
    · simpa using hq
    · simpa [Shared.Codes.FiniteProgramFirstBlocksController.loopOutput] using ht
  | cons b bs =>
    have hq' : c.1 = 0 := by simpa using hq
    have hne : (b::bs).reverse ≠ [] := by simp
    have ht' : TapeRel c.2 (boundaryTape ((b::bs).reverse).reverse xs L) := by simpa using ht
    simpa using Shared.Codes.FiniteProgramFirstBlocksController.run_blocks
      zero one (b::bs).reverse xs L hne c hq' ht'

/-- One valid finite table processes every first component, including the
empty list. Two probe transitions and two routing transitions are charged. -/
theorem run_first (zero one x xs L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (boundaryTape x xs L)) :
    ∃ d, run (program zero one) c (4+loopCost zero one x.reverse xs) = some (.inr d) ∧
      d.1 = 6+boundary zero one ∧ TapeRel d.2 (boundaryTape [] (loopOutput zero one x.reverse xs) L) := by
  let t := boundaryTape x xs L
  let entry := if x.isEmpty then boundary zero one else 0
  let q := if x.isEmpty then 2 else 3
  let source := (expanded x).reverse ++ false::false::L
  let right := Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false]
  obtain ⟨mid,hm,hstate,htape⟩ := probe_run zero one x xs L c hq ht
  have hhead : source.head?.getD false = false :=
    Shared.Codes.FiniteProgramFirstBlockProbe.first_component_head x L
  have hshape : t = tapeAt source.tail (false::false::right) := by
    change (source.tail,source.head?.getD false,false::right) = _
    simp [tapeAt,hhead]
  have hexit : run (program zero one) (q,t) 2 = some (.inr (6+entry,t)) := by
    rw [hshape]
    cases he : x.isEmpty with
    | false => simpa [q,entry,he] using exit_nonempty zero one false source.tail right
    | true => simpa [q,entry,he] using exit_empty zero one false source.tail right
  have hrel := run_related (program zero one) mid (q,t) hstate htape 2
  rw [hexit] at hrel
  obtain ⟨start,hr,hqstart,htstart⟩ := status_live _ _ _ hrel
  obtain ⟨last,hlast,hlastq,hlastt⟩ := payload_run zero one x xs L (entry,start.2) rfl htstart
  have hin : ((entry,start.2) : Config).1 < (payload zero one).length := by
    cases he : x.isEmpty with
    | false =>
      simp only [entry,he,Bool.false_eq_true,reduceIte]
      exact Shared.Codes.FiniteProgramLink.valid_nonempty _
        (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one)
    | true =>
      have hb := Shared.Codes.FiniteProgramFirstBlocksController.program_length zero one
      have hstop : boundary zero one < (payload zero one).length := by
        simp [boundary,Shared.Codes.FiniteProgramFirstBlocksController.boundary,
          Shared.Codes.FiniteProgramFirstBlocksController.program,
          Shared.Codes.FiniteProgramFirstBlocksController.base_length]
      simpa [entry,he] using hstop
  have hs := run_shift (pre zero one) (payload zero one) []
    (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one) (entry,start.2) hin
    (loopCost zero one x.reverse xs)
  rw [hlast,program_link] at hs
  have hcfg : start = shiftConfig 6 (entry,start.2) := by
    apply Prod.ext
    · simpa only [shiftConfig] using hqstart
    · rfl
  refine ⟨shiftConfig 6 last,?_,?_,hlastt⟩
  · rw [show 4+loopCost zero one x.reverse xs = 2+(2+loopCost zero one x.reverse xs) by omega]
    rw [run_continue _ _ _ _ _ hm,run_continue _ _ _ _ _ hr,hcfg]
    simpa only [pre_length,shiftStatus] using hs
  · simp only [shiftConfig,hlastq]

/-- The guard adds four steps to the existing quadratic first-block bound. -/
theorem cost_bound (zero one x xs : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    4+loopCost zero one x.reverse xs ≤ 4+x.length *
      (6*(16*(xs.length+x.length*gain+gain)+16*w+31)+4) := by
  have h := Shared.Codes.FiniteProgramFirstBlocksController.loopCost_bound zero one x.reverse xs
  simp only [List.length_reverse] at h
  exact Nat.add_le_add_left h 4

namespace Fixtures
example : valid (program [false] [true]) = true := program_valid [false] [true]
example : (program [false] [true]).length = 287 := by simpa using program_length [false] [true]
example : run (program [] []) (2,tapeAt [] [false,false]) 2 =
    some (.inr (6+boundary [] [],tapeAt [] [false,false])) := exit_empty [] [] false [] []
example : run (program [] []) (3,tapeAt [] [false,false]) 2 =
    some (.inr (6,tapeAt [] [false,false])) := exit_nonempty [] [] false [] []
end Fixtures

end Shared.Codes.FiniteProgramFirstStart
