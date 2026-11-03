import Shared.Codes.FiniteProgramFirstEntryMany
import Shared.Codes.FiniteProgramExtendAdvance
import Shared.Codes.FiniteProgramTaggedExtend
import Shared.Codes.FiniteProgramTaggedLoop
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Attach a finite continuation to two distinct terminal rows, preserving
runs up to either exit and charging the handoff transitions. -/
namespace Shared.Codes.FiniteProgramTwoExit
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def pre (p : Program) (a b : Nat) : Program :=
  (p.set a (branch p.length)).set b (branch (p.length+1)) ++
    [bridge (p.length+2),bridge (p.length+2)]
def program (p q : Program) (a b : Nat) : Program := link (pre p a b) q []

theorem pre_length (p : Program) (a b : Nat) : (pre p a b).length = p.length+2 := by simp [pre]
theorem program_length (p q : Program) (a b : Nat) :
    (program p q a b).length = p.length+2+q.length := by simp [program,link,pre_length,Nat.add_assoc]

theorem source_other (p q : Program) (a b : Nat) (d : Config)
    (hd : d.1 < p.length) (ha : d.1 ≠ a) (hb : d.1 ≠ b) :
    step p d = step (program p q a b) d := by
  have hl : (program p q a b)[d.1]? = p[d.1]? := by
    simp [program,link,pre,List.getElem?_append_left,hd,Ne.symm ha,Ne.symm hb]
  simp [step,hl]

theorem first_row (p q : Program) (a b : Nat) (ha : a < p.length) (hne : a ≠ b) :
    (program p q a b)[a]? = some (branch p.length) := by
  simp [program,link,pre,List.getElem?_append_left,ha,Ne.symm hne]
theorem second_row (p q : Program) (a b : Nat) (hb : b < p.length) :
    (program p q a b)[b]? = some (branch (p.length+1)) := by
  simp [program,link,pre,List.getElem?_append_left,hb]
theorem first_bridge (p q : Program) (a b : Nat) :
    (program p q a b)[p.length]? = some (bridge (p.length+2)) := by simp [program,link,pre]
theorem second_bridge (p q : Program) (a b : Nat) :
    (program p q a b)[p.length+1]? = some (bridge (p.length+2)) := by simp [program,link,pre]

theorem handoff_first (p q : Program) (a b : Nat) (ha : a < p.length) (hne : a ≠ b)
    (head next : Bool) (L R : List Bool) :
    run (program p q a b) (a,tapeAt L (head::next::R)) 2 =
      some (.inr ((pre p a b).length,tapeAt L (head::next::R))) := by
  have h := first_row p q a b ha hne
  have hb := first_bridge p q a b
  cases head <;> cases next <;> simp [run,advance,step,h,hb,branch,bridge,tapeAt,moveTape,pre_length]

theorem handoff_second (p q : Program) (a b : Nat) (hb : b < p.length)
    (head next : Bool) (L R : List Bool) :
    run (program p q a b) (b,tapeAt L (head::next::R)) 2 =
      some (.inr ((pre p a b).length,tapeAt L (head::next::R))) := by
  have h := second_row p q a b hb
  have ht := second_bridge p q a b
  cases head <;> cases next <;> simp [run,advance,step,h,ht,branch,bridge,tapeAt,moveTape,pre_length]

/-- A live run of the original table is preserved before either terminal row. -/
theorem first_entry (p q : Program) (a b : Nat) (c d : Config) (n : Nat)
    (hp : valid p = true) (hc : c.1 < p.length)
    (ha : ∀ t, step p (a,t) = some (.inl false))
    (hb : ∀ t, step p (b,t) = some (.inl false))
    (h : run p c n = some (.inr d)) : run (program p q a b) c n = some (.inr d) := by
  let stops : Set Nat := {a,b}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many p (program p q a b) c d n stops hp hc ?_ ?_ h
  · intro s hs
    simp only [stops,Set.mem_insert_iff,Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨false,ha⟩
    · exact ⟨false,hb⟩
  · intro c hc hn
    have ha' : c.1 ≠ a := by intro h; apply hn; simp [stops,h]
    have hb' : c.1 ≠ b := by intro h; apply hn; simp [stops,h]
    exact source_other p q a b c hc ha' hb'

theorem program_valid (p q : Program) (a b : Nat) (hp : valid p = true) (hq : valid q = true)
    (_ha : a < p.length) (_hb : b < p.length) : valid (program p q a b) = true := by
  let m := p.length+2+q.length
  have hqpos := Shared.Codes.FiniteProgramLink.valid_nonempty q hq
  have hl : (program p q a b).length = m := program_length p q a b
  have hpRows : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hp
    simpa only [Bool.and_eq_true] using hp.2 r hr
  have hqRows : ∀ r ∈ q, validRow q.length r.1 = true ∧ validRow q.length r.2 = true := by
    intro r hr
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hq
    simpa only [Bool.and_eq_true] using hq.2 r hr
  have hp_m : p.length ≤ m := by dsimp [m]; omega
  have hb0 : validRow m (branch p.length).1 = true ∧ validRow m (branch p.length).2 = true := by
    have h : p.length < m := by dsimp [m]; omega
    simp [branch,validRow,h]
  have hb1 : validRow m (branch (p.length+1)).1 = true ∧ validRow m (branch (p.length+1)).2 = true := by
    have h : p.length+1 < m := by dsimp [m]; omega
    simp [branch,validRow,h]
  have ht : validRow m (bridge (p.length+2)).1 = true ∧ validRow m (bridge (p.length+2)).2 = true := by
    have h : p.length+2 < m := by dsimp [m]; omega
    simp [bridge,validRow,h]
  have hset : ∀ r ∈ (p.set a (branch p.length)).set b (branch (p.length+1)),
      validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with hr | h
    · rcases List.mem_or_eq_of_mem_set hr with hr | h
      · obtain ⟨h₁,h₂⟩ := hpRows r hr
        exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hp_m h₁,
          Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hp_m h₂⟩
      · subst r; exact hb0
    · subst r; exact hb1
  have hall : (program p q a b).all
      (fun r => validRow (program p q a b).length r.1 && validRow (program p q a b).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ (p.set a (branch p.length)).set b (branch (p.length+1)) ∨
        r = bridge (p.length+2) ∨ r ∈ q.map (shiftPair (p.length+2)) := by
      simpa [program,link,pre,pre_length,List.mem_append] using hr
    rw [hl]
    rcases hr' with hs | hbridge | hmap
    · simpa only [Bool.and_eq_true] using hset r hs
    · subst r; simpa only [Bool.and_eq_true] using ht
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hqRows r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 (p.length+2) q.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 (p.length+2) q.length h₂⟩
  have hne : (program p q a b).isEmpty = false := by
    cases h : program p q a b with
    | nil => simp [h] at hl; dsimp [m] at hl; omega
    | cons r rs => rfl
  change (!(program p q a b).isEmpty && (program p q a b).all
    (fun r => validRow (program p q a b).length r.1 && validRow (program p q a b).length r.2)) = true
  rw [hne,hall]
  rfl


private theorem initial_tape_shape (input : List Bool) :
    ∃ head next L R, Shared.Codes.FiniteProgramTapeEquiv.TapeRel (initial input).2
      (tapeAt L (head::next::R)) := by
  cases input with
  | nil =>
    refine ⟨false,false,[],[],?_⟩
    simpa [initial,tapeAt] using Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank [] [] false
  | cons head tail =>
    cases tail with
    | nil =>
      refine ⟨head,false,[],[],?_⟩
      simpa [initial,tapeAt] using Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank [] [] head
    | cons next rest => exact ⟨head,next,[],rest,rfl⟩

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : Shared.Codes.FiniteProgramTapeEquiv.StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ Shared.Codes.FiniteProgramTapeEquiv.TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

/-- A terminating initialization to either exit followed by two charged moves
    starts any valid evaluator on the initialized tape. The equality includes
    its timeout and invalid-result behavior; no termination is assumed. -/
theorem bounded_after_exit (p q : Program) (a b : Nat) (input payload : List Bool)
    (setup fuel : Nat) (d : Config) (hp : valid p = true) (hq : valid q = true)
    (ha : a < p.length) (hb : b < p.length) (hne : a ≠ b)
    (hstopa : ∀ t, step p (a,t) = some (.inl false))
    (hstopb : ∀ t, step p (b,t) = some (.inl false))
    (hr : run p (initial input) setup = some (.inr d)) (hstate : d.1 = a ∨ d.1 = b)
    (htape : Shared.Codes.FiniteProgramTapeEquiv.TapeRel d.2 (initial payload).2) :
    bounded (program p q a b) input (setup+2+fuel) = bounded q payload fuel := by
  obtain ⟨head,next,L,R,hshape⟩ := initial_tape_shape payload
  let t := tapeAt L (head::next::R)
  have ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel d.2 t := Eq.trans htape hshape
  have hc : (initial input).1 < p.length := by
    simpa [initial] using (Shared.Codes.FiniteProgramLink.valid_nonempty p hp)
  have hr' := first_entry p q a b (initial input) d setup hp hc hstopa hstopb hr
  have hh : ∃ after, run (program p q a b) d 2 = some (.inr after) ∧
      after.1 = (pre p a b).length ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel after.2 t := by
    rcases hstate with hstate | hstate
    · have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program p q a b) d (a,t) hstate ht 2
      have hhandoff := handoff_first p q a b ha hne head next L R
      change run (program p q a b) (a,t) 2 = _ at hhandoff
      rw [hhandoff] at h
      exact status_live _ _ _ h
    · have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program p q a b) d (b,t) hstate ht 2
      have hhandoff := handoff_second p q a b hb head next L R
      change run (program p q a b) (b,t) 2 = _ at hhandoff
      rw [hhandoff] at h
      exact status_live _ _ _ h
  obtain ⟨after,hafter,hqafter,htafter⟩ := hh
  have hcfg : after = shiftConfig (pre p a b).length (0,after.2) := by
    apply Prod.ext
    · simpa [shiftConfig] using hqafter
    · rfl
  have hentry : run (program p q a b) (initial input) (setup+2) =
      some (.inr (shiftConfig (pre p a b).length (0,after.2))) := by
    rw [run_continue _ _ _ _ _ hr',hafter]
    exact congrArg (fun c : Config => (some (.inr c) : Status)) hcfg
  have hout := Shared.Codes.FiniteProgramLink.bounded_after_setup_tape
    (pre p a b) q [] hq input payload (0,after.2) (setup+2) fuel rfl
    (Eq.trans htafter (Eq.symm hshape)) hentry
  simpa [program,Nat.add_assoc] using hout

end Shared.Codes.FiniteProgramTwoExit
