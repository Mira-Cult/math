import Shared.PNP.Record285.PythonControlRelocationInside

/-! The relocated decoder relation is preserved by each actual step until
its boundary, with explicit paired-fault behavior. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationRun
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationStep
open Shared.PNP.Record285.PythonControlRelocationRegion
open Shared.PNP.Record285.PythonControlRelocationActual
open Shared.PNP.Record285.PythonControlRelocationInvariant
open Shared.PNP.Record285.PythonControlRelocationInside
open Shared.PNP.Record285.PythonControlSettle
open Shared.Beeping

def BoundedMatched (r c : Status) : Prop := Matched r c ∧ Inside r

def BeforeBoundary : Status → Prop
  | .fault => True
  | .returned _ => False
  | .live c => (settle c.pc c.loops).1 < 65

theorem reference_inside_step (pc : Nat) (s : Store) (inner : List Loop)
    (hlo : 47 ≤ pc) (hhi : pc ≤ 65)
    (hheads : ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65)
    (hinside : (settle pc (inner++referenceBase)).1 < 65) :
    Inside (step code (.live ⟨pc,s,inner++referenceBase⟩)).1 := by
  obtain ⟨target,remaining,htlo,hthi,hrem,href,hcand⟩ :=
    settle_shared_bounded pc inner hlo hhi hheads
  have htinside : target < 65 := by simpa only [href,Prod.fst] using hinside
  let i := target-47
  have hindex : i < 18 := by dsimp [i]; omega
  have ht : 47+i=target := by dsimp [i]; omega
  obtain ⟨line,hrow,hrowc,hallowed,hedges⟩ := decoder_row i hindex
  have hb := decoder_bounds i hindex line hrow
  rw [ht] at hrow hb
  have hrefFixed := settle_idempotent pc (inner++referenceBase)
  rw [href] at hrefFixed
  simp only at hrefFixed
  rw [step_settled pc s (inner++referenceBase) target (remaining++referenceBase) href]
  exact reference_step_bounded target s remaining line htlo htinside hrem hrefFixed hrow hallowed hb

theorem bounded_step (r c : Status) (h : BoundedMatched r c) (hb : BeforeBoundary r) :
    let rs := step code r
    let cs := step code c
    rs.2=cs.2 ∧ BoundedMatched rs.1 cs.1 := by
  cases r with
  | returned n => cases c <;> simp [BoundedMatched,Matched] at h
  | fault =>
    cases c <;> simp [BoundedMatched,Matched,Inside,step] at h ⊢
  | live rc =>
    cases c with
    | fault => simp [BoundedMatched,Matched] at h
    | returned n => simp [BoundedMatched,Matched] at h
    | live cc =>
      rcases h with ⟨⟨hstore,hpc,inner,hloops,hcloops⟩,hlo,hhi,inside,hiloops,hheads⟩
      have heq : inside=inner := List.append_cancel_right (hiloops.symm.trans hloops)
      subst inside
      cases rc with
      | mk pc s loops =>
        cases cc with
        | mk pc' s' loops' =>
          simp only at *
          subst loops
          subst loops'
          subst s'
          subst pc'
          have hevent := decoder_step pc s inner hlo hhi hheads hb
          have hinside := reference_inside_step pc s inner hlo hhi hheads hb
          exact ⟨hevent.1,hevent.2,hinside⟩

def execution (initial : Status) : EventSystem Status := ⟨initial,step code⟩

/-- Every finite prefix that stays before the decoder boundary has equal
event labels at every transition and a matching complete successor state.
The premise includes the paired-fault case; it does not claim termination. -/
theorem bounded_runs (r c : Status) (h : BoundedMatched r c) (n : Nat)
    (hbefore : ∀ t, t < n → BeforeBoundary ((execution r).run t)) :
    BoundedMatched ((execution r).run n) ((execution c).run n) ∧
      ∀ t, t < n → (step code ((execution r).run t)).2 =
        (step code ((execution c).run t)).2 := by
  induction n with
  | zero => exact ⟨h,by simp⟩
  | succ n ih =>
    obtain ⟨hn,hevents⟩ := ih (fun t ht => hbefore t (by omega))
    have hstep := bounded_step ((execution r).run n) ((execution c).run n) hn
      (hbefore n (by omega))
    refine ⟨hstep.2,?_⟩
    intro t ht
    by_cases htn : t < n
    · exact hevents t htn
    · have : t=n := by omega
      simpa [this] using hstep.1

end Shared.PNP.Record285.PythonControlRelocationRun
