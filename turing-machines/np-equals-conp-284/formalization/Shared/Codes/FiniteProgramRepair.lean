import Shared.Codes.FiniteProgramTotalize

/-! Normalize arbitrary finite programs into valid tables. Invalid rows and
out-of-range next states are sent to a nonaccepting loop. This module does
not assert any machine-model simulation or bit-cost bound. -/
namespace Shared.Codes.FiniteProgramRepair

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize (sinkRow)

def repairRow (m : Nat) (row : Row) : Row :=
  if row.2.2.2 = 0 then
    if row.2.2.1 < m then row else sinkRow m
  else if row.2.2.2 = 1 ∨ row.2.2.2 = 2 then row else sinkRow m

def repairPair (m : Nat) (rows : Row × Row) : Row × Row :=
  (repairRow m rows.1,repairRow m rows.2)

def repair (p : Program) : Program :=
  p.map (repairPair p.length) ++ [(sinkRow p.length,sinkRow p.length)]

@[simp] theorem repair_length (p : Program) : (repair p).length = p.length+1 := by
  simp [repair]

theorem repairRow_valid (m : Nat) (row : Row) : validRow (m+1) (repairRow m row) = true := by
  rcases row with ⟨w,d,next,tag⟩
  simp only [repairRow]
  split_ifs with hz hn hh
  · simp [validRow,hz]; omega
  · simp [validRow,sinkRow] <;> omega
  · simp [validRow]; omega
  · simp [validRow,sinkRow] <;> omega

theorem repair_valid (p : Program) : valid (repair p) = true := by
  have hne : (repair p).isEmpty = false := by simp [repair]
  simp only [valid,repair_length,hne,Bool.not_false,Bool.true_and]
  rw [List.all_eq_true]
  intro rows hrows
  simp only [repair,List.mem_append,List.mem_map,List.mem_singleton] at hrows
  rcases hrows with ⟨pair,hpair,rfl⟩ | rfl
  · simp [repairPair,repairRow_valid]
  · simp [validRow,sinkRow]

theorem repair_original (p : Program) (q : Nat) (pair : Row × Row) (h : p[q]? = some pair) :
    (repair p)[q]? = some (repairPair p.length pair) := by
  have hq : q < p.length := (List.getElem?_eq_some_iff.mp h).1
  have he : p[q] = pair := (List.getElem?_eq_some_iff.mp h).2
  simp [repair,List.getElem?_append_left,hq,he]

theorem repair_sink (p : Program) :
    (repair p)[p.length]? = some (sinkRow p.length,sinkRow p.length) := by
  simp [repair,List.getElem?_append_right]

theorem repair_sink_step (p : Program) (t : Tape) :
    step (repair p) (p.length,t) = some (.inr (p.length,moveTape false false t)) := by
  unfold step
  rw [repair_sink]
  simp [sinkRow]

def Sink (p : Program) (s : Status) : Prop :=
  ∃ t, s = some (.inr (p.length,t))

def Related (p : Program) (original normalized : Status) : Prop :=
  match original with
  | none => Sink p normalized
  | some (.inl b) => normalized = some (.inl b)
  | some (.inr c) => if c.1 < p.length then normalized = some (.inr c) else Sink p normalized

theorem execute_repair_related (p : Program) (row : Row) (t : Tape) :
    Related p (executeRow row t) (executeRow (repairRow p.length row) t) := by
  rcases row with ⟨w,d,next,tag⟩
  cases tag with
  | zero =>
    by_cases h : next < p.length
    · simp [executeRow,repairRow,Related,h]
    · simp [executeRow,repairRow,Related,Sink,sinkRow,h]
  | succ tag =>
    cases tag with
    | zero => simp [executeRow,repairRow,Related]
    | succ tag =>
      cases tag with
      | zero => simp [executeRow,repairRow,Related]
      | succ tag => simp [executeRow,repairRow,Related,Sink,sinkRow]

theorem step_repair_related (p : Program) (c : Config) (hc : c.1 < p.length) :
    Related p (step p c) (step (repair p) c) := by
  cases hp : p[c.1]? with
  | none =>
    have he := List.getElem?_eq_none_iff.mp hp
    omega
  | some pair =>
    have hr := repair_original p c.1 pair hp
    cases hbit : c.2.2.1 with
    | false =>
      have h := execute_repair_related p pair.1 c.2
      simpa only [step,hp,hr,hbit,Bool.false_eq_true,↓reduceIte,repairPair,Prod.fst,executeRow] using h
    | true =>
      have h := execute_repair_related p pair.2 c.2
      simpa only [step,hp,hr,hbit,↓reduceIte,repairPair,Prod.snd,executeRow] using h

theorem advance_repair_related (p : Program) (original normalized : Status)
    (h : Related p original normalized) :
    Related p (advance p original) (advance (repair p) normalized) := by
  cases original with
  | none =>
    obtain ⟨t,rfl⟩ := h
    simp only [advance,repair_sink_step,Related,Sink]
    exact ⟨_,rfl⟩
  | some v =>
    cases v with
    | inl b =>
      change normalized = some (.inl b) at h
      subst normalized
      rfl
    | inr c =>
      by_cases hc : c.1 < p.length
      · have hh : normalized = some (.inr c) := by simpa [Related,hc] using h
        subst normalized
        exact step_repair_related p c hc
      · have hh : Sink p normalized := by simpa [Related,hc] using h
        obtain ⟨t,rfl⟩ := hh
        have hn : p[c.1]? = none := List.getElem?_eq_none (by omega)
        have hs : step p c = none := by simp only [step,hn]
        simp only [advance,hs,repair_sink_step,Related,Sink]
        exact ⟨_,rfl⟩

theorem initial_related (p : Program) (input : List Bool) :
    Related p (some (.inr (initial input))) (some (.inr (initial input))) := by
  by_cases h : 0 < p.length
  · simp [Related,initial,h]
  · have hz : p.length = 0 := by omega
    simp [Related,initial,h,Sink,hz]

theorem run_related (p : Program) (input : List Bool) (fuel : Nat) :
    Related p (run p (initial input) fuel) (run (repair p) (initial input) fuel) := by
  induction fuel with
  | zero => exact initial_related p input
  | succ fuel ih => exact advance_repair_related p _ _ ih

theorem bounded_repair (p : Program) (input : List Bool) (fuel : Nat) :
    bounded (repair p) input fuel = bounded p input fuel := by
  have h := run_related p input fuel
  unfold bounded
  cases ho : run p (initial input) fuel with
  | none =>
    rw [ho] at h
    obtain ⟨t,ht⟩ := h
    simp [ho,ht]
  | some v =>
    cases v with
    | inl b =>
      rw [ho] at h
      change run (repair p) (initial input) fuel = some (.inl b) at h
      simp [ho,h]
    | inr c =>
      rw [ho] at h
      by_cases hc : c.1 < p.length
      · have hh : run (repair p) (initial input) fuel = some (.inr c) := by simpa [Related,hc] using h
        simp [ho,hh]
      · have hh : Sink p (run (repair p) (initial input) fuel) := by simpa [Related,hc] using h
        obtain ⟨t,ht⟩ := hh
        simp [ho,ht]

theorem repairRow_primrec : Primrec₂ repairRow := by
  let A := Nat × Row
  have hm : Primrec (fun z : A => z.1) := Primrec.fst
  have hr : Primrec (fun z : A => z.2) := Primrec.snd
  have hn : Primrec (fun z : A => z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec (fun z : A => z.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hsink : Primrec (fun z : A => sinkRow z.1) :=
    Primrec.pair (Primrec.const false) (Primrec.pair (Primrec.const true) (Primrec.pair hm (Primrec.const 0)))
  have h := Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
    (Primrec.ite (Primrec.nat_lt.comp hn hm) hr hsink)
    (Primrec.ite ((Primrec.eq.comp ht (Primrec.const 1)).or (Primrec.eq.comp ht (Primrec.const 2))) hr hsink)
  apply h.to₂.of_eq
  intro m row
  simp only [repairRow]

theorem repairPair_primrec : Primrec₂ repairPair := by
  exact (Primrec.pair (repairRow_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (repairRow_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂

theorem repair_primrec : Primrec repair := by
  have hpair : Primrec₂ (fun (p : Program) (rows : Row × Row) => repairPair p.length rows) :=
    (repairPair_primrec.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd).to₂
  have hmap := Primrec.list_map (Primrec.id : Primrec (id : Program → Program)) hpair
  have hlen : Primrec (fun p : Program => p.length) := Primrec.list_length
  have hsink : Primrec (fun p : Program => sinkRow p.length) :=
    Primrec.pair (Primrec.const false) (Primrec.pair (Primrec.const true) (Primrec.pair hlen (Primrec.const 0)))
  have hsinks := Primrec.list_cons.comp (Primrec.pair hsink hsink) (Primrec.const ([] : Program))
  exact Primrec.list_append.comp hmap hsinks

theorem repair_computable : Computable repair := repair_primrec.to_comp

theorem valid_bounded_equivalent (p : Program) :
    ∃ q, valid q = true ∧ ∀ input fuel, bounded q input fuel = bounded p input fuel :=
  ⟨repair p,repair_valid p,bounded_repair p⟩

namespace Fixtures
def badNext : Program := [((false,true,7,0),(false,true,7,0))]
def badTag : Program := [((false,true,0,9),(false,true,0,9))]
example : valid (repair []) = true := by decide
example : bounded (repair badNext) [] 1 = none := by decide
example : bounded (repair badTag) [] 4 = none := by decide
example : bounded (repair [((false,true,999,2),(false,true,999,2))]) [] 1 = some true := by decide
end Fixtures

end Shared.Codes.FiniteProgramRepair
