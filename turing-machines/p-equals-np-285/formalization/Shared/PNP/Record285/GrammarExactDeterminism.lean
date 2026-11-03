import Shared.PNP.Record285.GrammarExactStep

/-! Uniqueness of the selected register decomposition and exact action data. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.CleanBank

theorem split_unique (before before' after after' : List Nat) (target target' : Nat)
    (hlen : before.length = before'.length)
    (heq : before++[target]++after = before'++[target']++after') :
    before = before' ∧ target = target' ∧ after = after' := by
  simp only [List.append_assoc] at heq
  have hbefore : before = before' := by
    have h := congrArg (List.take before.length) heq
    rw [List.take_append_length,hlen,List.take_append_length] at h
    exact h
  subst before'
  have hrest := List.append_cancel_left heq
  simp only [List.singleton_append,List.cons.injEq] at hrest
  exact ⟨rfl,hrest.1,hrest.2⟩

theorem split_parts (before after : List Nat) (target : Nat) :
    let fields := before++[target]++after
    fields.take before.length = before ∧
      (fields.drop before.length).headD 0 = target ∧
      (fields.drop before.length).tail = after := by
  simp [List.append_assoc]

def applyUpdate (e : Edge) (fields : List Nat) : List Nat :=
  match e with
  | .inc i =>
    let before := fields.take i
    let rest := fields.drop i
    before++[rest.headD 0+1]++rest.tail
  | .dec i =>
    let before := fields.take i
    let rest := fields.drop i
    decrementFields before rest.tail (rest.headD 0)
  | .half i =>
    let before := fields.take i
    let rest := fields.drop i
    let target := rest.headD 0
    let after := rest.tail
    if target = 0 then before++[0]++after
    else if target = 1 then before++[0]++after++[0]
    else if target%2 = 0 then
      let n := (target-2)/2
      before++[n+1]++(after++List.replicate n 0)++[0]
    else
      let n := (target-3)/2
      before++[n+1]++(after++List.replicate n 0)++[0,0]
  | _ => fields

theorem update_sound (e : Edge) (fields result : List Nat) (h : Update e fields result) :
    applyUpdate e fields = result := by
  cases h with
  | inc before fields target =>
    have hp := split_parts before fields target
    simp only [applyUpdate,hp.1,hp.2.1,hp.2.2]
  | dec before fields target =>
    have hp := split_parts before fields target
    simp only [applyUpdate,hp.1,hp.2.1,hp.2.2]
  | half before fields newFields target hh =>
    have hp := split_parts before fields target
    simp only [applyUpdate,hp.1,hp.2.1,hp.2.2]
    cases hh with
    | zero => simp
    | one => simp
    | even n =>
      have hz : 2*n+2 ≠ 0 := by omega
      have ho : 2*n+2 ≠ 1 := by omega
      have hm : (2*n+2)%2 = 0 := by omega
      have hd : (2*n+2-2)/2 = n := by omega
      simp [ho,hm]
    | odd n =>
      have hz : 2*n+3 ≠ 0 := by omega
      have ho : 2*n+3 ≠ 1 := by omega
      have hm : (2*n+3)%2 ≠ 0 := by omega
      have hd : (2*n+3-3)/2 = n := by omega
      simp [ho]
  | beep fields => rfl
  | brk i fields => rfl
  | cont i fields => rfl

theorem update_unique (e : Edge) (fields a b : List Nat)
    (ha : Update e fields a) (hb : Update e fields b) : a = b :=
  (update_sound e fields a ha).symm.trans (update_sound e fields b hb)

/-- The duration is computable from the edge, full bank, code and gap. -/
def durationFor (e : Edge) (fields : List Nat) (code : List Bool) (gap : Nat) : Nat :=
  match e with
  | .inc i => incTime code gap ((fields.drop i).headD 0) (fields.take i) (fields.drop i).tail
  | .dec i =>
    let target := (fields.drop i).headD 0
    if target = 0 then decZeroTime code gap (fields.take i)
    else decPositiveTime code gap (target-1) (fields.take i) (fields.drop i).tail
  | .half i =>
    let target := (fields.drop i).headD 0
    let before := fields.take i
    let after := (fields.drop i).tail
    if target = 0 then halfZeroTime code gap before
    else if target = 1 then halfOneTime code gap before after
    else if target%2 = 0 then halfEvenTime code gap ((target-2)/2) before after
    else halfOddTime code gap ((target-3)/2) before after
  | .beep => Grammar.beepDuration false gap
  | .brk 0 => breakZeroTime code code.dropLast gap
  | .brk 1 => breakOneTime code code.dropLast gap
  | .brk 2 => breakTwoTime code code.dropLast gap
  | .cont 1 => continueOneTime code code.dropLast
  | .cont 2 => continueTwoTime code code.dropLast
  | _ => 0

theorem duration_sound (e : Edge) (fields : List Nat) (code : List Bool) (gap steps : Nat)
    (h : Duration e fields code gap steps) : durationFor e fields code gap = steps := by
  cases h with
  | inc before fields target code gap =>
    have hp := split_parts before fields target
    simp only [durationFor,hp.1,hp.2.1,hp.2.2]
  | decZero before fields code gap =>
    have hp := split_parts before fields 0
    simp only [durationFor,hp.1,hp.2.1,hp.2.2,if_true]
  | decPositive before fields k code gap =>
    have hp := split_parts before fields (k+1)
    simp only [durationFor,hp.1,hp.2.1,hp.2.2,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
  | halfZero before fields code gap =>
    have hp := split_parts before fields 0
    simp only [durationFor,hp.1,hp.2.1,hp.2.2,if_true]
  | halfOne before fields code gap =>
    have hp := split_parts before fields 1
    simp only [durationFor,hp.1,hp.2.1,hp.2.2,Nat.one_ne_zero,if_false,if_true]
  | halfEven before fields n code gap =>
    have hp := split_parts before fields (2*n+2)
    have hz : 2*n+2 ≠ 0 := by omega
    have ho : 2*n+2 ≠ 1 := by omega
    have hm : (2*n+2)%2 = 0 := by omega
    have hd : (2*n+2-2)/2 = n := by omega
    simp only [durationFor,hp.1,hp.2.1,hp.2.2,hz,ho,hm,hd,if_false,if_true]
  | halfOdd before fields n code gap =>
    have hp := split_parts before fields (2*n+3)
    have hz : 2*n+3 ≠ 0 := by omega
    have ho : 2*n+3 ≠ 1 := by omega
    have hm : (2*n+3)%2 ≠ 0 := by omega
    have hd : (2*n+3-3)/2 = n := by omega
    simp only [durationFor,hp.1,hp.2.1,hp.2.2,hz,ho,hm,hd,if_false]
  | beep fields code gap => rfl
  | brkZero fields code pre gap hcode => simp [durationFor,hcode]
  | brkOne fields code pre gap hcode => simp [durationFor,hcode]
  | brkTwo fields code pre gap hcode => simp [durationFor,hcode]
  | contOne fields code pre gap hcode => simp [durationFor,hcode]
  | contTwo fields code pre gap hcode => simp [durationFor,hcode]

theorem duration_unique (e : Edge) (fields : List Nat) (code : List Bool) (gap a b : Nat)
    (ha : Duration e fields code gap a) (hb : Duration e fields code gap b) : a = b :=
  (duration_sound e fields code gap a ha).symm.trans (duration_sound e fields code gap b hb)

end Shared.PNP.Record285.GrammarExact
