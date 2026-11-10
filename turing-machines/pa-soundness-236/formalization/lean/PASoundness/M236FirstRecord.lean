import PASoundness.M236Observer

/-!
The first-record convention of the historical omega observer, restricted to
the existing timed receipt interface. For `decodedEvents`, a receipt at
transition `t` is eligible when no error has occurred through the
post-transition boundary `t + 1`. The least eligible receipt is selected, or
false is returned when there is no such receipt. For `wordDecodedEvents`,
`out` instead denotes cumulative receipt membership at a prefix boundary;
the comparison with it below uses `Complete`, so no error is present and the
offset does not affect the value. No equivalence is claimed for malformed word
traces. This does not identify `Complete` or `FrameProgress` with every clause
of the historical `WellFormedTotal` specification.
-/
namespace PASoundness.M236FirstRecord

open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer

def Eligible (E : EventStructure) (a : Address) (t : Nat) (b : Bool) : Prop :=
  E.out b t a ∧ ∀ u, u ≤ t + 1 → ¬ E.error u

def HasRecord (E : EventStructure) (a : Address) : Prop :=
  ∃ t, ∃ b, Eligible E a t b

noncomputable def firstTime (E : EventStructure) (a : Address) (h : HasRecord E a) : Nat := by
  classical
  exact Nat.find h

/-- The first completed record before error, with false for missing records.
The selection is classical because an infinite trace need not decide whether
any receipt ever occurs. -/
noncomputable def value (E : EventStructure) (a : Address) : Bool := by
  classical
  exact if h : HasRecord E a then Classical.choose (Nat.find_spec h) else false

theorem value_default (E : EventStructure) (a : Address) (h : ¬ HasRecord E a) :
    value E a = false := by
  classical
  simp [value, h]

theorem value_eligible (E : EventStructure) (a : Address) (h : HasRecord E a) :
    Eligible E a (firstTime E a h) (value E a) := by
  classical
  simpa only [firstTime, value, dif_pos h] using (Classical.choose_spec (Nat.find_spec h))

theorem first_time_le (E : EventStructure) (a : Address) (h : HasRecord E a)
    {t : Nat} {b : Bool} (hr : Eligible E a t b) : firstTime E a h ≤ t := by
  classical
  exact Nat.find_min' h ⟨b, hr⟩

theorem no_earlier_eligible (E : EventStructure) (a : Address) (h : HasRecord E a)
    {t : Nat} (ht : t < firstTime E a h) (b : Bool) : ¬ Eligible E a t b := by
  intro hr
  have hle := first_time_le E a h hr
  omega

/-- The online decoder can append at most one receipt in a transition. -/
theorem online_receipt_unique (trace : Nat → Option Bool) (t : Nat)
    (a c : Address) (b d : Bool)
    (h₁ : (decodedEvents trace).out b t a)
    (h₂ : (decodedEvents trace).out d t c) : (a, b) = (c, d) := by
  have h : (decoderRun trace t).numbers.records ++ [(a, b)] =
      (decoderRun trace t).numbers.records ++ [(c, d)] := h₁.symm.trans h₂
  have hs := List.append_cancel_left h
  simpa only [List.cons.injEq, and_true] using hs

/-- On online traces, even if a later error occurs, an explicitly first
eligible completed receipt determines the selected value. -/
theorem online_value_of_first (trace : Nat → Option Bool) (a : Address)
    (t : Nat) (b : Bool) (hr : Eligible (decodedEvents trace) a t b)
    (hfirst : ∀ s, s < t → ∀ c, ¬ Eligible (decodedEvents trace) a s c) :
    value (decodedEvents trace) a = b := by
  let E := decodedEvents trace
  have hex : HasRecord E a := ⟨t, b, hr⟩
  have hle := first_time_le E a hex hr
  have hnot : ¬ firstTime E a hex < t := by
    intro hlt
    exact hfirst _ hlt _ (value_eligible E a hex)
  have htime : firstTime E a hex = t := by omega
  have hs := (value_eligible E a hex).1
  rw [htime] at hs
  exact congrArg Prod.snd (online_receipt_unique trace t a a _ b hs hr.1)

theorem value_default_of_no_receipt (E : EventStructure) (a : Address)
    (h : ∀ t b, ¬ E.out b t a) : value E a = false := by
  apply value_default
  rintro ⟨t, b, hr, _⟩
  exact h t b hr

theorem hasRecord_of_emitted (E : EventStructure) (a : Address) (b : Bool)
    (he : ¬ ∃ t, E.error t) (ho : Emitted E b a) : HasRecord E a := by
  obtain ⟨t, ht⟩ := ho
  exact ⟨t, b, ht, fun u _ hu => he ⟨u, hu⟩⟩

theorem value_eq_of_emitted (E : EventStructure) (a : Address) (b : Bool)
    (he : ¬ ∃ t, E.error t)
    (hn : ¬ (Emitted E false a ∧ Emitted E true a))
    (ho : Emitted E b a) : value E a = b := by
  have h := hasRecord_of_emitted E a b he ho
  have hv : Emitted E (value E a) a := ⟨firstTime E a h, (value_eligible E a h).1⟩
  cases hb : b <;> cases hvb : value E a <;> simp_all

/-- On a complete trace, the first/default value is exactly the unique
recorded value at each admissible address. In particular the default branch
cannot be used to replace a missing receipt. -/
theorem value_eq_iff_emitted (E : EventStructure) (hc : Complete E)
    (a : Address) (ha : Admissible E.profile a) (b : Bool) :
    value E a = b ↔ Emitted E b a := by
  constructor
  · intro hv
    have hex : HasRecord E a := by
      rcases hc.1.2.1 a ha with hzero | hone
      · exact hasRecord_of_emitted E a false hc.1.1 hzero
      · exact hasRecord_of_emitted E a true hc.1.1 hone
    have hr := (value_eligible E a hex).1
    rw [hv] at hr
    exact ⟨firstTime E a hex, hr⟩
  · exact value_eq_of_emitted E a b hc.1.1 (hc.1.2.2 a)

noncomputable def values (E : EventStructure) : PASoundness.RecordValues :=
  fun n p xs => value E ⟨n, p, xs⟩

theorem recordsAgree (E : EventStructure) (hc : Complete E)
    (hp : E.profile = .legacy) : RecordsAgree E (values E) := by
  intro n p xs hn hlen
  have ha : Admissible E.profile ⟨n, p, xs⟩ := by
    simp [Admissible, hp, hlen, hn]
  exact (value_eq_iff_emitted E hc _ ha true).symm

/-- With the existing guard, the positive-rank receipt observer is exactly the
rank predicate evaluated on the first-record/default value function. -/
theorem accept_iff_firstValues (E : EventStructure) (hp : E.profile = .legacy) :
    Accept E ↔ Complete E ∧ ∀ n, 0 < n → ¬ PASoundness.RankFailure (values E) n := by
  unfold Accept
  apply and_congr_right
  intro hc
  apply forall_congr'
  intro n
  apply imp_congr_right
  intro hn
  exact not_congr (rawFailure_iff_rankFailure E (values E) (recordsAgree E hc hp) n hn)

/-- The same comparison for the full existing wire observer retains its
separate frame-progress guard. It does not prove the historical guard equals
these conditions. -/
theorem traceAccept_iff_firstValues {C : Type} (M : WordEventSystem C Bool) :
    TraceAccept M ↔ Complete (wordDecodedEvents M) ∧
      (∀ n, 0 < n → ¬ PASoundness.RankFailure (values (wordDecodedEvents M)) n) ∧
      FrameProgress M := by
  unfold TraceAccept
  rw [accept_iff_firstValues _ rfl]
  exact and_assoc

end PASoundness.M236FirstRecord
