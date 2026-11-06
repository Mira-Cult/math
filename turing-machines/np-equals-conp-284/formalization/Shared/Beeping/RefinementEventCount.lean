import Shared.Beeping.Refinement

/-! Event occurrence and uniqueness are preserved by positive-segment
refinement, including arbitrary finite stuttering. -/
namespace Shared.Beeping
namespace EventSystem
variable {C : Type} (M : EventSystem C)
def HasBeep : Prop := ∃ t, M.BeepAt t
def AtMostOneBeep : Prop := ∀ t u, M.BeepAt t → M.BeepAt u → t = u
end EventSystem

namespace EventRefinement
variable {S T : Type} {source : EventSystem S} {target : EventSystem T}
variable (r : EventRefinement source target)

theorem hasBeep_iff (r : EventRefinement source target) : source.HasBeep ↔ target.HasBeep := by
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨j,_,_,hj⟩ := (r.event_iff i).1 hi
    exact ⟨j,hj⟩
  · rintro ⟨j,hj⟩
    obtain ⟨i,lo,hi⟩ := r.covers j
    exact ⟨i,(r.event_iff i).2 ⟨j,lo,hi,hj⟩⟩

theorem atMostOneBeep_iff (r : EventRefinement source target) : source.AtMostOneBeep ↔ target.AtMostOneBeep := by
  constructor
  · intro hs j k hj hk
    obtain ⟨i,ji,jj⟩ := r.covers j
    obtain ⟨l,kl,kk⟩ := r.covers k
    have hi := (r.event_iff i).2 ⟨j,ji,jj,hj⟩
    have hl := (r.event_iff l).2 ⟨k,kl,kk,hk⟩
    have he := hs i l hi hl
    subst l
    exact r.event_unique i j k ji jj kl kk hj hk
  · intro ht i l hi hl
    obtain ⟨j,ji,jj,hj⟩ := (r.event_iff i).1 hi
    obtain ⟨k,kl,kk,hk⟩ := (r.event_iff l).1 hl
    have he := ht j k hj hk
    subst k
    exact r.segment_unique ji jj kl kk
end EventRefinement
end Shared.Beeping
