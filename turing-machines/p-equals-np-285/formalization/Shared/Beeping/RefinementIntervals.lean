import Shared.Beeping.Refinement

/-! Event-exact refinements preserve event existence and uniqueness on any
finite interval of source actions, with endpoints mapped by the boundary. -/
namespace Shared.Beeping

namespace EventSystem

def HasEvent {S : Type} (M : EventSystem S) (lo hi : Nat) : Prop :=
  ∃ i, lo ≤ i ∧ i < hi ∧ M.BeepAt i

def UniqueEvents {S : Type} (M : EventSystem S) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < hi → lo ≤ j → j < hi → M.BeepAt i → M.BeepAt j → i = j

end EventSystem
namespace EventRefinement

variable {S T : Type} {source : EventSystem S} {target : EventSystem T}

/-- An event appears in a source interval exactly when one appears between
its two target boundaries. -/
theorem interval_event_iff (r : EventRefinement source target) (lo hi : Nat) :
    source.HasEvent lo hi ↔ target.HasEvent (r.boundary lo) (r.boundary hi) := by
  constructor
  · rintro ⟨i,hlo,hhi,he⟩
    obtain ⟨j,hjlo,hjhi,hj⟩ := (r.event_iff i).1 he
    have h1 := r.boundary_mono hlo
    have h2 := r.boundary_mono (show i+1 ≤ hi by omega)
    exact ⟨j,by omega,by omega,hj⟩
  · rintro ⟨j,hlo,hhi,he⟩
    obtain ⟨i,hilo,hihi,hjlo,hjhi⟩ := r.covers_between hlo hhi
    exact ⟨i,hilo,hihi,(r.event_iff i).2 ⟨j,hjlo,hjhi,he⟩⟩

/-- At-most-one event is preserved in both directions, including an empty
interval and intervals spanning many variable-length segments. -/
theorem interval_unique_iff (r : EventRefinement source target) (lo hi : Nat) :
    source.UniqueEvents lo hi ↔ target.UniqueEvents (r.boundary lo) (r.boundary hi) := by
  constructor
  · intro hu a b halo hahi hblo hbhi ha hb
    obtain ⟨i,hilo,hihi,ha1,ha2⟩ := r.covers_between halo hahi
    obtain ⟨j,hjlo,hjhi,hb1,hb2⟩ := r.covers_between hblo hbhi
    have hai := (r.event_iff i).2 ⟨a,ha1,ha2,ha⟩
    have hbj := (r.event_iff j).2 ⟨b,hb1,hb2,hb⟩
    have hij := hu i j hilo hihi hjlo hjhi hai hbj
    subst j
    exact r.event_unique i a b ha1 ha2 hb1 hb2 ha hb
  · intro hu i j hilo hihi hjlo hjhi hei hej
    obtain ⟨a,ha1,ha2,ha⟩ := (r.event_iff i).1 hei
    obtain ⟨b,hb1,hb2,hb⟩ := (r.event_iff j).1 hej
    have hli := r.boundary_mono hilo
    have hhi := r.boundary_mono (show i+1 ≤ hi by omega)
    have hlj := r.boundary_mono hjlo
    have hhj := r.boundary_mono (show j+1 ≤ hi by omega)
    have hab := hu a b (by omega) (by omega) (by omega) (by omega) ha hb
    subst b
    exact r.segment_unique ha1 ha2 hb1 hb2

end EventRefinement
end Shared.Beeping
