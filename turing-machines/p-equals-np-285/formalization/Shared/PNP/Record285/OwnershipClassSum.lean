import Shared.PNP.Record285.OwnershipInvariant

/-! Class-sum representation for all 18 logical registers. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore

def classSum (classes : Array Nat) (bank : Nat → Nat) (c : Nat) : Nat :=
  ((List.range 18).map fun i => if classAt classes i = c then bank i else 0).sum

def Isolated (classes : Array Nat) (bank : Nat → Nat) (i : Nat) : Prop :=
  ∀ j, j < 18 → j ≠ i → classAt classes j = classAt classes i → bank j = 0

theorem classSum_ext (classes : Array Nat) (a b : Nat → Nat) (c : Nat)
    (h : ∀ j, j < 18 → classAt classes j = c → a j = b j) :
    classSum classes a c = classSum classes b c := by
  unfold classSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  by_cases hc : classAt classes j = c
  · simp [hc,h j (List.mem_range.mp hj) hc]
  · simp [hc]

theorem map_zero_sum (xs : List Nat) : (xs.map (fun _ => 0)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem indicator_sum (xs : List Nat) (i value : Nat) (hnd : xs.Nodup) (hi : i ∈ xs) :
    (xs.map (fun j => if j = i then value else 0)).sum = value := by
  induction xs with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.mem_cons] at hi
    rcases hi with h | h
    · subst x
      have hz : (xs.map (fun j => if j = i then value else 0)).sum = 0 := by
        have hm : xs.map (fun j => if j = i then value else 0) = xs.map (fun _ => 0) := by
          apply List.map_congr_left
          intro j hj
          have hne : j ≠ i := by intro he; subst j; exact hnd.1 hj
          simp [hne]
        rw [hm]
        exact map_zero_sum xs
      simp [hz]
    · have hne : x ≠ i := by intro he; subst x; exact hnd.1 h
      simp [hne,ih hnd.2 h]

theorem isolated_sum (classes : Array Nat) (bank : Nat → Nat) (i : Nat)
    (hi : i < 18) (hiso : Isolated classes bank i) :
    classSum classes bank (classAt classes i) = bank i := by
  unfold classSum
  have hm : (List.range 18).map (fun j => if classAt classes j = classAt classes i then bank j else 0) =
      (List.range 18).map (fun j => if j = i then bank i else 0) := by
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    by_cases hji : j = i
    · subst j
      simp
    · by_cases hc : classAt classes j = classAt classes i
      · simp [hji,hc,hiso j hj' hji hc]
      · simp [hji,hc]
  rw [hm]
  exact indicator_sum _ i (bank i) List.nodup_range (List.mem_range.mpr hi)

theorem zero_classSum (classes : Array Nat) (c : Nat) :
    classSum classes (fun _ => 0) c = 0 := by
  simp [classSum,map_zero_sum]

/-- Replacing an isolated logical register changes exactly its physical class. -/
theorem classSum_replace (classes : Array Nat) (bank : Nat → Nat) (i value c : Nat)
    (hi : i < 18) (hiso : Isolated classes bank i) :
    classSum classes (fun j => if j = i then value else bank j) c =
      if c = classAt classes i then value else classSum classes bank c := by
  by_cases hc : c = classAt classes i
  · subst c
    have hnew : Isolated classes (fun j => if j = i then value else bank j) i := by
      intro j hj hne hclass
      simpa [hne] using hiso j hj hne hclass
    simpa using isolated_sum classes (fun j => if j = i then value else bank j) i hi hnew
  · simp only [hc,if_false]
    apply classSum_ext
    intro j hj hjclass
    have hne : j ≠ i := by
      intro he
      subst j
      exact hc hjclass.symm
    simp [hne]

/-- A move between distinct isolated classes transfers the entire source
class into the destination and leaves every other class untouched. -/
theorem classSum_move (classes : Array Nat) (bank : Nat → Nat) (src dst c : Nat)
    (hs : src < 18) (hd : dst < 18)
    (hclasses : classAt classes src ≠ classAt classes dst)
    (hsrc : Isolated classes bank src) (hdst : Isolated classes bank dst) :
    classSum classes (update (.move src dst) bank) c =
      if c = classAt classes src then 0 else
      if c = classAt classes dst then bank dst + bank src else classSum classes bank c := by
  have hne : src ≠ dst := by intro he; subst dst; exact hclasses rfl
  by_cases hcsrc : c = classAt classes src
  · subst c
    have hiso : Isolated classes (update (.move src dst) bank) src := by
      intro j hj hjne hjclass
      have hjdst : j ≠ dst := by
        intro he
        subst j
        exact hclasses hjclass.symm
      simpa [update,hjne,hjdst] using hsrc j hj hjne hjclass
    simpa [update] using isolated_sum classes (update (.move src dst) bank) src hs hiso
  · simp only [hcsrc,if_false]
    by_cases hcdst : c = classAt classes dst
    · subst c
      have hiso : Isolated classes (update (.move src dst) bank) dst := by
        intro j hj hjne hjclass
        have hjsrc : j ≠ src := by
          intro he
          subst j
          exact hclasses hjclass
        simpa [update,hjsrc,hjne] using hdst j hj hjne hjclass
      simpa [update,Ne.symm hne] using isolated_sum classes (update (.move src dst) bank) dst hd hiso
    · simp only [hcdst,if_false]
      apply classSum_ext
      intro j hj hjclass
      have hjsrc : j ≠ src := by
        intro he
        subst j
        exact hcsrc hjclass.symm
      have hjdst : j ≠ dst := by
        intro he
        subst j
        exact hcdst hjclass.symm
      simp [update,hjsrc,hjdst]

end Shared.PNP.Record285.OwnershipCore
