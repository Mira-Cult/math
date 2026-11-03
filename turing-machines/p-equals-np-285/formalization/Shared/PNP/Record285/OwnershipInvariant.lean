import Shared.PNP.Record285.OwnershipCheck

/-! Soundness of the 18-register ownership mask checker. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreZero

def validBank (mask : Array Nat) (bank : Nat → Nat) : Prop :=
  ∀ i, i < 18 → admits (slot mask i) (bank i) = true

theorem category_add (a b : Nat) : category (category a + category b) = category (a+b) := by
  by_cases ha0 : a = 0 <;> by_cases ha1 : a = 1 <;>
    by_cases hb0 : b = 0 <;> by_cases hb1 : b = 1 <;>
    simp [category,ha0,ha1,hb0,hb1] <;> omega

theorem others_sound (before after : Array Nat) (first second i value : Nat)
    (h : others before after first second = true) (hi : i < 18)
    (hfirst : i ≠ first) (hsecond : i ≠ second)
    (hadmit : admits (slot before i) value = true) : admits (slot after i) value = true := by
  have hs := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have hsub : subset (slot before i) (slot after i) = true := by
    simpa [hfirst,hsecond] using hs
  exact subset_sound _ _ _ hsub hadmit

theorem singleBranch_sound (e : Edge) (i : Nat) (before after : Array Nat) (branch : Bool)
    (h : singleBranch e i before after branch = true) (value : Nat)
    (hadmit : admits (slot before i) value = true) (hbranch : operationBranch e value = branch) :
    admits (slot after i) (operationValue e value) = true ∧
      ∀ j, j < 18 → j ≠ i → ∀ x, admits (slot before j) x = true → admits (slot after j) x = true := by
  let rep := representative value
  have hrep : rep ∈ List.range 6 := List.mem_range.mpr (representative_lt_six value)
  have hcase := List.all_eq_true.mp h rep hrep
  have hinput : admits (slot before i) rep = true := by simpa only [rep,admits_representative] using hadmit
  have htest : operationBranch e rep = branch := by simpa only [rep,representative_branch] using hbranch
  simp only [hinput,htest,beq_self_eq_true,Bool.true_and,if_true,Bool.and_eq_true_iff] at hcase
  refine ⟨?_,?_⟩
  · simpa only [rep,admits_operation_representative] using hcase.1
  · intro j hj hne x hx
    exact others_sound before after i i j x hcase.2 hj hne hne hx

theorem single_sound (e : Edge) (i : Nat) (before no yes : Array Nat) (bank : Nat → Nat)
    (hi : i < 18) (hno : singleBranch e i before no false = true)
    (hyes : singleBranch e i before yes true = true) (hbank : validBank before bank) :
    validBank (if operationBranch e (bank i) then yes else no)
      (fun j => if j = i then operationValue e (bank i) else bank j) := by
  cases hb : operationBranch e (bank i) with
  | false =>
    have hs := singleBranch_sound e i before no false hno (bank i) (hbank i hi) hb
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [hb] using hs.1
    · simpa [hb,hji] using hs.2 j hj hji (bank j) (hbank j hj)
  | true =>
    have hs := singleBranch_sound e i before yes true hyes (bank i) (hbank i hi) hb
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [hb] using hs.1
    · simpa [hb,hji] using hs.2 j hj hji (bank j) (hbank j hj)

theorem move_sound (src dst : Nat) (before after : Array Nat) (bank : Nat → Nat)
    (h : moveTransfer src dst before after = true) (hbank : validBank before bank) :
    validBank after (update (.move src dst) bank) := by
  simp only [moveTransfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsrc,hdst,hne⟩,hzero⟩,hother⟩,hadd⟩ := h
  have ha := List.all_eq_true.mp hadd (category (bank src)) (List.mem_range.mpr (category_lt_three _))
  have hab := List.all_eq_true.mp ha (category (bank dst)) (List.mem_range.mpr (category_lt_three _))
  have h1 : admits (slot before src) (category (bank src)) = true := by
    simpa only [admits_category] using hbank src hsrc
  have h2 : admits (slot before dst) (category (bank dst)) = true := by
    simpa only [admits_category] using hbank dst hdst
  simp [h1,h2] at hab
  have hsum : admits (slot after dst) (bank dst + bank src) = true := by
    have hc : category (category (bank src) + category (bank dst)) = category (bank dst + bank src) := by
      rw [category_add,Nat.add_comm]
    simpa only [admits,hc] using hab
  intro j hj
  by_cases hjs : j = src
  · subst j
    simpa [update] using hzero
  · by_cases hjd : j = dst
    · subst j
      simpa [update,Ne.symm hne] using hsum
    · have hv := others_sound before after src dst j (bank j) hother hj hjs hjd (hbank j hj)
      simpa [update,hjs,hjd] using hv

theorem transfer_sound (row : Row) (before no yes : Array Nat) (bank : Nat → Nat)
    (h : transfer row before no yes = true) (hbank : validBank before bank) :
    validBank (if observe row.action bank then yes else no) (update row.action bank) := by
  cases row with
  | mk action noidx yesidx =>
    cases action with
    | inc i =>
      simp only [transfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      have hs := single_sound (.inc i) i before no yes bank h.1.1 h.1.2 h.2 hbank
      change validBank no (fun j => if j = i then bank i + 1 else bank j)
      simpa [operationBranch,operationValue] using hs
    | dec i =>
      simp only [transfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      have hs := single_sound (.dec i) i before no yes bank h.1.1 h.1.2 h.2 hbank
      simp only [observe,decide_eq_true_eq]
      change validBank (if bank i = 0 then yes else no) (fun j => if j = i then bank i - 1 else bank j)
      simpa [operationBranch,operationValue] using hs
    | half i =>
      simp only [transfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      have hs := single_sound (.half i) i before no yes bank h.1.1 h.1.2 h.2 hbank
      simp only [observe,decide_eq_true_eq]
      change validBank (if bank i % 2 = 0 then yes else no) (fun j => if j = i then bank i / 2 else bank j)
      simpa [operationBranch,operationValue] using hs
    | move src dst =>
      have hm : moveTransfer src dst before no = true := h
      simpa [observe] using move_sound src dst before no bank hm hbank
    | beep =>
      have ho : others before no 18 18 = true := h
      intro j hj
      have hne : j ≠ 18 := by omega
      have hv := others_sound before no 18 18 j (bank j) ho hj hne hne (hbank j hj)
      simpa [observe,update] using hv

def Valid (rows : Array Row) (masks : Array (Array Nat)) (s : State) : Prop :=
  s.index < rows.size ∧ ∃ mask, masks[s.index]? = some mask ∧ validBank mask s.bank

theorem invariant_parts (rows : Array Row) (masks : Array (Array Nat))
    (h : invariantCheck rows masks = true) :
    rows.size = masks.size ∧
      (List.range 18).all (fun i => admits (slot (masks[0]?.getD #[]) i) 0) = true ∧
      (List.range rows.size).all (invariantRow rows masks) = true := by
  simp only [invariantCheck,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact ⟨h.1.1.1,h.1.2,h.2⟩

theorem initial_valid (rows : Array Row) (masks : Array (Array Nat))
    (h : invariantCheck rows masks = true) (hne : 0 < rows.size) : Valid rows masks (system rows).initial := by
  obtain ⟨hsize,hzero,_⟩ := invariant_parts rows masks h
  have hm : 0 < masks.size := by omega
  let mask := masks[0]
  have hmask : masks[0]? = some mask := by simp [mask]
  refine ⟨hne,mask,hmask,?_⟩
  intro i hi
  have hz := List.all_eq_true.mp hzero i (List.mem_range.mpr hi)
  simpa [hmask,system] using hz

theorem invariantRow_sound (rows : Array Row) (masks : Array (Array Nat))
    (i : Nat) (row : Row) (before : Array Nat)
    (hr : rows[i]? = some row) (hm : masks[i]? = some before)
    (h : invariantRow rows masks i = true) :
    ∃ no yes, masks[row.no]? = some no ∧ masks[row.yes]? = some yes ∧
      transfer row before no yes = true := by
  simp only [invariantRow,hr,hm] at h
  cases hn : masks[row.no]? with
  | none => simp [hn] at h
  | some no =>
    cases hy : masks[row.yes]? with
    | none => simp [hn,hy] at h
    | some yes => exact ⟨no,yes,rfl,rfl,by simpa [hn,hy] using h⟩

theorem step_preserves (rows : Array Row) (masks : Array (Array Nat))
    (hcheck : invariantCheck rows masks = true) (s : State) (hvalid : Valid rows masks s) :
    Valid rows masks (step rows s).1 := by
  obtain ⟨hindex,before,hbefore,hbank⟩ := hvalid
  obtain ⟨hsize,_,hrows⟩ := invariant_parts rows masks hcheck
  obtain ⟨row,hrow⟩ : ∃ row, rows[s.index]? = some row := ⟨rows[s.index],by simp⟩
  have hc := List.all_eq_true.mp hrows s.index (List.mem_range.mpr hindex)
  obtain ⟨no,yes,hno,hyes,htransfer⟩ := invariantRow_sound rows masks s.index row before hrow hbefore hc
  let nextIndex := if observe row.action s.bank then row.yes else row.no
  let nextMask := if observe row.action s.bank then yes else no
  have hm : masks[nextIndex]? = some nextMask := by
    dsimp [nextIndex,nextMask]
    cases observe row.action s.bank <;> simp_all
  have hn : nextIndex < rows.size := by
    obtain ⟨hm',_⟩ := Array.getElem?_eq_some_iff.mp hm
    omega
  have hb := transfer_sound row before no yes s.bank htransfer hbank
  have hs : step rows s = (⟨nextIndex,update row.action s.bank⟩,decide (row.action = .beep)) := by
    simp [step,hrow,nextIndex]
  rw [hs]
  change Valid rows masks ⟨nextIndex,update row.action s.bank⟩
  exact ⟨hn,nextMask,hm,hb⟩

theorem run_valid (rows : Array Row) (masks : Array (Array Nat))
    (hcheck : invariantCheck rows masks = true) (hne : 0 < rows.size) (n : Nat) :
    Valid rows masks ((system rows).run n) := by
  induction n with
  | zero => exact initial_valid rows masks hcheck hne
  | succ n ih =>
    have hs := step_preserves rows masks hcheck ((system rows).run n) ih
    simpa only [EventSystem.run_succ,system] using hs

/-- An accepted peer-zero check implies actual zero in every other logical
register of the same physical class, for arbitrary natural-valued banks. -/
theorem peerZero_sound (classes mask : Array Nat) (i : Nat) (bank : Nat → Nat)
    (hcheck : peerZero classes mask i = true) (hbank : validBank mask bank)
    (j : Nat) (hj : j < 18) (hne : j ≠ i) (hclass : classAt classes j = classAt classes i) :
    bank j = 0 := by
  have hs := List.all_eq_true.mp hcheck j (List.mem_range.mpr hj)
  have hm : slot mask j = 1 := by simpa [hne,hclass] using hs
  have hv := hbank j hj
  rw [hm] at hv
  exact admits_only_zero _ hv

end Shared.PNP.Record285.OwnershipCore
