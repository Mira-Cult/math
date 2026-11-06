import Shared.Beeping.NPcoNP.Grammar284BreakOneShape
import Shared.Beeping.NPcoNP.NativeState95Corridor
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
import Shared.Beeping.NPcoNP.NativeCarryPivot

/-! A `_break.1` leaf follows its first expanded successor under explicit
control-window assumptions. Later jumps and window reachability are separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284BreakOne
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeCarryExactControl
open Shared.Beeping.NPcoNP.NativeCarryPivot
open Shared.Beeping.NPcoNP.NativeState95Corridor
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284BreakOneShape
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

theorem break_one_to_first_successor (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (name : entry.2="_break.1")
    (origin separator : Int) (t : Int → Bool)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+55<separator) (right : t (separator-1)=true) (sep : t separator=false) :
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts entry.1 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ Holds out origin next ∧ (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨i,j,dst,next,nextName,_,_,hsucc,hnext,ilo,hij,jhi,hbit,hmid,hsuffix,hfinal,hshape⟩ :=
    break_one_shape_sound entry member name
  have walk := expanded_leaf_follows traceState557.acc producerExpand entry member
  have ⟨elen,ecount⟩ := prepared_path_bound entry.1 (.op entry.2) walk
  have nlist : traceState557.acc.leaves.toList[dst]?=some (next,nextName) := by
    simpa only [Array.getElem?_toList] using hnext
  obtain ⟨nbound,nhget⟩ := List.getElem?_eq_some_iff.mp nlist
  have nmem : (next,nextName) ∈ traceState557.acc.leaves.toList := by
    rw [←nhget]
    exact List.getElem_mem nbound
  have nwalk : PreparedWalk next (.op nextName) :=
    expanded_leaf_follows traceState557.acc producerExpand (next,nextName) nmem
  have nlen : next.length≤55 := (prepared_path_bound next (.op nextName) nwalk).1
  obtain ⟨first,tail⟩ := prepared_head_tail t origin entry.1 entry.2 walk word
  let last := origin+((entry.1.length : Nat) : Int)-1
  let middle := origin+(j : Int)
  let base := clearAt last t
  let cleared := clearRange base (middle+1) last
  have targetEntry : administrativeEntry entry.2=some 95 := by rw [name]; rfl
  have dispatch := expanded_administrative_dispatch traceState557.acc producerExpand entry member 95 targetEntry (origin+1) t tail
  obtain ⟨_,_,hlast,_⟩ := administrative_path_checked entry member 95 targetEntry
  have htailLen : entry.1.tail.dropLast.length+1=entry.1.tail.length := by
    have he : entry.1.tail.dropLast ++ [true]=entry.1.tail :=
      List.dropLast_append_getLast? true (by simp [hlast])
    have hh := congrArg List.length he
    simpa using hh
  have hpathLen : entry.1.tail.length+1=entry.1.length := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hlastPos : origin+1+((entry.1.tail.dropLast.length : Nat) : Int)=last := by dsimp [last]; omega
  have hdispatch : silentSegment machine (cfg 93 (origin+1) t) (cfg 95 (last-1) base)
      (entry.1.tail.dropLast.length+1) := by
    rw [hlastPos] at dispatch
    have he : (cfg (93 : Fin 284) last t).write false=base := rfl
    rw [he] at dispatch
    exact dispatch
  have jbound : j<entry.1.length := by omega
  have midbit : entry.1[j]=false := by
    rw [List.getElem?_eq_getElem jbound] at hmid
    exact Option.some.inj hmid
  have midzero : base middle=false := by
    have ht : t middle=false := by dsimp [middle]; rw [holds_get t origin entry.1 word j jbound,midbit]
    simpa [base,clearAt,show middle≠last by dsimp [middle,last]; omega] using ht
  have runones : ∀ q, middle<q → q≤last-1 → base q=true := by
    intro q hq hq'
    let k := (q-origin).toNat
    have hk : (k : Int)=q-origin := Int.toNat_of_nonneg (by dsimp [middle] at hq; omega)
    have hklo : j<k := by dsimp [middle] at hq; omega
    have hkhi : k<entry.1.length-1 := by dsimp [last] at hq'; omega
    have hkbound : k<entry.1.length := by omega
    have hv := hfinal k hklo hkhi
    rw [List.getElem?_eq_getElem hkbound] at hv
    have hv' : entry.1[k]=true := Option.some.inj hv
    have he : origin+(k : Int)=q := by omega
    have ht : t q=true := by simpa only [he,hv'] using holds_get t origin entry.1 word k hkbound
    simpa [base,clearAt,show q≠last by omega] using ht
  obtain ⟨a,ha,hscan⟩ := scan95_corridor (last-1) middle base (by dsimp [last,middle]; omega) midzero runones
  have hscan' : silentSegment machine (cfg 95 (last-1) base) (cfg 1 (middle-1) cleared) a := by
    simpa [cleared] using hscan
  have hbefore : ∀ q, q≤middle → cleared q=t q := by
    intro q hq
    dsimp only [cleared,clearRange]
    rw [if_neg (show ¬ (middle+1≤q ∧ q<last) by omega)]
    simp [base,clearAt,show q≠last by dsimp [last,middle] at *; omega]
  let xs := entry.1.take j
  have hxslen : xs.length=j := by simp [xs,List.length_take_of_le (by omega : j≤entry.1.length)]
  have hxscount : xs.count false≤11 := by
    have hc := congrArg (List.count false) (List.take_append_drop j entry.1)
    simp only [List.count_append] at hc
    dsimp [xs]
    omega
  have hxsword : Holds cleared origin xs := by
    have hw : Holds t origin xs := by
      apply holds_prefix t origin (entry.1.take j) (entry.1.drop j)
      simpa only [List.take_append_drop] using word
    apply holds_transport t cleared origin xs hw
    intro q hq hq'
    exact (hbefore q (by rw [hxslen] at hq'; dsimp [middle]; omega)).symm
  have hleft : ∀ q, q<origin → cleared q=false := by
    intro q hq
    rw [hbefore q (by dsimp [middle]; omega)]
    exact left q hq
  have hfirst : cleared origin=true := by
    rw [hbefore origin (by dsimp [middle]; omega)]
    exact first
  have hanchor : cleared (origin+2)=false := by
    rw [hbefore (origin+2) (by dsimp [middle]; omega)]
    obtain ⟨raw,he,_⟩ := walk
    have hw := word
    rw [he] at hw
    simp only [preparedPrefix,List.cons_append,Holds] at hw
    have hh : origin+1+1=origin+2 := by omega
    simpa only [hh] using hw.2.2.1
  have hright : cleared (separator-1)=true := by
    rw [show cleared (separator-1)=t (separator-1) by
      dsimp only [cleared,clearRange]
      rw [if_neg (show ¬ (middle+1≤separator-1 ∧ separator-1<last) by dsimp [last]; omega)]
      simp [base,clearAt,show separator-1≠last by dsimp [last]; omega]]
    exact right
  have hsep : cleared separator=false := by
    rw [show cleared separator=t separator by
      dsimp only [cleared,clearRange]
      rw [if_neg (show ¬ (middle+1≤separator ∧ separator<last) by dsimp [last]; omega)]
      simp [base,clearAt,show separator≠last by dsimp [last]; omega]]
    exact sep
  have hbetween : ∀ q, middle-1<q → q<separator-1 → cleared q=false := by
    intro q hq hq'
    by_cases hm : q=middle
    · subst q
      rw [hbefore middle (le_refl _)]
      dsimp [middle]
      rw [holds_get t origin entry.1 word j jbound,midbit]
    by_cases hc : q<last
    · simp [cleared,clearRange,show middle+1≤q by omega,hc]
    by_cases he : q=last
    · simp [cleared,clearRange,base,clearAt,he]
    · have ht := gap q (by dsimp [last] at *; omega) hq'
      dsimp only [cleared,clearRange]
      rw [if_neg (show ¬ (middle+1≤q ∧ q<last) by omega)]
      simpa [base,clearAt,he] using ht
  have hbank : ∀ q, separator≤q → cleared q=t q := by
    intro q hq
    dsimp only [cleared,clearRange]
    rw [if_neg (show ¬ (middle+1≤q ∧ q<last) by dsimp [last]; omega)]
    simp [base,clearAt,show q≠last by dsimp [last]; omega]
  obtain ⟨b,out,mark,hb,hmarklo,hmarkhi,hmarkzero,hmarkones,hnewmark,hframe,houtgap,houtmark,houtbank,hcarry⟩ :=
    carry_to_origin_single_marker (middle-1) origin separator cleared xs
      (by simp [hxslen,middle]) (by dsimp [middle]; omega) hanchor hxscount hxsword hfirst hleft
      (by dsimp [middle,last]; omega) hright hbetween hsep
  have markEq : mark=origin+(i : Int) := by
    apply carry_pivot_eq t origin (middle-1) mark entry.1 j i (by omega) (by simp [middle]) word hij hbit hsuffix
      (by omega) hmarkhi
    · rw [←hbefore mark (by omega)]
      exact hmarkzero
    · intro q hq hq'
      rw [←hbefore q (by omega)]
      exact hmarkones q hq hq'
  let zeros := next.length-(entry.1.take i ++ [true]).length
  have hlength : next.length=i+1+zeros := by
    have hh := congrArg List.length hshape
    simpa [zeros,List.length_take_of_le (by omega : i ≤ entry.1.length),
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have houtword := control_word_of_frame cleared out origin mark separator xs zeros (by omega)
    (by rw [markEq,hxslen]; omega) hxsword hframe hnewmark houtgap (by rw [markEq]; omega)
  have htake : xs.take (mark-origin).toNat=entry.1.take i := by
    rw [markEq]
    simp [xs,List.take_take,show min i j=i by omega]
  rw [htake] at houtword
  have hnextword : Holds out origin next := by
    rw [hshape]
    simpa only [zeros,List.append_assoc,List.singleton_append] using houtword
  have houtleft : ∀ q, q<origin → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact hleft q hq
  have houtgap' : ∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false := by
    intro q hq hq'
    exact houtgap q (by rw [markEq]; omega) hq'
  have houtsep : out separator=false := by rw [houtbank separator (le_refl _),hsep]
  have houtbank' : ∀ q, separator≤q → out q=t q := by
    intro q hq
    exact (houtbank q hq).trans (hbank q hq)
  have hchain := segAdd machine _ _ _ _ a hdispatch hscan'
  exact ⟨dst,next,nextName,entry.1.tail.dropLast.length+1+a+b,out,hsucc,hnext,by omega,
    hnextword,houtleft,houtgap',houtmark,houtsep,houtbank',segAdd machine _ _ _ _ b hchain hcarry⟩

#print axioms break_one_to_first_successor
end Shared.Beeping.NPcoNP.Grammar284BreakOne
