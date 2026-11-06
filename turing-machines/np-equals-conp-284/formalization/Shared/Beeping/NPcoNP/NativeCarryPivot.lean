import Shared.Beeping.NPcoNP.NativeCarryExactControl
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Identify a physical carry marker with a supplied rightmost zero of a
finite control word. Grammar successor and reachability remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeCarryPivot
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeCarryExactControl
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The physical rightmost-zero marker equals the unique supplied rightmost
zero in the tape word below the carry cutoff. -/
theorem carry_pivot_eq (t : Int → Bool) (origin h mark : Int) (path : List Bool)
    (cutoff i : Nat) (hcut : cutoff≤path.length)
    (hpos : h=origin+(cutoff : Int)-1) (word : Holds t origin path)
    (ilo : i<cutoff) (ibit : path[i]?=some false)
    (suffix : ∀ j, i<j → j<cutoff → path[j]?=some true)
    (mlo : origin≤mark) (mhi : mark≤h) (mzero : t mark=false)
    (mones : ∀ q, mark<q → q≤h → t q=true) :
    mark=origin+(i : Int) := by
  have ibound : i<path.length := by omega
  have hip : path[i]=false := by
    have hh := ibit
    rw [List.getElem?_eq_getElem ibound] at hh
    exact Option.some.inj hh
  have hpivot : t (origin+(i : Int))=false := by
    rw [holds_get t origin path word i ibound,hip]
  have hmarkIndex : 0≤mark-origin := by omega
  let j := (mark-origin).toNat
  have hj : (j : Int)=mark-origin := Int.toNat_of_nonneg hmarkIndex
  have hjcut : j<cutoff := by omega
  have hjbound : j<path.length := by omega
  have hmarkAt : t mark=path[j] := by
    have he : origin+(j : Int)=mark := by omega
    simpa only [he] using holds_get t origin path word j hjbound
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have ht := mones (origin+(i : Int)) hlt (by omega)
    rw [hpivot] at ht
    contradiction
  · have hij : i<j := by omega
    have ht := suffix j hij hjcut
    rw [List.getElem?_eq_getElem hjbound] at ht
    have hjtrue : path[j]=true := Option.some.inj ht
    rw [mzero,hjtrue] at hmarkAt
    contradiction

/-- If a candidate successor is the carried prefix followed by zeros, and its
selected bit is the rightmost zero below the carry cutoff, the literal carry
and selector produce that candidate word at the original parser origin. -/
theorem carry_produces_candidate_exact (t : Int → Bool) (origin h p separator : Int)
    (path next : List Bool) (skip i zeros : Nat) (hskip : skip≤path.length)
    (hpos : h=origin+((path.length-skip : Nat) : Int)-1)
    (ilo : 2 ≤ i) (ihi : i<path.length-skip) (ibit : path[i]?=some false)
    (suffix : ∀ j, i<j → j<path.length-skip → path[j]?=some true)
    (shape : next=(path.take i ++ [true]) ++ List.replicate zeros false)
    (room : origin+((next.length : Nat) : Int)<separator)
    (count : path.count false≤11) (word : Holds t origin path)
    (first : t origin=true) (anchor : t (origin+2)=false)
    (left : ∀ q, q<origin → t q=false) (hp : h<p) (hone : t p=true)
    (between : ∀ q, h<q → q<p → t q=false) (hsep : p+1<separator)
    (ones : ∀ q, p<q → q<separator → t q=true) (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧ Holds out origin next ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  let cutoff := path.length-skip
  let xs := path.take cutoff
  have hcut : cutoff≤path.length := by dsimp [cutoff]; omega
  have hlen : xs.length=cutoff := by simp [xs,List.length_take_of_le hcut]
  have hcount : xs.count false≤11 := by
    have hc := congrArg (List.count false) (List.take_append_drop cutoff path)
    simp only [List.count_append] at hc
    dsimp [xs]
    omega
  have hword : Holds t origin xs := by
    apply holds_prefix t origin (path.take cutoff) (path.drop cutoff)
    simpa only [List.take_append_drop] using word
  have hhead : h=origin+((xs.length : Nat) : Int)-1 := by simpa only [hlen,cutoff] using hpos
  have hanchor : origin+2≤h := by dsimp [cutoff] at hcut; omega
  obtain ⟨steps,out,mark,hs,hlo,hhi,hzero,hones,hmarkone,hframe,hgap,hright,hbank,hseg⟩ :=
    carry_to_origin_exact_control h p origin separator t xs hhead hanchor anchor hcount hword first left
      hp hone between hsep ones blank
  have hmark : mark=origin+(i : Int) :=
    carry_pivot_eq t origin h mark path cutoff i hcut (by simpa only [cutoff] using hpos) word
      (by simpa only [cutoff] using ihi) ibit (by simpa only [cutoff] using suffix)
      (by omega) hhi hzero hones
  have hj : (mark-origin).toNat=i := by rw [hmark]; simp
  have htake : xs.take (mark-origin).toNat=path.take i := by
    rw [hj]
    simp only [xs,List.take_take]
    congr 1
    omega
  have htakeLen : (path.take i).length=i := List.length_take_of_le (by omega)
  have hnextLen : next.length=i+1+zeros := by
    rw [shape]
    simp [htakeLen,Nat.add_comm,Nat.add_left_comm]
  have hroom : mark+(zeros : Int)<separator-1 := by rw [hmark] ; omega
  have hnewword := control_word_of_frame t out origin mark separator xs zeros (by omega)
    (by rw [hlen]; omega) hword hframe hmarkone hgap hroom
  rw [htake] at hnewword
  have hresult : Holds out origin next := by
    rw [shape]
    simpa [List.append_assoc] using hnewword
  have houtleft : ∀ q, q<origin → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have houtgap : ∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false := by
    intro q hq hq'
    exact hgap q (by rw [hmark]; omega) hq'
  have houtsep : out separator=false := (hbank separator (le_refl _)).trans blank
  exact ⟨steps,out,hs,hresult,houtleft,houtgap,houtsep,hright,hbank,hseg⟩

/-- Original candidate interface. -/
theorem carry_produces_candidate (t : Int → Bool) (origin h p separator : Int)
    (path next : List Bool) (skip i zeros : Nat) (hskip : skip≤path.length)
    (hpos : h=origin+((path.length-skip : Nat) : Int)-1)
    (ilo : 2 ≤ i) (ihi : i<path.length-skip) (ibit : path[i]?=some false)
    (suffix : ∀ j, i<j → j<path.length-skip → path[j]?=some true)
    (shape : next=(path.take i ++ [true]) ++ List.replicate zeros false)
    (room : origin+((next.length : Nat) : Int)<separator)
    (count : path.count false≤11) (word : Holds t origin path)
    (first : t origin=true) (anchor : t (origin+2)=false)
    (left : ∀ q, q<origin → t q=false) (hp : h<p) (hone : t p=true)
    (between : ∀ q, h<q → q<p → t q=false) (hsep : p+1<separator)
    (ones : ∀ q, p<q → q<separator → t q=true) (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧ Holds out origin next ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨steps,out,hs,hw,_,_,_,hr,hbank,hseg⟩ := carry_produces_candidate_exact t origin h p separator path next skip i zeros hskip hpos ilo ihi ibit suffix shape room count word first anchor left hp hone between hsep ones blank
  exact ⟨steps,out,hs,hw,hr,hbank,hseg⟩

#print axioms carry_pivot_eq
#print axioms carry_produces_candidate_exact
#print axioms carry_produces_candidate
end Shared.Beeping.NPcoNP.NativeCarryPivot
