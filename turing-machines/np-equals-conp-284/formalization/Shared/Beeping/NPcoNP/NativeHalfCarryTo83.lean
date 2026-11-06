import Shared.Beeping.NPcoNP.NativeHalfBankCarry
import Shared.Beeping.NPcoNP.NativeHalfProtectedMarker

/-! The exceptional prepared HALF path carries a concrete protected marker
through state 28 and the state-97 scan. The prepared boundary is supplied;
no blank-start reachability or complete HALF semantics is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCarryTo83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfBankCarry
open Shared.Beeping.NPcoNP.NativeHalfProtectedMarker

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The cleanup output has an all-zero right tail regardless of its
arbitrary protected prefix. -/
theorem postTape_right_zero (base : Int → Bool) (b q : Int) (values : List Nat)
    (hq : b+3+((false :: UnaryBank.encode values).length : Int) < q) :
    postTape base b values q = false := by
  unfold postTape
  rw [spec_outside _ _ _ _ (Or.inr hq)]
  apply after_tail_zero
  omega

/-- The actual carry writes one at the first zero to the left; subsequent
state-27 dispatch cannot touch that marker. -/
theorem carry_marker (t : Int → Bool) (gap : Int) (k : Nat) :
    put (result t (gap-1) k) (gap+2) false (gap-1-(k : Int)) = true := by
  have hne : gap-1-(k : Int) ≠ gap+2 := by omega
  rw [put_other _ _ _ _ hne]
  simp [result,put]

/-- The same carry/dispatch preserves every cell strictly to the right of
its marked boundary. -/
theorem carry_preserves_right (t : Int → Bool) (gap q : Int) (k : Nat)
    (hq : gap+2 < q) :
    put (result t (gap-1) k) (gap+2) false q = t q := by
  have hne : q ≠ gap+2 := by omega
  have hne' : q ≠ gap-1-(k : Int) := by omega
  have hout : ¬ (gap-1-(k : Int) < q ∧ q ≤ gap-1) := by omega
  simp [put,result,cleared,hne,hne',hout] <;> omega

/-- A prepared exceptional state-30 boundary reaches state 83 in positive
finite silent time. The marker produced by the carry is explicitly retained;
the only local pattern hypothesis is the finite left carry. -/
theorem exceptional_through_83 (back : Int → Bool) (gap : Int)
    (left values : List Nat) (k : Nat)
    (hm : downHolds back (gap-1) (List.replicate k true ++ [false])) :
    let suffix := leftSuffix left
    let base := before back gap suffix
    let b := gap+1+(suffix.length : Int)
    let p := gap-1-(k : Int)
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state=83 ∧ e.tape p=true ∧ e.tape (e.head+1)=true ∧
      (∀ q, q < p → e.tape q = back q) ∧ silentSegment machine (cfg 30 b (prior base b (false :: UnaryBank.encode values))) e n := by
  dsimp only
  let suffix := leftSuffix left
  let base := before back gap suffix
  let b := gap+1+(suffix.length : Int)
  let t := preparedTape back gap left values
  let p := gap-1-(k : Int)
  let t' := put (result t (gap-1) k) (gap+2) false
  have hbase : 0 < (suffix.length : Int) := by exact_mod_cast suffix_length_pos left
  let q := b+4+((false :: UnaryBank.encode values).length : Int)
  have hq : gap+3 ≤ q := by dsimp [q,b]; omega
  have htq : t q=false := by
    change postTape base b values q=false
    apply postTape_right_zero
    dsimp [q]
    omega
  have hqt : t' q=false := by
    rw [show t' q=t q from carry_preserves_right t gap q k (by dsimp [q,b]; omega)]
    exact htq
  let d := (q-(gap+3)).toNat
  have hd : gap+3+(d : Int)=q := by
    have hd' : (d : Int)=q-(gap+3) := Int.toNat_of_nonneg (by omega)
    omega
  have hzero : t' (gap+3+(d : Int))=false := by rw [hd]; exact hqt
  have hp : p ≤ (gap+3)-2 := by dsimp [p]; omega
  have hmarker : t' p=true := carry_marker t gap k
  have hleft : t' ((gap+3)-1)=false := by
    have he : gap+3-1=gap+2 := by omega
    rw [he]
    simp [t',put]
  obtain ⟨n,e,hn,hstate,hprotected,hfound,hprefix,hseg⟩ :=
    state28_to_83 (gap+3) p t' hp hmarker hleft d hzero
  obtain ⟨m,hmpos,hcarry⟩ := exceptional_through_carry back gap left values k hm
  have htail : ∀ q, q < p → e.tape q = back q := by
    intro q hq
    rw [hprefix q (by dsimp [p] at hq; omega)]
    have ht : t' q=t q := by
      dsimp [t']
      have hne : q ≠ gap+2 := by dsimp [p] at hq; omega
      have hne' : q ≠ gap-1-(k : Int) := by dsimp [p] at hq; omega
      have hnot : ¬ (gap-1-(k : Int) < q ∧ q ≤ gap-1) := by dsimp [p] at hq; omega
      simp [put,result,cleared,hne,hne',hnot] <;> omega
    rw [ht]
    exact prepared_prefix back gap q left values (by dsimp [p] at hq; omega)
  refine ⟨m+n,e,by omega,hstate,hprotected,hfound,htail,?_⟩
  exact segAdd machine _ _ _ m n hcarry hseg

end Shared.Beeping.NPcoNP.NativeHalfCarryTo83
