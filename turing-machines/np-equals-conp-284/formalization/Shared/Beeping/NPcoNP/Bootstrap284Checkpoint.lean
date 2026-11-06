import Shared.Beeping.NPcoNP.Bootstrap284FastReplay

/-! Exact finite-window checkpoint comparisons. A finite equality test alone
is not enough: both tapes must also be known blank outside the window. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Checkpoint
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284FastReplay

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The tape is blank outside the half-open window `[lo,lo+width)`. -/
def InWindow (lo : Int) (width : Nat) (t : Int → Bool) : Prop :=
  ∀ p : Int, (p<lo ∨ lo+(width : Int)≤p) → t p=false

/-- Compare exactly the cells in the proposed finite window. -/
def agree (lo : Int) (width : Nat) (a b : Int → Bool) : Bool :=
  (List.range width).all fun i => a (lo+(i : Int)) == b (lo+(i : Int))

/-- The two outside-blank proofs are essential: finite agreement alone
cannot establish equality of arbitrary unbounded tapes. -/
theorem tapes_eq (lo : Int) (width : Nat) (a b : Int → Bool)
    (ha : InWindow lo width a) (hb : InWindow lo width b)
    (hc : agree lo width a b=true) : a=b := by
  funext p
  by_cases hp : p<lo ∨ lo+(width : Int)≤p
  · rw [ha p hp,hb p hp]
  · let i : Nat := (p-lo).toNat
    have hi : (i : Int)=p-lo := Int.toNat_of_nonneg (by omega)
    have hil : i<width := by omega
    have hh := (List.all_eq_true.mp hc) i (List.mem_range.mpr hil)
    have he : lo+(i : Int)=p := by omega
    rw [he] at hh
    simpa only [beq_iff_eq] using hh

/-- A checkpoint compares state, head and every cell in a finite window. -/
def sameWindow (lo : Int) (width : Nat) (a b : Config 284) : Bool :=
  (a.state == b.state) && (a.head == b.head) && agree lo width a.tape b.tape

theorem configs_eq (lo : Int) (width : Nat) (a b : Config 284)
    (ha : InWindow lo width a.tape) (hb : InWindow lo width b.tape)
    (hc : sameWindow lo width a b=true) : a=b := by
  simp only [sameWindow,Bool.and_eq_true,beq_iff_eq] at hc
  obtain ⟨⟨hs,hh⟩,ht⟩ := hc
  have he := tapes_eq lo width a.tape b.tape ha hb ht
  cases a
  cases b
  simp_all

/-- A checked replacement can be used between independently replayed
certificate blocks without changing the physical run or event word. -/
theorem compose_checkpoint (lo : Int) (width : Nat)
    (a mid checkpoint e : Config 284) (n m : Nat)
    (hfirst : silentSegment machine a mid n)
    (hmid : InWindow lo width mid.tape)
    (hcheckpoint : InWindow lo width checkpoint.tape)
    (hmatch : sameWindow lo width mid checkpoint=true)
    (hsecond : silentSegment machine checkpoint e m) :
    silentSegment machine a e (n+m) := by
  have he := configs_eq lo width mid checkpoint hmid hcheckpoint hmatch
  subst checkpoint
  exact segAdd machine _ _ _ n m hfirst hsecond

end Shared.Beeping.NPcoNP.Bootstrap284Checkpoint
