import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Unit-selector dispatch through a finite scan and exact unary increment.
All words and their lengths are supplied; no global layout is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeUnit261Increment
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- A unit dispatch clears its marker, crosses a supplied one-run and
increments the first supplied unary bank value. The result and the full tape
frame include the initial control write and have an exact silent duration. -/
theorem dispatch_increment (r v : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false])) :
    let base := h+2+(r : Int)+1
    let last := base+(((v+1)+(encode rest).length : Nat):Int)
    ∃ e : Config 284, e.state=23 ∧ e.head=last ∧
      Holds e.tape base (encode ((v+1)::rest)) ∧ e.tape h=false ∧
      (∀ p, p≠h → (p<base ∨ last<p) → e.tape p=t p) ∧
      silentSegment machine (cfg 261 h t) e (r+v+6+(encode rest).length) := by
  dsimp only
  let base := h+2+(r : Int)+1
  let last := base+(((v+1)+(encode rest).length : Nat):Int)
  let cleared := clearAt h t
  have hz : cleared (h+1)=false := by simp [cleared,clearAt,hzero]
  have hs : Holds cleared (h+2) (List.replicate r true ++ [false]) := by
    apply holds_clear_left t h (h+2) _ (by omega) scanword
  have hb : Holds cleared base (encode (v::rest) ++ [false]) := by
    apply holds_clear_left t h base _ (by dsimp [base]; omega) bank
  have h261 := oneSeg machine _ _ (step261_one h t hone)
  have h16 := oneSeg machine _ _ (step16_zero (h+1) cleared hz)
  have h16' : silentSegment machine (cfg 16 (h+1) cleared) (cfg 12 (h+2) cleared) 1 := by
    have hp : h+1+1=h+2 := by omega
    simpa only [hp] using h16
  have h12 := scan12 r (h+2) cleared hs
  have hpre := segAdd machine _ _ _ (1+1) (r+1)
    (segAdd machine _ _ _ 1 1 h261 h16') h12
  have he : h+2+(r : Int)+1=base := rfl
  rw [he] at hpre
  obtain ⟨e,hstate,hhead,hbank,hframe,hinc⟩ := encoded_increment v rest base cleared hb
  have htotal := segAdd machine _ _ _ (1+1+(r+1)) (v+3+(encode rest).length) hpre hinc
  refine ⟨e,hstate,hhead,hbank,?_,?_,?_⟩
  · rw [hframe h (Or.inl (by dsimp [base]; omega))]
    simp [cleared,clearAt]
  · intro p hne hp
    rw [hframe p hp]
    simp [cleared,clearAt,hne]
  · have hcost : (1+1+(r+1))+(v+3+(encode rest).length)=r+v+6+(encode rest).length := by omega
    rw [hcost] at htotal
    exact htotal

#print axioms dispatch_increment
end Shared.Beeping.NPcoNP.NativeUnit261Increment
