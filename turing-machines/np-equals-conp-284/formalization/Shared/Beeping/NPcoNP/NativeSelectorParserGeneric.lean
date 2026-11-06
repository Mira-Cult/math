import Shared.Beeping.NPcoNP.NativeHalfSelectorExact
import Shared.Beeping.NPcoNP.NativeFirstDispatch
import Shared.Beeping.NPcoNP.Grammar284ForwardParser

/-! Conditional connection between the literal selector and the prepared-path
parser. This is a finite segment theorem, not a reachability or recurrent
simulation result. -/
namespace Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false

/-- Every block has at least one delimiter, so the selector segment always
contains a positive number of physical steps. -/
theorem blocks_length_lower_bound (ks : List Nat) : ks.length ≤ (blocks ks).length := by
  induction ks with
  | nil => simp [blocks]
  | cons k ks ih => simp [blocks, List.length_append]; omega

/-- If the fourteen physical blocks end at or left of the first one of a
prepared path, the selector reaches state 93 immediately after that one. The
whole tape is unchanged, and the abstract parser identifies the entire path.
The hypothesis supplies the window; the theorem does not claim it is reachable. -/
theorem selector_to_parser (t : Int → Bool) (head origin : Int) (ks : List Nat)
    (path : List Bool) (name : String)
    (hlen : ks.length=14)
    (window : downHolds t head (blocks ks ++ []))
    (horder : head-((blocks ks).length : Int) ≤ origin)
    (left : ∀ q, q<origin → t q=false)
    (first : t origin=true)
    (walk : PreparedWalk path (.op name)) (word : Holds t origin path) :
    let d := (origin-(head-((blocks ks).length : Int))).toNat
    0 < (blocks ks).length+d+1 ∧
    silentSegment machine (cfg 83 head t) (cfg 93 (origin+1) t)
      ((blocks ks).length+d+1) ∧
    parseForward 52 t origin=some (name,path.length) := by
  dsimp only
  let start := head-((blocks ks).length : Int)
  let d := (origin-start).toNat
  have hd : (d : Int)=origin-start := by
    dsimp [d,start]
    exact Int.toNat_of_nonneg (by omega)
  have hz : ∀ i : Nat, i<d → t (start+(i : Int))=false := by
    intro i hi
    apply left
    omega
  have ho : t (start+(d : Int))=true := by
    have he : start+(d : Int)=origin := by omega
    simpa only [he] using first
  have hs := (chain_blocks chain83 ks head t [] hlen window).2
  have hr := scan92_exact d start t hz ho
  have hall := segAdd machine _ _ _ (blocks ks).length (d+1) hs hr
  have he : start+(d : Int)+1=origin+1 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [start, he, Nat.add_assoc] using hall
  · exact (parseForward_iff t origin name path.length).2 ⟨path,walk,rfl,word⟩

#print axioms blocks_length_lower_bound
#print axioms selector_to_parser
end Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
