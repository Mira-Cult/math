import Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRoundtrip
import Shared.Beeping.NPcoNP.NativeShortPositiveWindow
import Shared.Beeping.NPcoNP.NativeVariableMarkerReturn

/-! The shortened positive selector's return on the actual blank-start run. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeShortPositiveWindow
open Shared.Beeping.NPcoNP.NativeVariableMarkerReturn
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRoundtrip
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

/-- The actual shortened positive scan returns to state 93 in 3,829
further silent steps, with the next selector and bank explicitly supplied. -/
theorem blank_start_short_positive_return_with_left_ray :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [3,3795])) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧ (∀ q, q≤ -3823 → out q=false) ∧
      Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hw,h2,h3,h4,hray,hbank,hseg⟩ :=
    blank_start_variable_positive_roundtrip
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hw,h2,h3,h4,hray,hbank,by simpa [Nat.add_assoc] using hseg⟩

/-- Retain the earlier reachable positive-return interface. -/
theorem blank_start_short_positive_return :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [3,3795])) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧
      Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hw,h2,h3,h4,_hray,hbank,hseg⟩ :=
    blank_start_short_positive_return_with_left_ray
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hw,h2,h3,h4,hbank,hseg⟩

#print axioms blank_start_short_positive_return
end Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveReturn
