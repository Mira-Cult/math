import PASoundness.PAtoCompactPAAddSuccSharedDiamondPack
import PASoundness.PAtoCompactPAAddSuccFrameConditional

/-! The guarded PA addition-successor axiom follows from explicit finite K
proof data constructing its arithmetic diamond. No diamond existence or
semantic soundness is asserted here. -/
namespace PASoundness.PAtoCompactPAAddSuccDiamondBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactPAAddSuccSharedDiamondPack
open PASoundness.PAtoCompactPAAddSuccFrameConditional
open PASoundness.PAtoCompactVacuousEqualityAlignment

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The finite K formula requiring the exact shared arithmetic witnesses. -/
def requiredDiamond (t u : Peano.Term) : Nat :=
  let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
  let q := guardBase A
  existsCode (q+1) (existsCode (q+2) (existsCode (q+3) (existsCode (q+4)
    (existsCode q (diamond t u (q+100) (q+1) (q+2) (q+3) (q+4) q)))))

/-- A supplied K proof of the guarded diamond constructs the actual guarded
PA axiom, with one shared output and no graph-functionality assumption. -/
noncomputable def add_succ_of_diamond (t u : Peano.Term)
    (h : let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
      KDerivation (imp (guardFormula A).encode (requiredDiamond t u))) :
    KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u)))) := by
  let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
  let q := guardBase A
  have ht : ∀ a ∈ t.varFinset, a < q := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp [A, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
    have hbound := Finset.le_sup (f := id) hfree
    simp only [id_eq] at hbound
    dsimp [q, guardBase]
    omega
  have hu : ∀ a ∈ u.varFinset, a < q := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp [A, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
    have hbound := Finset.le_sup (f := id) hfree
    simp only [id_eq] at hbound
    dsimp [q, guardBase]
    omega
  have hpack := shared_from_diamond t u q ht hu
  apply add_succ_of_shared t u
  change KDerivation (imp (guardFormula A).encode
    (existsCode q (andF (termGraph id (Peano.add t (Peano.succ u)) q (q+2))
      (termGraph id (Peano.succ (Peano.add t u)) q
        (q+2+termCost (Peano.add t (Peano.succ u))))).encode))
  have hd : KDerivation (imp (guardFormula A).encode
      (existsCode (q+1) (existsCode (q+2) (existsCode (q+3) (existsCode (q+4)
        (existsCode q (diamond t u (q+100) (q+1) (q+2) (q+3) (q+4) q))))))) := by
    simpa only [requiredDiamond, A, q] using h
  exact compose hd hpack

theorem add_succ_of_diamond_certificate (t u : Peano.Term)
    (h : let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
      KDerivation (imp (guardFormula A).encode (requiredDiamond t u))) :
    theoremCode (certificate (add_succ_of_diamond t u h)) =
      guardedCode ((Peano.add t (Peano.succ u)).equal
        (Peano.succ (Peano.add t u))) := certificate_correct _

end PASoundness.PAtoCompactPAAddSuccDiamondBridge

#print axioms PASoundness.PAtoCompactPAAddSuccDiamondBridge.add_succ_of_diamond
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondBridge.add_succ_of_diamond_certificate
