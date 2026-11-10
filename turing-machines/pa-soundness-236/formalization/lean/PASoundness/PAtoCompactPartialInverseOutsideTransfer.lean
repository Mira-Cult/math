import PASoundness.CompactDerivations

/-! Purely syntactic pointwise transport for the outside-prefix branch. The
old invariant and prefix-membership equivalence are explicit premises; this
module does not prove successor behavior, graph existence, or induction. -/
namespace PASoundness.PAtoCompactPartialInverseOutsideTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under the input-domain guard X, an old/new prefix membership equivalence
transports the guarded graph biconditional from M to N. -/
def transfer (X Y H M N O : Nat) : KDerivation
    (imp (imp X (both (imp M N) (imp N M)))
      (imp (imp (both X Y) (both (imp H (both M O)) (imp (both M O) H)))
        (imp (both X Y) (both (imp H (both N O)) (imp (both N O) H))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := imp X (both (imp M N) (imp N M))
  let P := imp (both X Y) (both (imp H (both M O)) (imp (both M O) H))
  let Γ := [both X Y,P,C]
  have hguard : Context Γ (both X Y) := Context.head _ _
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hs : Context Γ (both (imp M N) (imp N M)) := .mp (Context.conjunctionLeft hguard) hc
  have old : Context Γ (both (imp H (both M O)) (imp (both M O) H)) := .mp hguard hp
  have hforward : Context Γ (imp H (both N O)) := by
    apply Context.deduction
    let Δ := [H,both X Y,P,C]
    have hh : Context Δ H := Context.head _ _
    have hold : Context Δ (imp H (both M O)) := Context.under (Context.conjunctionLeft old) H
    have hmo : Context Δ (both M O) := .mp hh hold
    have hn : Context Δ N := .mp (Context.conjunctionLeft hmo)
      (Context.under (Context.conjunctionLeft hs) H)
    exact Context.conjunctionIntro hn (Context.conjunctionRight hmo)
  have hback : Context Γ (imp (both N O) H) := by
    apply Context.deduction
    let Δ := [both N O,both X Y,P,C]
    have hno : Context Δ (both N O) := Context.head _ _
    have hm : Context Δ M := .mp (Context.conjunctionLeft hno)
      (Context.under (Context.conjunctionRight hs) (both N O))
    have hmo : Context Δ (both M O) := Context.conjunctionIntro hm (Context.conjunctionRight hno)
    exact .mp hmo (Context.under (Context.conjunctionRight old) (both N O))
  exact Context.conjunctionIntro hforward hback

theorem transfer_certificate (X Y H M N O : Nat) :
    theoremCode (certificate (transfer X Y H M N O)) =
      imp (imp X (both (imp M N) (imp N M)))
        (imp (imp (both X Y) (both (imp H (both M O)) (imp (both M O) H)))
          (imp (both X Y) (both (imp H (both N O)) (imp (both N O) H)))) :=
  certificate_correct (transfer X Y H M N O)

end PASoundness.PAtoCompactPartialInverseOutsideTransfer

#print axioms PASoundness.PAtoCompactPartialInverseOutsideTransfer.transfer
#print axioms PASoundness.PAtoCompactPartialInverseOutsideTransfer.transfer_certificate
