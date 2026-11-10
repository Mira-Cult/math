import PASoundness.PAtoCompactZeroSuccessor

/-! Conditional syntactic injectivity of the compact successor graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorInjective
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactMatrix PASoundness.CompactSemantics
open PASoundness.PAtoCompactZeroSuccessor

/-- K can inspect any chosen element of a successor graph when the graph's
bound test name is distinct from its input, output, and the chosen element. -/
def successor_inspect (x y w q : Nat) (hwx : w ≠ x) (hwy : w ≠ y) (hwq : w ≠ q) :
    KDerivation (imp (successorCode x y w)
      (imp (member y q) (either (equal q x) (member x q)))) := by
  let body := namedSuccessorBody x y w
  have hinst := CompactNamed.universalInstance w q body hwq
    (by simp [body, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [body, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders])
  have hstep : KDerivation (imp (successorCode x y w)
      (both (imp (member y q) (either (equal q x) (member x q)))
        (imp (either (equal q x) (member x q)) (member y q)))) := by
    simpa [body, namedSuccessorBody, namedBoth, namedEither, successorCode,
      CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hwx, hwy, hwq, Ne.symm hwx, Ne.symm hwy, Ne.symm hwq] using hinst
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (.mp (Context.head [] (successorCode x y w)) (.closed hstep))

/-- No two sets can contain each other, true in the standard HF coding. This
is a semantic result only; no K proof of the scheme is asserted. -/
theorem no_two_cycle_true (x u : Nat) (ρ : Environment) :
    (decode (imp (member u x) (neg (member x u)))).Realize ρ := by
  simp only [realize_imp, realize_neg, realize_member]
  intro h1 h2
  have hlt1 := member_lt (ρ u) (ρ x) h1
  have hlt2 := member_lt (ρ x) (ρ u) h2
  omega

/-- Full literal K proof of successor injectivity, under an explicit
no-membership-two-cycle premise. No semantic soundness is used. -/
def successor_injective_from_no_cycle (x u y v w : Nat)
    (hwx : w ≠ x) (hwu : w ≠ u) (hwy : w ≠ y) (hwv : w ≠ v) :
    KDerivation (imp (successorCode x y w)
      (imp (successorCode u v w)
        (imp (equal y v)
          (imp (imp (member u x) (neg (member x u))) (equal x u))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [imp (member u x) (neg (member x u)), equal y v,
    successorCode u v w, successorCode x y w]
  have hn : Context Γ (imp (member u x) (neg (member x u))) := .hypothesis (by simp [Γ])
  have he : Context Γ (equal y v) := .hypothesis (by simp [Γ])
  have hsx : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hsu : Context Γ (successorCode u v w) := .hypothesis (by simp [Γ])
  have hxmem : Context Γ (member y x) := .mp hsx (.closed (successor_contains_input x y w hwx hwy))
  have humem : Context Γ (member v u) := .mp hsu (.closed (successor_contains_input u v w hwu hwv))
  have hxv : Context Γ (member v x) := .mp hxmem (.mp he (.closed (memberLeftEquality y v x)))
  have huy : Context Γ (member y u) := .mp humem (.mp (Context.eqSymm he) (.closed (memberLeftEquality v y u)))
  have hleft : Context Γ (either (equal x u) (member u x)) :=
    .mp hxv (.mp hsu (.closed (successor_inspect u v w x hwu hwv hwx)))
  have hright : Context Γ (either (equal u x) (member x u)) :=
    .mp huy (.mp hsx (.closed (successor_inspect x y w u hwx hwy hwu)))
  apply Context.disjunctionElim hleft
  · exact Context.head Γ (equal x u)
  · let Δ := member u x :: Γ
    have hmux : Context Δ (member u x) := .hypothesis (by simp [Δ])
    have hnot : Context Δ (neg (member x u)) := .mp hmux (Context.under hn (member u x))
    have hright' : Context Δ (either (equal u x) (member x u)) := Context.under hright (member u x)
    apply Context.disjunctionElim hright'
    · exact Context.eqSymm (Context.head Δ (equal u x))
    · have hbad : Context (member x u :: Δ) 1 := .mp (Context.head Δ (member x u))
        (Context.under hnot (member x u))
      exact Context.explode (equal x u) hbad

theorem successor_injective_certificate (x u y v w : Nat)
    (hwx : w ≠ x) (hwu : w ≠ u) (hwy : w ≠ y) (hwv : w ≠ v) :
    theoremCode (certificate (successor_injective_from_no_cycle x u y v w hwx hwu hwy hwv)) =
      imp (successorCode x y w)
        (imp (successorCode u v w)
          (imp (equal y v) (imp (imp (member u x) (neg (member x u))) (equal x u)))) :=
  certificate_correct (successor_injective_from_no_cycle x u y v w hwx hwu hwy hwv)

/-- On ordinal-coded natural inputs, the interpreted successor outputs are
equal exactly when the original natural inputs are equal. This is the separate
semantic counterpart of the syntactic PA successor-injectivity schema. -/
theorem ordinal_successor_graph_injective (x u y v w n m : Nat) (ρ : Environment)
    (hxw : x ≠ w) (huw : u ≠ w) (hyw : y ≠ w) (hvw : v ≠ w)
    (hx : ρ x = (HFCoding.ordinal n).code) (hu : ρ u = (HFCoding.ordinal m).code)
    (hsx : (decode (successorCode x y w)).Realize ρ)
    (hsu : (decode (successorCode u v w)).Realize ρ) :
    ρ y = ρ v ↔ n = m := by
  have hy := (ordinal_successor_relation x y w n ρ hxw hyw hx).mp hsx
  have hv := (ordinal_successor_relation u v w m ρ huw hvw hu).mp hsu
  rw [hy, hv]
  constructor
  · intro h
    have hobj := HFCoding.code_injective h
    have hn := HFCoding.ordinal_injective hobj
    omega
  · rintro rfl
    rfl

end PASoundness.PAtoCompactSuccessorInjective
