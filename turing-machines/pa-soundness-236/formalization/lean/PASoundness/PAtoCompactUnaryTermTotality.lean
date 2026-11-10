import PASoundness.PAtoCompactVariableTotalityGeneral
import PASoundness.PAtoCompactGuardedEqualityReflexivity
import PASoundness.PAtoCompactGuardBaseTransport

/-! Guarded variable-term graph existence. The zero and successor branches
are separate obligations; this module does not claim unary-term totality. -/
namespace PASoundness.PAtoCompactUnaryTermTotality

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedEqualityReflexivity

/-- A listed variable candidate supplies a variable graph output. Names must
be fresh for the generated block and output binder; their assigned objects may
coincide. The variable carrier and name map are arbitrary. -/
def variable_of_guardList {α : Type} (v : α → Nat) (p : α) (base out : Nat)
    (xs : List Nat) (hmem : v p ∈ xs) (hp : v p < base)
    (hout : out < base) (hne : out ≠ v p) :
    KDerivation (imp (guardList base xs).encode
      (existsCode out (termGraph v (.var p : Peano.language.Term α) out base).encode)) :=
  compose (guardList_projection base (v p) xs hmem)
    (PAtoCompactVariableTotalityGeneral.variable_graph_total v p base out hp hout hne)

theorem variable_of_guardList_certificate {α : Type} (v : α → Nat) (p : α)
    (base out : Nat) (xs : List Nat) (hmem : v p ∈ xs) (hp : v p < base)
    (hout : out < base) (hne : out ≠ v p) :
    theoremCode (certificate (variable_of_guardList v p base out xs hmem hp hout hne)) =
      imp (guardList base xs).encode
        (existsCode out (termGraph v (.var p : Peano.language.Term α) out base).encode) :=
  certificate_correct _

/-- The actual guard for a source formula supplies a graph value for any
variable name occurring free in that formula. -/
def variable_of_guardFormula {α : Type} (v : α → Nat) (p : α)
    (φ : Peano.Formula) (base out : Nat) (hmem : v p ∈ φ.freeVarFinset)
    (hp : v p < base) (hout : out < base) (hne : out ≠ v p) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode out (termGraph v (.var p : Peano.language.Term α) out base).encode)) := by
  have hguard : v p < guardBase φ := by
    have hle : v p ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hmem
    unfold guardBase
    omega
  exact compose (guardFormula_projection φ (v p) hmem)
    (compose (PAtoCompactGuardBaseTransport.domainAt_transport (guardBase φ) base (v p)
      (by omega) (by omega))
      (PAtoCompactVariableTotalityGeneral.variable_graph_total v p base out hp hout hne))

theorem variable_of_guardFormula_certificate {α : Type} (v : α → Nat) (p : α)
    (φ : Peano.Formula) (base out : Nat) (hmem : v p ∈ φ.freeVarFinset)
    (hp : v p < base) (hout : out < base) (hne : out ≠ v p) :
    theoremCode (certificate (variable_of_guardFormula v p φ base out hmem hp hout hne)) =
      imp (guardFormula φ).encode
        (existsCode out (termGraph v (.var p : Peano.language.Term α) out base).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactUnaryTermTotality

#print axioms PASoundness.PAtoCompactUnaryTermTotality.variable_of_guardList
#print axioms PASoundness.PAtoCompactUnaryTermTotality.variable_of_guardList_certificate
#print axioms PASoundness.PAtoCompactUnaryTermTotality.variable_of_guardFormula
#print axioms PASoundness.PAtoCompactUnaryTermTotality.variable_of_guardFormula_certificate
