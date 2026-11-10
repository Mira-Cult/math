import PASoundness.PAtoCompactUnaryTermTransport

/-! The closure of unary terms under successor and addition of zero on the
right. Evidence is Type-valued to permit construction of finite K proofs. -/
namespace PASoundness.PAtoCompactSuccRightZeroGrammar

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactUnaryTermTransport

inductive SuccRightZeroTerm {α : Type} : Peano.language.Term α → Type
  | unary {t : Peano.language.Term α} : UnaryTerm t → SuccRightZeroTerm t
  | succ {t : Peano.language.Term α} : SuccRightZeroTerm t →
      SuccRightZeroTerm (.func .succ ![t])
  | addZero {t : Peano.language.Term α} : SuccRightZeroTerm t →
      SuccRightZeroTerm (.func .add ![t, .func .zero Fin.elim0])

end PASoundness.PAtoCompactSuccRightZeroGrammar
