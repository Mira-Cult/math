import PASoundness.PAtoCompactUnaryTermTransport

/-! Terms obtained from a unary term by repeatedly adding zero on the right.
Evidence is Type-valued so finite K proof data can be built by recursion. -/
namespace PASoundness.PAtoCompactRightZeroTermGrammar

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactUnaryTermTransport

inductive RightZeroTerm {α : Type} : Peano.language.Term α → Type
  | unary {t : Peano.language.Term α} : UnaryTerm t → RightZeroTerm t
  | addZero {t : Peano.language.Term α} : RightZeroTerm t →
      RightZeroTerm (.func .add ![t, .func .zero Fin.elim0])

end PASoundness.PAtoCompactRightZeroTermGrammar
