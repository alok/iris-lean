import Iris.Instances.IProp.Instance
import Iris.ProofMode.Classes

namespace Iris
open COFE
open ProofMode

section iOwn

open IProp

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

instance intoSep_iOwn (γ : GName) (a1 a2 : F.ap (IProp GF)) :
    IntoSep iprop(iOwn γ (a1 • a2)) iprop(iOwn γ a1) iprop(iOwn γ a2) where
  into_sep := iOwn_op.1

instance fromSep_iOwn (γ : GName) (a1 a2 : F.ap (IProp GF)) :
    FromSep iprop(iOwn γ (a1 • a2)) iprop(iOwn γ a1) iprop(iOwn γ a2) where
  from_sep := iOwn_op.2

end iOwn
end Iris
