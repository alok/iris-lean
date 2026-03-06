import Iris.Algebra.Excl
import Iris.Instances.IProp.ProofMode

namespace Iris

open COFE BI

/-! A small ownership wrapper for unique tokens, mirroring `base_logic/lib/token.v`. -/

abbrev tokenOF : OFunctorPre := constOF (Excl Unit)

class abbrev TokenG (GF : BundledGFunctors) := ElemG GF tokenOF

def token {GF} [TokenG GF] (γ : GName) : IProp GF :=
  iOwn (GF := GF) (F := tokenOF) γ (.excl ())

section token

variable {GF : BundledGFunctors} [TokenG GF]

theorem token_alloc : ⊢ |==> ∃ γ, token (GF := GF) γ := by
  simpa [token] using
    (iOwn_alloc (GF := GF) (F := tokenOF) (a := Excl.excl ()) (show ✓ (Excl.excl ()) by trivial))

theorem token_exclusive_2 (γ : GName) : token (GF := GF) γ ∗ token γ ⊢ False := by
  simpa [token] using
    (iOwn_invalid_2 (GF := GF) (F := tokenOF) (γ := γ) (a1 := Excl.excl ()) (a2 := Excl.excl ())
      (CMRA.not_valid_exclN_op_left (n := 0) (x := Excl.excl ()) (y := Excl.excl ())))

theorem token_exclusive (γ : GName) : ⊢ token (GF := GF) γ -∗ token γ -∗ False :=
  entails_wand <| wand_intro <| token_exclusive_2 (GF := GF) γ

end token

end Iris
