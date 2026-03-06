import Iris.Algebra.DFracAgree
import Iris.Instances.IProp.ProofMode

namespace Iris

open COFE OFE BI DFracAgree

abbrev ghostVarOF (Q : Type _) [UFraction Q] (A : Type _) : OFunctorPre :=
  constOF (DFracAgree Q (LeibnizO A))

class abbrev GhostVarG (Q : Type _) [UFraction Q] (A : Type _) (GF : BundledGFunctors) :=
  ElemG GF (ghostVarOF Q A)

def ghostVar {Q A GF} [UFraction Q] [GhostVarG Q A GF] (γ : GName) (q : Q) (a : A) : IProp GF :=
  iOwn (GF := GF) (F := ghostVarOF Q A) γ (toFracAgree q ⟨a⟩)

section ghostVar

variable {Q A : Type _} {GF : BundledGFunctors} [UFraction Q] [GhostVarG Q A GF]

theorem ghostVar_alloc (a : A) : ⊢ |==> ∃ γ, ghostVar (Q := Q) (A := A) (GF := GF) γ One.one a := by
  simpa [ghostVar] using
    (iOwn_alloc (GF := GF) (F := ghostVarOF Q A) (a := toFracAgree (F := Q) (A := LeibnizO A) One.one ⟨a⟩)
      (show ✓ (toFracAgree (F := Q) (A := LeibnizO A) One.one ⟨a⟩) by
        change ✓ ((DFrac.own One.one : DFrac Q), toAgree (⟨a⟩ : LeibnizO A))
        exact ⟨DFrac.valid_own_one, fun _ => trivial⟩))

theorem ghostVar_valid_2_sep (γ : GName) (q1 q2 : Q) (a1 a2 : A) :
    ghostVar (Q := Q) (A := A) (GF := GF) γ q1 a1 ∗ ghostVar γ q2 a2 ⊢
      ⌜✓ (DFrac.own q1 • DFrac.own q2 : DFrac Q) ∧ a1 = a2⌝ := by
  refine (iOwn_cmraValid_op (GF := GF) (F := ghostVarOF Q A) (γ := γ)).trans ?_
  refine (UPred.cmraValid_elim _).trans ?_
  apply pure_elim'
  intro h
  have h' : ✓ (toFracAgree (F := Q) (A := LeibnizO A) q1 (⟨a1⟩ : LeibnizO A) •
      toFracAgree (F := Q) (A := LeibnizO A) q2 (⟨a2⟩ : LeibnizO A)) := CMRA.discrete_valid h
  exact pure_intro <| by
    simpa using
      (fracAgree_op_valid_L (F := Q) (A := LeibnizO A) q1 q2 (⟨a1⟩ : LeibnizO A) (⟨a2⟩ : LeibnizO A)).mp h'

theorem ghostVar_valid_2 (γ : GName) (q1 q2 : Q) (a1 a2 : A) :
    ⊢ ghostVar (Q := Q) (A := A) (GF := GF) γ q1 a1 -∗ ghostVar γ q2 a2 -∗
      ⌜✓ (DFrac.own q1 • DFrac.own q2 : DFrac Q) ∧ a1 = a2⌝ :=
  entails_wand <| wand_intro <| ghostVar_valid_2_sep (Q := Q) (A := A) (γ := γ) q1 q2 a1 a2

theorem ghostVar_agree (γ : GName) (q1 q2 : Q) (a1 a2 : A) :
    ⊢ ghostVar (Q := Q) (A := A) (GF := GF) γ q1 a1 -∗ ghostVar γ q2 a2 -∗ ⌜a1 = a2⌝ := by
  refine entails_wand <| wand_intro <|
    (ghostVar_valid_2_sep (Q := Q) (A := A) (γ := γ) q1 q2 a1 a2).trans <|
      pure_elim' (fun h => pure_intro h.2)

theorem ghostVar_split (γ : GName) (q1 q2 : Q) (a : A) :
    ghostVar (Q := Q) (A := A) (GF := GF) γ (q1 + q2) a ⊣⊢ ghostVar γ q1 a ∗ ghostVar γ q2 a := by
  refine (equiv_iff.mp <| (iOwn_ne (GF := GF) (F := ghostVarOF Q A) (τ := γ)).eqv
    (DFracAgree.fracAgree_op (F := Q) (A := LeibnizO A) q1 q2 ⟨a⟩)).trans ?_
  simpa [ghostVar] using
    (iOwn_op (GF := GF) (F := ghostVarOF Q A) (γ := γ)
      (a1 := toFracAgree (F := Q) (A := LeibnizO A) q1 ⟨a⟩)
      (a2 := toFracAgree (F := Q) (A := LeibnizO A) q2 ⟨a⟩))

theorem ghostVar_update (γ : GName) (a b : A) :
    ghostVar (Q := Q) (A := A) (GF := GF) γ (One.one : Q) a ⊢ |==> ghostVar γ (One.one : Q) b := by
  apply iOwn_update (GF := GF) (F := ghostVarOF Q A) (γ := γ)
  letI : CMRA.Exclusive (toFracAgree (F := Q) (A := LeibnizO A) (One.one : Q) (⟨a⟩ : LeibnizO A)) :=
    toFracAgree_one_exclusive (F := Q) (A := LeibnizO A)
  apply Update.exclusive
  change ✓ ((DFrac.own (One.one : Q) : DFrac Q), toAgree (⟨b⟩ : LeibnizO A))
  exact ⟨DFrac.valid_own_one, fun _ => trivial⟩

theorem ghostVar_update_2 (γ : GName) (q1 q2 : Q) (a1 a2 b : A) (hq : q1 + q2 = (One.one : Q)) :
    ghostVar (Q := Q) (A := A) (GF := GF) γ q1 a1 ∗ ghostVar γ q2 a2 ⊢
      |==> (ghostVar γ q1 b ∗ ghostVar γ q2 b) := by
  refine (show ghostVar (Q := Q) (A := A) (GF := GF) γ q1 a1 ∗ ghostVar γ q2 a2 ⊢
      iOwn (GF := GF) (F := ghostVarOF Q A) γ
        (toFracAgree (F := Q) (A := LeibnizO A) q1 (⟨a1⟩ : LeibnizO A) •
          toFracAgree (F := Q) (A := LeibnizO A) q2 (⟨a2⟩ : LeibnizO A)) from by
      simpa [ghostVar] using
        (iOwn_op (GF := GF) (F := ghostVarOF Q A) (γ := γ)
          (a1 := toFracAgree (F := Q) (A := LeibnizO A) q1 ⟨a1⟩)
          (a2 := toFracAgree (F := Q) (A := LeibnizO A) q2 ⟨a2⟩)).mpr).trans ?_
  refine (iOwn_update (GF := GF) (F := ghostVarOF Q A) (γ := γ)
      (DFracAgree.fracAgree_update_2 (F := Q) (A := LeibnizO A) q1 q2 (⟨a1⟩ : LeibnizO A) (⟨a2⟩ : LeibnizO A)
        (⟨b⟩ : LeibnizO A) hq)).trans <|
    BIUpdate.mono (PROP := IProp GF) <|
      (show iOwn (GF := GF) (F := ghostVarOF Q A) γ
          (toFracAgree (F := Q) (A := LeibnizO A) q1 (⟨b⟩ : LeibnizO A) •
            toFracAgree (F := Q) (A := LeibnizO A) q2 (⟨b⟩ : LeibnizO A)) ⊢
          ghostVar (Q := Q) (A := A) (GF := GF) γ q1 b ∗ ghostVar γ q2 b from by
        simpa [ghostVar] using
          (iOwn_op (GF := GF) (F := ghostVarOF Q A) (γ := γ)
            (a1 := toFracAgree (F := Q) (A := LeibnizO A) q1 ⟨b⟩)
            (a2 := toFracAgree (F := Q) (A := LeibnizO A) q2 ⟨b⟩)).mp)

end ghostVar

end Iris
