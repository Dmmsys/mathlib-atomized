/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing

/-!
# The opposite of a pairing

Let `A` be a subcomplex of a simplicial set `X`. If `P` is a pairing of `A`,
we construct a pairing `P.op` for the subcomplex `A.op` of `X.op`.

-/

@[expose] public section

universe u

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

/-- If `P` is a pairing for a subcomplex `A` of a simplicial set `X`,
this is the corresponding pairing of `A.op`. -/
@[simps I II]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : A.op.Pairing where
  body: Subcomplex.N.opEquiv ⁻¹' P.I
  II := Subcomplex.N.opEquiv ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := (N.opEquiv.subtypeEquiv (by simp)).trans
    (P.p.trans (N.opEquiv.symm.subtypeEquiv (by simp)))

中文:
定义 op
  签名: : A.op.Pairing where
  定义体: Subcomplex.N.opEquiv ⁻¹' P.I
  II := Subcomplex.N.opEquiv ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := (N.opEquiv.subtypeEquiv (by simp)).trans
    (P.p.trans (N.opEquiv.symm.subtypeEquiv (by simp)))

Depends on / 依赖: Subcomplex, Subcomplex.N.opEquiv, opEquiv
-/
def op : A.op.Pairing where
  I := Subcomplex.N.opEquiv ⁻¹' P.I
  II := Subcomplex.N.opEquiv ⁻¹' P.II
  inter := by simp [← Set.preimage_inter, P.inter]
  union := by simp [← Set.preimage_union, P.union]
  p := (N.opEquiv.subtypeEquiv (by simp)).trans
    (P.p.trans (N.opEquiv.symm.subtypeEquiv (by simp)))

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `op_p` / 引理 `op_p`

English:
lemma op_p
  given: (x : P.II)
  proof: rfl

中文:
引理 op_p
  条件: (x : P.II)
  证明: rfl
-/
lemma op_p (x : P.II) :
    dsimp% P.op.p ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩ =
      ⟨Subcomplex.N.opEquiv.symm (P.p x), by simp⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `op_ancestralRel_iff` / 引理 `op_ancestralRel_iff`

English:
lemma op_ancestralRel_iff
  given: (x y : P.II)
  proof: and_congr (not_congr (by aesop)) (by simp)

中文:
引理 op_ancestralRel_iff
  条件: (x y : P.II)
  证明: and_congr (not_congr (by aesop)) (by simp)

Depends on / 依赖: and_congr, not_congr
-/
lemma op_ancestralRel_iff (x y : P.II) :
    P.op.AncestralRel ⟨Subcomplex.N.opEquiv.symm x.1, x.2⟩
      ⟨Subcomplex.N.opEquiv.symm y.1, y.2⟩ ↔ P.AncestralRel x y :=
  and_congr (not_congr (by aesop)) (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsProper]
  signature: : P.op.IsProper where
  body: (P.isUniquelyCodimOneFace ⟨_, x.2⟩).op

中文:
实例 [P.是真]
  签名: : P.op.是真 where
  定义体: (P.isUniquelyCodimOneFace ⟨_, x.2⟩).op

Depends on / 依赖: P.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
instance [P.IsProper] : P.op.IsProper where
  isUniquelyCodimOneFace x := (P.isUniquelyCodimOneFace ⟨_, x.2⟩).op

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsRegular]
  signature: : P.op.IsRegular where
  body: by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n => ⟨_, (f n).2⟩, fun n => ?_⟩
    simpa [← P.op_ancestralRel_iff] using hf n

中文:
实例 [P.是正则]
  签名: : P.op.是正则 where
  定义体: by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n => ⟨_, (f n).2⟩, fun n => ?_⟩
    simpa [← P.op_ancestralRel_iff] using hf n

Depends on / 依赖: P.op_ancestralRel_iff, P.wf, hP.false, op_ancestralRel_iff, wellFounded_iff_isEmpty_descending_chain
-/
instance [P.IsRegular] : P.op.IsRegular where
  wf := by
    have hP := P.wf
    rw [wellFounded_iff_isEmpty_descending_chain] at hP ⊢
    by_contra!
    obtain ⟨f, hf⟩ := this
    refine hP.false ⟨fun n => ⟨_, (f n).2⟩, fun n => ?_⟩
    simpa [← P.op_ancestralRel_iff] using hf n

end SSet.Subcomplex.Pairing
