/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite

/-!
# The extension of a homological complex by an embedding of complex shapes

Given an embedding `e : Embedding c c'` of complex shapes,
and `K : HomologicalComplex C c`, we define `K.extend e : HomologicalComplex C c'`, and this
leads to a functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`.

This construction first appeared in the Liquid Tensor Experiment.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C]

section

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : Option ι -> C

中文:
定义 X
  签名: : 选项类型 ι -> C
-/
noncomputable def X : Option ι -> C
  | some x => K.X x
  | none => 0

/--
Definition of `XIso` / `XIso` 的定义

English:
definition XIso
  signature: {i : Option ι} {j : ι} (hj : i = some j)
  body: eqToIso (by subst hj; rfl)

中文:
定义 XIso
  签名: {i : 选项类型 ι} {j : ι} (hj : i = some j)
  定义体: eqToIso (by subst hj; rfl)

Depends on / 依赖: HasHomology, K.op.truncGE, e.op, eqToIso, truncGE, unop.HasHomology
-/
noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

/--
lemma `isZero_X` / 引理 `isZero_X`

English:
lemma isZero_X
  given: {i : Option ι} (hi : i = none)
  proof: by
  subst hi
  exact Limits.isZero_zero _

中文:
引理 isZero_X
  条件: {i : 选项类型 ι} (hi : i = none)
  证明: by
  subst hi
  exact Limits.isZero_zero _

Depends on / 依赖: Limits, Limits.isZero_zero, isZero_zero
-/
lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

/--
Definition of `XOpIso` / `XOpIso` 的定义

English:
definition XOpIso
  signature: (i : Option ι)
  body: match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (isZero_X _ rfl) (isZero_X K rfl).op

中文:
定义 XOpIso
  签名: (i : 选项类型 ι)
  定义体: match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (isZero_X _ rfl) (isZero_X K rfl).op

Depends on / 依赖: IsZero, IsZero.iso, Iso.refl, K.quasiIsoAt_, isZero_X
-/
noncomputable def XOpIso (i : Option ι) : X K.op i ≅ Opposite.op (X K i) :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (isZero_X _ rfl) (isZero_X K rfl).op

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: : forall (i j : Option ι), extend.X K i ⟶ extend.X K j

中文:
定义 d
  签名: : 对任意 (i j : 选项类型 ι), extend.X K i ⟶ extend.X K j
-/
noncomputable def d : forall (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0

/--
lemma `d_none_eq_zero` / 引理 `d_none_eq_zero`

English:
lemma d_none_eq_zero
  given: (i j : Option ι) (hi : i = none)
  proof: by subst hi; rfl

中文:
引理 d_none_eq_zero
  条件: (i j : 选项类型 ι) (hi : i = none)
  证明: by subst hi; rfl
-/
lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl

/--
lemma `d_none_eq_zero'` / 引理 `d_none_eq_zero'`

English:
lemma d_none_eq_zero'
  given: (i j : Option ι) (hj : j = none)
  proof: by subst hj; cases i <;> rfl

中文:
引理 d_none_eq_zero'
  条件: (i j : 选项类型 ι) (hj : j = none)
  证明: by subst hj; cases i <;> rfl
-/
lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `d_eq` / 引理 `d_eq`

English:
lemma d_eq
  given: {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b)
  proof: by
  subst hi hj
  simp [XIso, X, d]

中文:
引理 d_eq
  条件: {i j : 选项类型 ι} {a b : ι} (hi : i = some a) (hj : j = some b)
  证明: by
  subst hi hj
  simp [XIso, X, d]
-/
lemma d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  simp [XIso, X, d]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `XOpIso_hom_d_op` / 引理 `XOpIso_hom_d_op`

English:
lemma XOpIso_hom_d_op
  given: (i j : Option ι)
  proof: match i, j with
  | none, _ => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [XOpIso]
      simp only [d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]

中文:
引理 XOpIso_hom_d_op
  条件: (i j : 选项类型 ι)
  证明: match i, j with
  | none, _ => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [XOpIso]
      simp only [d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]

Depends on / 依赖: XOpIso, comp_id, comp_zero, d_eq, d_none_eq_zero, id_comp, op_comp, op_zero, zero_comp
-/
lemma XOpIso_hom_d_op (i j : Option ι) :
    (XOpIso K i).hom ≫ (d K j i).op =
      d K.op i j ≫ (XOpIso K j).hom :=
  match i, j with
  | none, _ => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [XOpIso]
      simp only [d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]

variable {K L}

/--
Definition of `mapX` / `mapX` 的定义

English:
definition mapX
  signature: : forall (i : Option ι), X K i ⟶ X L i

中文:
定义 mapX
  签名: : 对任意 (i : 选项类型 ι), X K i ⟶ X L i
-/
noncomputable def mapX : forall (i : Option ι), X K i ⟶ X L i
  | some i => φ.f i
  | none => 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mapX_some` / 引理 `mapX_some`

English:
lemma mapX_some
  given: {i : Option ι} {a : ι} (hi : i = some a)
  proof: by
  subst hi
  dsimp [XIso, X]
  rw [id_comp]; rw [comp_id]
  rfl

中文:
引理 mapX_some
  条件: {i : 选项类型 ι} {a : ι} (hi : i = some a)
  证明: by
  subst hi
  dsimp [XIso, X]
  rw [id_comp]; rw [comp_id]
  rfl

Depends on / 依赖: comp_id, id_comp
-/
lemma mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    mapX φ i = (XIso K hi).hom ≫ φ.f a ≫ (XIso L hi).inv := by
  subst hi
  dsimp [XIso, X]
  rw [id_comp]; rw [comp_id]
  rfl

/--
lemma `mapX_none` / 引理 `mapX_none`

English:
lemma mapX_none
  given: {i : Option ι} (hi : i = none)
  proof: by subst hi; rfl

中文:
引理 mapX_none
  条件: {i : 选项类型 ι} (hi : i = none)
  证明: by subst hi; rfl
-/
lemma mapX_none {i : Option ι} (hi : i = none) :
    mapX φ i = 0 := by subst hi; rfl

end extend

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: : HomologicalComplex C c' where
  body: extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj, K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk' | ⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj, extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

中文:
定义 extend
  签名: : 同调复形 C c' where
  定义体: extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj, K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk' | ⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj, extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

Depends on / 依赖: extend, extend.X
-/
noncomputable def extend : HomologicalComplex C c' where
  X i' := extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj, K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk' | ⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj, extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

/--
Definition of `extendXIso` / `extendXIso` 的定义

English:
definition extendXIso
  signature: {i' : ι'} {i : ι} (h : e.f i = i')
  body: extend.XIso K (e.r_eq_some h)

中文:
定义 extendXIso
  签名: {i' : ι'} {i : ι} (h : e.f i = i')
  定义体: extend.XIso K (e.r_eq_some h)

Depends on / 依赖: e.r_eq_some, extend, extend.XIso, r_eq_some
-/
noncomputable def extendXIso {i' : ι'} {i : ι} (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K (e.r_eq_some h)

/--
lemma `isZero_extend_X'` / 引理 `isZero_extend_X'`

English:
lemma isZero_extend_X'
  given: (i' : ι') (hi' : e.r i' = none)
  proof: extend.isZero_X K hi'

中文:
引理 isZero_extend_X'
  条件: (i' : ι') (hi' : e.r i' = none)
  证明: extend.isZero_X K hi'

Depends on / 依赖: extend, extend.isZero_X, isZero_X
-/
lemma isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K hi'

/--
lemma `isZero_extend_X` / 引理 `isZero_extend_X`

English:
lemma isZero_extend_X
  given: (i' : ι') (hi' : forall i, e.f i != i')
  proof: K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')

中文:
引理 isZero_extend_X
  条件: (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')

Depends on / 依赖: ComplexShape, ComplexShape.Embedding.r_eq_none, Embedding, K.isZero_extend_X, isZero_extend_X, r_eq_none
-/
lemma isZero_extend_X (i' : ι') (hi' : forall i, e.f i != i') :
    IsZero ((K.extend e).X i') :=
  K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (K.extend e).IsStrictlySupported e
  body: K.isZero_extend_X e i' hi'

中文:
实例 :
  签名: (K.extend e).是StrictlySupported e
  定义体: K.isZero_extend_X e i' hi'

Depends on / 依赖: K.isZero_extend_X, isZero_extend_X
-/
instance : (K.extend e).IsStrictlySupported e where
  isZero i' hi' := K.isZero_extend_X e i' hi'

/--
lemma `extend_d_eq` / 引理 `extend_d_eq`

English:
lemma extend_d_eq
  given: {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j')
  proof: by
  apply extend.d_eq

中文:
引理 extend_d_eq
  条件: {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j')
  证明: by
  apply extend.d_eq

Depends on / 依赖: d_eq, extend, extend.d_eq
-/
lemma extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫
      (K.extendXIso e hj).inv := by
  apply extend.d_eq

/--
lemma `extend_d_from_eq_zero` / 引理 `extend_d_from_eq_zero`

English:
lemma extend_d_from_eq_zero
  given: (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i))
  proof: by
  obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

中文:
引理 extend_d_from_eq_zero
  条件: (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.关系 i (c.next i))
  证明: by
  obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

Depends on / 依赖: K.shape, c.next_eq, comp_zero, d_none_eq_zero, e.f_eq_of_r_eq_some, eq_none_or_eq_some, extend, extend.d_none_eq_zero, extend_d_eq, f_eq_of_r_eq_some, next_eq, zero_comp
-/
lemma extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) :
    (K.extend e).d i' j' = 0 := by
  obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

/--
lemma `extend_d_to_eq_zero` / 引理 `extend_d_to_eq_zero`

English:
lemma extend_d_to_eq_zero
  given: (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j)
  proof: by
  obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

中文:
引理 extend_d_to_eq_zero
  条件: (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.关系 (c.prev j) j)
  证明: by
  obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

Depends on / 依赖: K.shape, c.prev_eq, comp_zero, d_none_eq_zero, e.f_eq_of_r_eq_some, eq_none_or_eq_some, extend, extend.d_none_eq_zero, extend_d_eq, f_eq_of_r_eq_some, prev_eq, zero_comp
-/
lemma extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

variable {K L M}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `extendMap` / `extendMap` 的定义

English:
definition extendMap
  signature: : K.extend e ⟶ L.extend e where
  body: extend.mapX φ _
  comm' i' j' _ := by
    by_cases hi : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : exists j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj]; rw [L.extend_d_eq e hi hj]; rw [extend.mapX_some φ (e.r_eq_some hi)]; rw [extend.mapX_some φ (e.r_eq_some hj)]
        simp only [extendXIso, assoc, Iso.inv_hom_id_assoc, Hom.comm_assoc]
      · have hj' := e.r_eq_none j' (fun j'' hj'' => hj ⟨j'', hj''⟩)
        dsimp [extend]
        rw [extend.d_none_eq_zero' _ _ _ hj']; rw [extend.d_none_eq_zero' _ _ _ hj']; rw [comp_zero]; rw [zero_comp]
    · have hi' := e.r_eq_none i' (fun i'' hi'' => hi ⟨i'', hi''⟩)
      dsimp [extend]
      rw [extend.d_none_eq_zero _ _ _ hi']; rw [extend.d_none_eq_zero _ _ _ hi']; rw [comp_zero]; rw [zero_comp]

中文:
定义 extendMap
  签名: : K.extend e ⟶ L.extend e where
  定义体: extend.mapX φ _
  comm' i' j' _ := by
    by_cases hi : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : exists j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj]; rw [L.extend_d_eq e hi hj]; rw [extend.mapX_some φ (e.r_eq_some hi)]; rw [extend.mapX_some φ (e.r_eq_some hj)]
        simp only [extendXIso, assoc, Iso.inv_hom_id_assoc, Hom.comm_assoc]
      · have hj' := e.r_eq_none j' (fun j'' hj'' => hj ⟨j'', hj''⟩)
        dsimp [extend]
        rw [extend.d_none_eq_zero' _ _ _ hj']; rw [extend.d_none_eq_zero' _ _ _ hj']; rw [comp_zero]; rw [zero_comp]
    · have hi' := e.r_eq_none i' (fun i'' hi'' => hi ⟨i'', hi''⟩)
      dsimp [extend]
      rw [extend.d_none_eq_zero _ _ _ hi']; rw [extend.d_none_eq_zero _ _ _ hi']; rw [comp_zero]; rw [zero_comp]

Depends on / 依赖: extend, extend.mapX
-/
noncomputable def extendMap : K.extend e ⟶ L.extend e where
  f _ := extend.mapX φ _
  comm' i' j' _ := by
    by_cases hi : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : exists j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj]; rw [L.extend_d_eq e hi hj]; rw [extend.mapX_some φ (e.r_eq_some hi)]; rw [extend.mapX_some φ (e.r_eq_some hj)]
        simp only [extendXIso, assoc, Iso.inv_hom_id_assoc, Hom.comm_assoc]
      · have hj' := e.r_eq_none j' (fun j'' hj'' => hj ⟨j'', hj''⟩)
        dsimp [extend]
        rw [extend.d_none_eq_zero' _ _ _ hj']; rw [extend.d_none_eq_zero' _ _ _ hj']; rw [comp_zero]; rw [zero_comp]
    · have hi' := e.r_eq_none i' (fun i'' hi'' => hi ⟨i'', hi''⟩)
      dsimp [extend]
      rw [extend.d_none_eq_zero _ _ _ hi']; rw [extend.d_none_eq_zero _ _ _ hi']; rw [comp_zero]; rw [zero_comp]

/--
lemma `extendMap_f` / 引理 `extendMap_f`

English:
lemma extendMap_f
  given: {i : ι} {i' : ι'} (h : e.f i = i')
  proof: by
  dsimp [extendMap]
  rw [extend.mapX_some φ (e.r_eq_some h)]
  rfl

中文:
引理 extendMap_f
  条件: {i : ι} {i' : ι'} (h : e.f i = i')
  证明: by
  dsimp [extendMap]
  rw [extend.mapX_some φ (e.r_eq_some h)]
  rfl

Depends on / 依赖: e.r_eq_some, extend, extend.mapX_some, extendMap, mapX_some, r_eq_some
-/
lemma extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (extendMap φ e).f i' =
      (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e h).inv := by
  dsimp [extendMap]
  rw [extend.mapX_some φ (e.r_eq_some h)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extendMap_f_eq_zero` / 引理 `extendMap_f_eq_zero`

English:
lemma extendMap_f_eq_zero
  given: (i' : ι') (hi' : forall i, e.f i != i')
  proof: by
  dsimp [extendMap]
  rw [extend.mapX_none φ (e.r_eq_none i' hi')]

@[reassoc, simp]

中文:
引理 extendMap_f_eq_zero
  条件: (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: by
  dsimp [extendMap]
  rw [extend.mapX_none φ (e.r_eq_none i' hi')]

@[reassoc, simp]

Depends on / 依赖: e.r_eq_none, extend, extend.mapX_none, extendMap, mapX_none, r_eq_none
-/
lemma extendMap_f_eq_zero (i' : ι') (hi' : forall i, e.f i != i') :
    (extendMap φ e).f i' = 0 := by
  dsimp [extendMap]
  rw [extend.mapX_none φ (e.r_eq_none i' hi')]

@[reassoc, simp]
/--
lemma `extendMap_comp` / 引理 `extendMap_comp`

English:
lemma extendMap_comp
  proof: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

中文:
引理 extendMap_comp
  证明: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

Depends on / 依赖: extendMap_f, extendMap_f_eq_zero
-/
lemma extendMap_comp :
    extendMap (φ ≫ φ') e = extendMap φ e ≫ extendMap φ' e := by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

variable (K L M)

/--
lemma `extendMap_id_f` / 引理 `extendMap_id_f`

English:
lemma extendMap_id_f
  given: (i' : ι')
  statement: (extendMap (𝟙 K) e).f i' = 𝟙 _
  proof: by
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]

中文:
引理 extendMap_id_f
  条件: (i' : ι')
  结论: (extendMap (𝟙 K) e).f i' = 𝟙 _
  证明: by
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]

Depends on / 依赖: F.property, K.isZero_extend_X, eq_of_src, extendMap_f, isZero_extend_X, property
-/
lemma extendMap_id_f (i' : ι') : (extendMap (𝟙 K) e).f i' = 𝟙 _ := by
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
/--
lemma `extendMap_id` / 引理 `extendMap_id`

English:
lemma extendMap_id
  statement: extendMap (𝟙 K) e = 𝟙 _
  proof: by
  ext
  simpa using extendMap_id_f _ _ _

@[simp]

中文:
引理 extendMap_id
  结论: extendMap (𝟙 K) e = 𝟙 _
  证明: by
  ext
  simpa using extendMap_id_f _ _ _

@[simp]

Depends on / 依赖: extendMap_id_f
-/
lemma extendMap_id : extendMap (𝟙 K) e = 𝟙 _ := by
  ext
  simpa using extendMap_id_f _ _ _

@[simp]
/--
lemma `extendMap_zero` / 引理 `extendMap_zero`

English:
lemma extendMap_zero
  statement: extendMap (0 : K ⟶ L) e = 0
  proof: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

中文:
引理 extendMap_zero
  结论: extendMap (0 : K ⟶ L) e = 0
  证明: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

Depends on / 依赖: K.isZero_extend_X, eq_of_src, extendMap_f, isZero_extend_X
-/
lemma extendMap_zero : extendMap (0 : K ⟶ L) e = 0 := by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

/--
Definition of `extendOpIso` / `extendOpIso` 的定义

English:
definition extendOpIso
  signature: : K.op.extend e.op ≅ (K.extend e).op
  body: Hom.isoOfComponents (fun _ => extend.XOpIso _ _) (fun _ _ _ =>
    extend.XOpIso_hom_d_op _ _ _)

中文:
定义 extendOpIso
  签名: : K.op.extend e.op ≅ (K.extend e).op
  定义体: Hom.isoOfComponents (fun _ => extend.XOpIso _ _) (fun _ _ _ =>
    extend.XOpIso_hom_d_op _ _ _)

Depends on / 依赖: Hom.isoOfComponents, XOpIso, XOpIso_hom_d_op, extend, extend.XOpIso, extend.XOpIso_hom_d_op, isoOfComponents
-/
noncomputable def extendOpIso : K.op.extend e.op ≅ (K.extend e).op :=
  Hom.isoOfComponents (fun _ => extend.XOpIso _ _) (fun _ _ _ =>
    extend.XOpIso_hom_d_op _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `extend_op_d` / 引理 `extend_op_d`

English:
lemma extend_op_d
  given: (i' j' : ι')
  proof: by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this]; rw [← comp_f_assoc]; rw [Iso.hom_inv_id]; rw [id_f]; rw [id_comp]

中文:
引理 extend_op_d
  条件: (i' j' : ι')
  证明: by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this]; rw [← comp_f_assoc]; rw [Iso.hom_inv_id]; rw [id_f]; rw [id_comp]

Depends on / 依赖: Iso.hom_inv_id, K.extendOpIso, comp_f_assoc, extendOpIso, hom_inv_id, id_comp, id_f, inv.comm
-/
lemma extend_op_d (i' j' : ι') :
    (K.op.extend e.op).d i' j' =
      (K.extendOpIso e).hom.f i' ≫ ((K.extend e).d j' i').op ≫
        (K.extendOpIso e).inv.f j' := by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this]; rw [← comp_f_assoc]; rw [Iso.hom_inv_id]; rw [id_f]; rw [id_comp]

end

@[simp]
/--
lemma `extendMap_add` / 引理 `extendMap_add`

English:
lemma extendMap_add
  statement: [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L)
  proof: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

中文:
引理 extendMap_add
  结论: [预加性 C] {K L : 同调复形 C c} (φ φ' : K ⟶ L)
  证明: by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

Depends on / 依赖: K.isZero_extend_X, eq_of_src, extendMap_f, isZero_extend_X
-/
lemma extendMap_add [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L)
    (e : c.Embedding c') : extendMap (φ + φ' : K ⟶ L) e = extendMap φ e + extendMap φ' e := by
  ext i'
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

section

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

@[simp]
/--
lemma `extend_single_d` / 引理 `extend_single_d`

English:
lemma extend_single_d
  given: (i : ι) (j' k' : ι')
  proof: by
  by_cases hj : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : exists k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

中文:
引理 extend_single_d
  条件: (i : ι) (j' k' : ι')
  证明: by
  by_cases hj : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : exists k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

Depends on / 依赖: IsZero, IsZero.eq_of_src, IsZero.eq_of_tgt, eq_of_src, eq_of_tgt, extend_d_eq, isZero_extend_X
-/
lemma extend_single_d (i : ι) (j' k' : ι') :
    (((single C c i).obj X).extend e).d j' k' = 0 := by
  by_cases hj : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : exists k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

variable [DecidableEq ι'] (i : ι) (i' : ι')

/--
Definition of `extendSingleIso` / `extendSingleIso` 的定义

English:
definition extendSingleIso
  signature: (h : e.f i = i')
  body: mkHomToSingle
      ((((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom) (by simp)
  inv :=
    mkHomFromSingle
      ((singleObjXSelf c i X).inv ≫ (((single C c i).obj X).extendXIso e h).inv) (by simp)
  hom_inv_id := by
    ext j'
    by_cases hj : exists j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      by_cases hij : j = i
      · obtain rfl : i' = j' := by rw [← hj, hij, h]
        simp
      · exact ((isZero_single_obj_X _ _ _ _ hij).of_iso
          (((single C c i).obj X).extendXIso e hj)).eq_of_src _ _
    · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

@[reassoc]

中文:
定义 extendSingleIso
  签名: (h : e.f i = i')
  定义体: mkHomToSingle
      ((((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom) (by simp)
  inv :=
    mkHomFromSingle
      ((singleObjXSelf c i X).inv ≫ (((single C c i).obj X).extendXIso e h).inv) (by simp)
  hom_inv_id := by
    ext j'
    by_cases hj : exists j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      by_cases hij : j = i
      · obtain rfl : i' = j' := by rw [← hj, hij, h]
        simp
      · exact ((isZero_single_obj_X _ _ _ _ hij).of_iso
          (((single C c i).obj X).extendXIso e hj)).eq_of_src _ _
    · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

@[reassoc]

Depends on / 依赖: IsZero, IsZero.eq_of_src, eq_of_src, extendXIso, hom_inv_id, isZero, isZero_single_obj_X, mkHomFromSingle, mkHomToSingle, of_iso, single, singleObjXSelf
-/
noncomputable def extendSingleIso (h : e.f i = i') :
    ((single C c i).obj X).extend e ≅ (single C c' i').obj X where
  hom :=
    mkHomToSingle
      ((((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom) (by simp)
  inv :=
    mkHomFromSingle
      ((singleObjXSelf c i X).inv ≫ (((single C c i).obj X).extendXIso e h).inv) (by simp)
  hom_inv_id := by
    ext j'
    by_cases hj : exists j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      by_cases hij : j = i
      · obtain rfl : i' = j' := by rw [← hj, hij, h]
        simp
      · exact ((isZero_single_obj_X _ _ _ _ hij).of_iso
          (((single C c i).obj X).extendXIso e hj)).eq_of_src _ _
    · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

@[reassoc]
/--
lemma `extendSingleIso_hom_f` / 引理 `extendSingleIso_hom_f`

English:
lemma extendSingleIso_hom_f
  given: (h : e.f i = i')
  proof: by
  simp [extendSingleIso]

@[reassoc]

中文:
引理 extendSingleIso_hom_f
  条件: (h : e.f i = i')
  证明: by
  simp [extendSingleIso]

@[reassoc]

Depends on / 依赖: extendSingleIso
-/
lemma extendSingleIso_hom_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).hom.f i' =
      (((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom ≫
        (singleObjXSelf c' i' X).inv := by
  simp [extendSingleIso]

@[reassoc]
/--
lemma `extendSingleIso_inv_f` / 引理 `extendSingleIso_inv_f`

English:
lemma extendSingleIso_inv_f
  given: (h : e.f i = i')
  proof: by
  simp [extendSingleIso]

中文:
引理 extendSingleIso_inv_f
  条件: (h : e.f i = i')
  证明: by
  simp [extendSingleIso]

Depends on / 依赖: extendSingleIso
-/
lemma extendSingleIso_inv_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).inv.f i' =
      (singleObjXSelf c' i' X).hom ≫ (singleObjXSelf c i X).inv ≫
        (((single C c i).obj X).extendXIso e h).inv := by
  simp [extendSingleIso]

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] (e
  body: by
  by_cases! hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Projective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').projective

中文:
实例 [有ZeroMorphisms
  签名: C] (e
  定义体: by
  by_cases! hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Projective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').projective

Depends on / 依赖: K.extendXIso, Projective, Projective.of_iso, extendXIso, isZero_extend_X, of_iso, projective
-/
instance [HasZeroMorphisms C] (e : c.Embedding c') (K : HomologicalComplex C c)
    [forall i, Projective (K.X i)] (i' : ι') : Projective ((K.extend e).X i') := by
  by_cases! hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Projective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').projective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] (e
  body: by
  by_cases! hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Injective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').injective

中文:
实例 [有ZeroMorphisms
  签名: C] (e
  定义体: by
  by_cases! hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Injective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').injective

Depends on / 依赖: Injective, Injective.of_iso, K.extendXIso, extendXIso, injective, isZero_extend_X, of_iso
-/
instance [HasZeroMorphisms C] (e : c.Embedding c') (K : HomologicalComplex C c)
    [forall i, Injective (K.X i)] (i' : ι') : Injective ((K.extend e).X i') := by
  by_cases! hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Injective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').injective

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroObject C]

/-- Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomologicalComplex C c ⥤ HomologicalComplex C c'` which
extend complexes along `e`: the extended complexes are zero
in the degrees that are not in the image of `e.f`. -/
@[simps]
/--
Definition of `extendFunctor` / `extendFunctor` 的定义

English:
definition extendFunctor
  signature: [HasZeroMorphisms C]
  body: K.extend e
  map φ := HomologicalComplex.extendMap φ e

中文:
定义 extendFunctor
  签名: [有ZeroMorphisms C]
  定义体: K.extend e
  map φ := HomologicalComplex.extendMap φ e

Depends on / 依赖: K.extend, extend
-/
noncomputable def extendFunctor [HasZeroMorphisms C] :
    HomologicalComplex C c ⥤ HomologicalComplex C c' where
  obj K := K.extend e
  map φ := HomologicalComplex.extendMap φ e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] : (e.extendFunctor C).PreservesZeroMorphisms where

中文:
实例 [有ZeroMorphisms
  签名: C] : (e.extendFunctor C).保持ZeroMorphisms where
-/
instance [HasZeroMorphisms C] : (e.extendFunctor C).PreservesZeroMorphisms where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : (e.extendFunctor C).Additive where

中文:
实例 [预加性
  签名: C] : (e.extendFunctor C).加性 where
-/
instance [Preadditive C] : (e.extendFunctor C).Additive where

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fullyFaithfulExtendFunctor` / `fullyFaithfulExtendFunctor` 的定义

English:
definition fullyFaithfulExtendFunctor
  signature: [HasZeroMorphisms C]
  body: { f i := (K.extendXIso e rfl).inv ≫ φ.f (e.f i) ≫ (L.extendXIso e rfl).hom
      comm' i j h := by
        have := φ.comm (e.f i) (e.f j)
        simp only [extendFunctor_obj, K.extend_d_eq e rfl rfl, L.extend_d_eq e rfl rfl] at this
        simp [← cancel_mono (L.extendXIso e rfl).inv, Category.assoc, this] }
  map_preimage {K L} φ := by
    ext i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simp [HomologicalComplex.extendMap_f _ _ rfl]
    · exact (K.isZero_extend_X _ _ (by tauto)).eq_of_src _ _
  preimage_map {K L} f := by
    ext i
    simp [HomologicalComplex.extendMap_f _ _ rfl]

中文:
定义 fullyFaithfulExtendFunctor
  签名: [有ZeroMorphisms C]
  定义体: { f i := (K.extendXIso e rfl).inv ≫ φ.f (e.f i) ≫ (L.extendXIso e rfl).hom
      comm' i j h := by
        have := φ.comm (e.f i) (e.f j)
        simp only [extendFunctor_obj, K.extend_d_eq e rfl rfl, L.extend_d_eq e rfl rfl] at this
        simp [← cancel_mono (L.extendXIso e rfl).inv, Category.assoc, this] }
  map_preimage {K L} φ := by
    ext i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simp [HomologicalComplex.extendMap_f _ _ rfl]
    · exact (K.isZero_extend_X _ _ (by tauto)).eq_of_src _ _
  preimage_map {K L} f := by
    ext i
    simp [HomologicalComplex.extendMap_f _ _ rfl]

Depends on / 依赖: Category, Category.assoc, HomologicalComplex, HomologicalComplex.extendMap_f, K.extendXIso, K.extend_d_eq, K.isZero_extend_X, L.extendXIso, L.extend_d_eq, cancel_mono, eq_of_src, extendFunctor_obj, extendMap_f, extendXIso, extend_d_eq, isZero_extend_X, map_preimage, preimage_map
-/
noncomputable def fullyFaithfulExtendFunctor [HasZeroMorphisms C] :
    (e.extendFunctor C).FullyFaithful where
  preimage {K L} φ :=
    { f i := (K.extendXIso e rfl).inv ≫ φ.f (e.f i) ≫ (L.extendXIso e rfl).hom
      comm' i j h := by
        have := φ.comm (e.f i) (e.f j)
        simp only [extendFunctor_obj, K.extend_d_eq e rfl rfl, L.extend_d_eq e rfl rfl] at this
        simp [← cancel_mono (L.extendXIso e rfl).inv, Category.assoc, this] }
  map_preimage {K L} φ := by
    ext i'
    by_cases hi' : exists i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simp [HomologicalComplex.extendMap_f _ _ rfl]
    · exact (K.isZero_extend_X _ _ (by tauto)).eq_of_src _ _
  preimage_map {K L} f := by
    ext i
    simp [HomologicalComplex.extendMap_f _ _ rfl]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] : (e.extendFunctor C).Faithful
  body: (e.fullyFaithfulExtendFunctor C).faithful

中文:
实例 [有ZeroMorphisms
  签名: C] : (e.extendFunctor C).忠实
  定义体: (e.fullyFaithfulExtendFunctor C).faithful

Depends on / 依赖: e.fullyFaithfulExtendFunctor, faithful, fullyFaithfulExtendFunctor
-/
instance [HasZeroMorphisms C] : (e.extendFunctor C).Faithful :=
    (e.fullyFaithfulExtendFunctor C).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] : (e.extendFunctor C).Full
  body: (e.fullyFaithfulExtendFunctor C).full

中文:
实例 [有ZeroMorphisms
  签名: C] : (e.extendFunctor C).满
  定义体: (e.fullyFaithfulExtendFunctor C).full

Depends on / 依赖: e.fullyFaithfulExtendFunctor, fullyFaithfulExtendFunctor
-/
instance [HasZeroMorphisms C] : (e.extendFunctor C).Full :=
    (e.fullyFaithfulExtendFunctor C).full

end ComplexShape.Embedding
