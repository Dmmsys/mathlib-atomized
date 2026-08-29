/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Order.SuccPred.Limit

/-!
# Limits of inverse systems indexed by well-ordered types

Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type,
we introduce a structure `F.WellOrderInductionData` which allows
to show that the map `F.sections → F.obj (op ⊥)` is surjective.

The data and properties in `F.WellOrderInductionData` consist of a
section to the maps `F.obj (op (Order.succ j)) → F.obj (op j)` when `j` is not maximal,
and, when `j` is limit, a section to the canonical map from `F.obj (op j)`
to the type of compatible families of elements in `F.obj (op i)` for `i < j`.

In other words, from `val₀ : F.obj (op ⊥)`, a term `d : F.WellOrderInductionData`
allows the construction, by transfinite induction, of a section of `F`
which restricts to `val₀`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite

namespace Functor

variable {J : Type u} [LinearOrder J] [SuccOrder J] (F : Jᵒᵖ ⥤ Type v)

/--
Definition of `WellOrderInductionData` / `WellOrderInductionData` 的定义

English:
structure WellOrderInductionData
  parameters: where
  axioms and operations (4):
    - succ((j : J) (hj : ¬IsMax j) (x : F.obj (op j))) : F.obj (op (Order.succ j))
    - map_succ((j : J) (hj : ¬IsMax j) (x : F.obj (op j))) : F.map (homOfLE (Order.le_succ j)).op (succ j hj x) = x
    - lift((j : J) (hj : Order.IsSuccLimit j) (x : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections)) : F.obj (op j)
    - map_lift((j : J) (hj : Order.IsSuccLimit j) (x : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections) (i : J) (hi : i < j)) : F.map (homOfLE hi.le).op (lift j hj x) = x.val (op ⟨i, hi⟩)

中文:
结构 WellOrderInductionData
  参数: where
  公理与运算 (4 个):
    - succ((j : J) (hj : ¬IsMax j) (x : F.obj (op j))) : F.obj (op (Order.succ j))
    - map_succ((j : J) (hj : ¬IsMax j) (x : F.obj (op j))) : F.map (homOfLE (Order.le_succ j)).op (succ j hj x) = x
    - lift((j : J) (hj : Order.是SuccLimit j) (x : ((序态射.子类型.val (· in 集合.左无界右开区间 j)).monotone.functor.op ⋙ F).sections)) : F.obj (op j)
    - map_lift((j : J) (hj : Order.是SuccLimit j) (x : ((序态射.子类型.val (· in 集合.左无界右开区间 j)).monotone.functor.op ⋙ F).sections) (i : J) (hi : i < j)) : F.map (homOfLE hi.le).op (lift j hj x) = x.val (op ⟨i, hi⟩)
-/
structure WellOrderInductionData where
  /-- A section `F.obj (op j) → F.obj (op (Order.succ j))` to the restriction
  `F.obj (op (Order.succ j)) → F.obj (op j)` when `j` is not maximal. -/
  succ (j : J) (hj : ¬IsMax j) (x : F.obj (op j)) : F.obj (op (Order.succ j))
  map_succ (j : J) (hj : ¬IsMax j) (x : F.obj (op j)) :
      F.map (homOfLE (Order.le_succ j)).op (succ j hj x) = x
  /-- When `j` is a limit element, and `x` is a compatible family of elements
  in `F.obj (op i)` for all `i < j`, this is a lifting to `F.obj (op j)`. -/
  lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections) :
      F.obj (op j)
  map_lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections)
    (i : J) (hi : i < j) :
        F.map (homOfLE hi.le).op (lift j hj x) = x.val (op ⟨i, hi⟩)

namespace WellOrderInductionData

variable {F} in
/--
Definition of `ofExists` / `ofExists` 的定义

English:
definition ofExists
  body: (h₁ j hj x).choose
  map_succ j hj x := (h₁ j hj x).choose_spec
  lift j hj x := (h₂ j hj x).choose
  map_lift j hj x := (h₂ j hj x).choose_spec

中文:
定义 ofExists
  定义体: (h₁ j hj x).choose
  map_succ j hj x := (h₁ j hj x).choose_spec
  lift j hj x := (h₂ j hj x).choose
  map_lift j hj x := (h₂ j hj x).choose_spec
-/
noncomputable def ofExists
    (h₁ : forall (j : J) (_ : ¬IsMax j), Function.Surjective (F.map (homOfLE (Order.le_succ j)).op))
    (h₂ : forall (j : J) (_ : Order.IsSuccLimit j)
      (x : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections),
      exists (y : F.obj (op j)), forall (i : J) (hi : i < j),
        F.map (homOfLE hi.le).op y = x.val (op ⟨i, hi⟩)) :
    F.WellOrderInductionData where
  succ j hj x := (h₁ j hj x).choose
  map_succ j hj x := (h₁ j hj x).choose_spec
  lift j hj x := (h₂ j hj x).choose
  map_lift j hj x := (h₂ j hj x).choose_spec

variable {F} (d : F.WellOrderInductionData) [OrderBot J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Extension` / `Extension` 的定义

English:
structure Extension
  parameters: (val₀ : F.obj (op ⊥)) (j : J)
  axioms and operations (4):
    - val : F.obj (op j)
    - map_zero : F.map (homOfLE bot_le).op val = val₀
    - map_succ((i : J) (hi : i < j)) : F.map (homOfLE (Order.succ_le_of_lt hi)).op val = d.succ i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val)
    - map_limit((i : J) (hi : Order.IsSuccLimit i) (hij : i <= j)) : F.map (homOfLE hij).op val = d.lift i hi { val := fun ⟨⟨k, hk⟩⟩ => F.map (homOfLE (hk.le.trans hij)).op val property := fun f => by dsimp rw [← comp_apply]; rw [← map_comp] rfl }

中文:
结构 扩张
  参数: (val₀ : F.obj (op ⊥)) (j : J)
  公理与运算 (4 个):
    - val : F.obj (op j)
    - map_zero : F.map (homOfLE bot_le).op val = val₀
    - map_succ((i : J) (hi : i < j)) : F.map (homOfLE (Order.succ_le_of_lt hi)).op val = d.succ i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val)
    - map_limit((i : J) (hi : Order.是SuccLimit i) (hij : i <= j)) : F.map (homOfLE hij).op val = d.lift i hi { val := fun ⟨⟨k, hk⟩⟩ => F.map (homOfLE (hk.le.trans hij)).op val property := fun f => by dsimp rw [← comp_apply]; rw [← map_comp] rfl }

Depends on / 依赖: F.map, hk.le.trans, homOfLE
-/
structure Extension (val₀ : F.obj (op ⊥)) (j : J) where
  /-- An element in `F.obj (op j)`, which, by restriction, induces elements
  in `F.obj (op i)` for all `i ≤ j`. -/
  val : F.obj (op j)
  map_zero : F.map (homOfLE bot_le).op val = val₀
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (Order.succ_le_of_lt hi)).op val =
      d.succ i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val)
  map_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i <= j) :
    F.map (homOfLE hij).op val = d.lift i hi
      { val := fun ⟨⟨k, hk⟩⟩ => F.map (homOfLE (hk.le.trans hij)).op val
        property := fun f => by
          dsimp
          rw [← comp_apply]; rw [← map_comp]
          rfl }

namespace Extension

variable {d} {val₀ : F.obj (op ⊥)}

/-- An element in `d.Extension val₀ j` induces an element in `d.Extension val₀ i` when `i ≤ j`. -/
@[simps]
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: {j : J} (e : d.Extension val₀ j) {i : J} (hij : i <= j)
  body: F.map (homOfLE hij).op e.val
  map_zero := by
    rw [← comp_apply]; rw [← map_comp]
    exact e.map_zero
  map_succ k hk := by
    rw [← comp_apply]; rw [← map_comp]; rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [← op_comp]; rw [homOfLE_comp]; rw [homOfLE_comp]; rw [e.map_succ k (lt_of_lt_of_le hk hij)]
  map_limit k hk hki := by
    rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [homOfLE_comp]; rw [e.map_limit k hk (hki.trans hij)]
    congr
    ext ⟨l, hl⟩
    dsimp
    rw [← comp_apply]; rw [← map_comp]
    rfl

中文:
定义 ofLE
  签名: {j : J} (e : d.扩张 val₀ j) {i : J} (hij : i <= j)
  定义体: F.map (homOfLE hij).op e.val
  map_zero := by
    rw [← comp_apply]; rw [← map_comp]
    exact e.map_zero
  map_succ k hk := by
    rw [← comp_apply]; rw [← map_comp]; rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [← op_comp]; rw [homOfLE_comp]; rw [homOfLE_comp]; rw [e.map_succ k (lt_of_lt_of_le hk hij)]
  map_limit k hk hki := by
    rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [homOfLE_comp]; rw [e.map_limit k hk (hki.trans hij)]
    congr
    ext ⟨l, hl⟩
    dsimp
    rw [← comp_apply]; rw [← map_comp]
    rfl

Depends on / 依赖: F.map, e.val, homOfLE
-/
def ofLE {j : J} (e : d.Extension val₀ j) {i : J} (hij : i <= j) : d.Extension val₀ i where
  val := F.map (homOfLE hij).op e.val
  map_zero := by
    rw [← comp_apply]; rw [← map_comp]
    exact e.map_zero
  map_succ k hk := by
    rw [← comp_apply]; rw [← map_comp]; rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [← op_comp]; rw [homOfLE_comp]; rw [homOfLE_comp]; rw [e.map_succ k (lt_of_lt_of_le hk hij)]
  map_limit k hk hki := by
    rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [homOfLE_comp]; rw [e.map_limit k hk (hki.trans hij)]
    congr
    ext ⟨l, hl⟩
    dsimp
    rw [← comp_apply]; rw [← map_comp]
    rfl

/--
lemma `val_injective` / 引理 `val_injective`

English:
lemma val_injective
  given: {j : J} {e e' : d.Extension val₀ j} (h : e.val = e'.val)
  statement: e = e'
  proof: by
  cases e
  cases e'
  subst h
  rfl

中文:
引理 val_injective
  条件: {j : J} {e e' : d.扩张 val₀ j} (h : e.val = e'.val)
  结论: e = e'
  证明: by
  cases e
  cases e'
  subst h
  rfl
-/
lemma val_injective {j : J} {e e' : d.Extension val₀ j} (h : e.val = e'.val) : e = e' := by
  cases e
  cases e'
  subst h
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedLT
  signature: J] (j
  body: by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    simp only [homOfLE_refl, op_id, map_id, id_apply] at h₁ h₂
    rw [h₁]; rw [h₂]
  | succ i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_succ i (Order.lt_succ_of_not_isMax hi)
    have h₂ := e₂.map_succ i (Order.lt_succ_of_not_isMax hi)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁]; rw [h₂]
    congr 1
    exact congrArg val (Subsingleton.elim (e₁.ofLE (Order.le_succ i)) (e₂.ofLE (Order.le_succ i)))
  | isSuccLimit i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_limit i hi (by rfl)
    have h₂ := e₂.map_limit i hi (by rfl)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁]; rw [h₂]
    congr
    ext ⟨⟨l, hl⟩⟩
    have := hi' l hl
    exact congr_arg val (Subsingleton.elim (e₁.ofLE hl.le) (e₂.ofLE hl.le))

中文:
实例 [WellFoundedLT
  签名: J] (j
  定义体: by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    simp only [homOfLE_refl, op_id, map_id, id_apply] at h₁ h₂
    rw [h₁]; rw [h₂]
  | succ i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_succ i (Order.lt_succ_of_not_isMax hi)
    have h₂ := e₂.map_succ i (Order.lt_succ_of_not_isMax hi)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁]; rw [h₂]
    congr 1
    exact congrArg val (Subsingleton.elim (e₁.ofLE (Order.le_succ i)) (e₂.ofLE (Order.le_succ i)))
  | isSuccLimit i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_limit i hi (by rfl)
    have h₂ := e₂.map_limit i hi (by rfl)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁]; rw [h₂]
    congr
    ext ⟨⟨l, hl⟩⟩
    have := hi' l hl
    exact congr_arg val (Subsingleton.elim (e₁.ofLE hl.le) (e₂.ofLE hl.le))

Depends on / 依赖: Order.lt_succ_of_not_isMax, Subsingleton, Subsingleton.intro, SuccOrder, SuccOrder.limitRecOn, homOfLE_refl, id_apply, limitRecOn, lt_succ_of_not_isMax, map_id, map_succ, map_zero, op_id, val_injective
-/
instance [WellFoundedLT J] (j : J) : Subsingleton (d.Extension val₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    simp only [homOfLE_refl, op_id, map_id, id_apply] at h₁ h₂
    rw [h₁]; rw [h₂]
  | succ i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_succ i (Order.lt_succ_of_not_isMax hi)
    have h₂ := e₂.map_succ i (Order.lt_succ_of_not_isMax hi)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁]; rw [h₂]
    congr 1
    exact congrArg val (Subsingleton.elim (e₁.ofLE (Order.le_succ i)) (e₂.ofLE (Order.le_succ i)))
  | isSuccLimit i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ => val_injective ?_)
    have h₁ := e₁.map_limit i hi (by rfl)
    have h₂ := e₂.map_limit i hi (by rfl)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁]; rw [h₂]
    congr
    ext ⟨⟨l, hl⟩⟩
    have := hi' l hl
    exact congr_arg val (Subsingleton.elim (e₁.ofLE hl.le) (e₂.ofLE hl.le))

/--
lemma `compatibility` / 引理 `compatibility`

English:
lemma compatibility
  statement: [WellFoundedLT J]
  proof: by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

中文:
引理 compatibility
  结论: [WellFoundedLT J]
  证明: by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

Depends on / 依赖: Subsingleton, Subsingleton.elim, e.ofLE
-/
lemma compatibility [WellFoundedLT J]
    {j : J} (e : d.Extension val₀ j) {i : J} (e' : d.Extension val₀ i) (h : i <= j) :
    F.map (homOfLE h).op e.val = e'.val := by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

variable (d val₀) in
/-- The obvious element in `d.Extension val₀ ⊥`. -/
@[simps]
/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : d.Extension val₀ ⊥ where
  body: val₀
  map_zero := by simp
  map_succ i hi := by simp at hi
  map_limit i hi hij := by
    obtain rfl : i = ⊥ := by simpa using hij
    simpa using hi.not_isMin

中文:
定义 zero
  签名: : d.扩张 val₀ ⊥ where
  定义体: val₀
  map_zero := by simp
  map_succ i hi := by simp at hi
  map_limit i hi hij := by
    obtain rfl : i = ⊥ := by simpa using hij
    simpa using hi.not_isMin
-/
def zero : d.Extension val₀ ⊥ where
  val := val₀
  map_zero := by simp
  map_succ i hi := by simp at hi
  map_limit i hi hij := by
    obtain rfl : i = ⊥ := by simpa using hij
    simpa using hi.not_isMin

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: {j : J} (e : d.Extension val₀ j) (hj : ¬IsMax j)
  body: d.succ j hj e.val
  map_zero := by
    simp only [← e.map_zero]
    conv_rhs => rw [← d.map_succ j hj e.val]
    rw [← comp_apply]; rw [← map_comp]
    rfl
  map_succ i hi := by
    obtain hij | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · rw [← homOfLE_comp ((Order.lt_succ_iff_of_not_isMax hj).mp hi) (Order.le_succ j), op_comp,
        map_comp, comp_apply, d.map_succ, ← e.map_succ i hij,
        ← homOfLE_comp (Order.succ_le_of_lt hij) (Order.le_succ j), op_comp,
        map_comp, comp_apply, d.map_succ]
    · simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom, d.map_succ]
  map_limit i hi hij := by
    obtain hij | rfl := hij.lt_or_eq
    · have hij' : i <= j := (Order.lt_succ_iff_of_not_isMax hj).mp hij
      have := congr_arg (F.map (homOfLE hij').op) (d.map_succ j hj e.val)
      rw [e.map_limit i hi]; rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [homOfLE_comp] at this
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      dsimp
      conv_lhs => rw [← d.map_succ j hj e.val]
      rw [← comp_apply]; rw [← map_comp]
      rfl
    · exfalso
      exact hj hi.isMax

中文:
定义 succ
  签名: {j : J} (e : d.扩张 val₀ j) (hj : ¬IsMax j)
  定义体: d.succ j hj e.val
  map_zero := by
    simp only [← e.map_zero]
    conv_rhs => rw [← d.map_succ j hj e.val]
    rw [← comp_apply]; rw [← map_comp]
    rfl
  map_succ i hi := by
    obtain hij | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · rw [← homOfLE_comp ((Order.lt_succ_iff_of_not_isMax hj).mp hi) (Order.le_succ j), op_comp,
        map_comp, comp_apply, d.map_succ, ← e.map_succ i hij,
        ← homOfLE_comp (Order.succ_le_of_lt hij) (Order.le_succ j), op_comp,
        map_comp, comp_apply, d.map_succ]
    · simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom, d.map_succ]
  map_limit i hi hij := by
    obtain hij | rfl := hij.lt_or_eq
    · have hij' : i <= j := (Order.lt_succ_iff_of_not_isMax hj).mp hij
      have := congr_arg (F.map (homOfLE hij').op) (d.map_succ j hj e.val)
      rw [e.map_limit i hi]; rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [homOfLE_comp] at this
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      dsimp
      conv_lhs => rw [← d.map_succ j hj e.val]
      rw [← comp_apply]; rw [← map_comp]
      rfl
    · exfalso
      exact hj hi.isMax

Depends on / 依赖: d.succ, e.val
-/
def succ {j : J} (e : d.Extension val₀ j) (hj : ¬IsMax j) :
    d.Extension val₀ (Order.succ j) where
  val := d.succ j hj e.val
  map_zero := by
    simp only [← e.map_zero]
    conv_rhs => rw [← d.map_succ j hj e.val]
    rw [← comp_apply]; rw [← map_comp]
    rfl
  map_succ i hi := by
    obtain hij | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · rw [← homOfLE_comp ((Order.lt_succ_iff_of_not_isMax hj).mp hi) (Order.le_succ j), op_comp,
        map_comp, comp_apply, d.map_succ, ← e.map_succ i hij,
        ← homOfLE_comp (Order.succ_le_of_lt hij) (Order.le_succ j), op_comp,
        map_comp, comp_apply, d.map_succ]
    · simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom, d.map_succ]
  map_limit i hi hij := by
    obtain hij | rfl := hij.lt_or_eq
    · have hij' : i <= j := (Order.lt_succ_iff_of_not_isMax hj).mp hij
      have := congr_arg (F.map (homOfLE hij').op) (d.map_succ j hj e.val)
      rw [e.map_limit i hi]; rw [← comp_apply]; rw [← map_comp]; rw [← op_comp]; rw [homOfLE_comp] at this
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      dsimp
      conv_lhs => rw [← d.map_succ j hj e.val]
      rw [← comp_apply]; rw [← map_comp]
      rfl
    · exfalso
      exact hj hi.isMax

variable [WellFoundedLT J]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `limit` / `limit` 的定义

English:
definition limit
  signature: (j : J) (hj : Order.IsSuccLimit j)
  body: d.lift j hj
    { val := fun ⟨i, hi⟩ => (e i hi).val
      property := fun f => by dsimp; apply compatibility }
  map_zero := by
    rw [d.map_lift _ _ _ _ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)]
    simpa using (e ⊥ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)).map_zero
  map_succ i hi := by
    convert!
      (e (Order.succ i) ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)).map_succ i
        (by
          simp only [Order.lt_succ_iff_not_isMax, not_isMax_iff]
          exact ⟨_, hi⟩) using 1
    · dsimp
      rw [map_id]; rw [id_apply]; rw [d.map_lift _ _ _ _ ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)]
    · congr 1
      rw [d.map_lift _ _ _ _ hi]
      symm
      apply compatibility
  map_limit i hi hij := by
    obtain hij' | rfl := hij.lt_or_eq
    · have := (e i hij').map_limit i hi (by rfl)
      dsimp at this ⊢
      rw [map_id]; rw [id_apply] at this
      rw [d.map_lift _ _ _ _ hij']
      dsimp
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [map_lift _ _ _ _ _ (hl.trans hij')]
      apply compatibility
    · dsimp
      rw [map_id]; rw [id_apply]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [d.map_lift _ _ _ _ hl]

中文:
定义 limit
  签名: (j : J) (hj : Order.是SuccLimit j)
  定义体: d.lift j hj
    { val := fun ⟨i, hi⟩ => (e i hi).val
      property := fun f => by dsimp; apply compatibility }
  map_zero := by
    rw [d.map_lift _ _ _ _ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)]
    simpa using (e ⊥ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)).map_zero
  map_succ i hi := by
    convert!
      (e (Order.succ i) ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)).map_succ i
        (by
          simp only [Order.lt_succ_iff_not_isMax, not_isMax_iff]
          exact ⟨_, hi⟩) using 1
    · dsimp
      rw [map_id]; rw [id_apply]; rw [d.map_lift _ _ _ _ ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)]
    · congr 1
      rw [d.map_lift _ _ _ _ hi]
      symm
      apply compatibility
  map_limit i hi hij := by
    obtain hij' | rfl := hij.lt_or_eq
    · have := (e i hij').map_limit i hi (by rfl)
      dsimp at this ⊢
      rw [map_id]; rw [id_apply] at this
      rw [d.map_lift _ _ _ _ hij']
      dsimp
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [map_lift _ _ _ _ _ (hl.trans hij')]
      apply compatibility
    · dsimp
      rw [map_id]; rw [id_apply]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [d.map_lift _ _ _ _ hl]

Depends on / 依赖: d.lift
-/
def limit (j : J) (hj : Order.IsSuccLimit j)
    (e : forall (i : J) (_ : i < j), d.Extension val₀ i) :
    d.Extension val₀ j where
  val := d.lift j hj
    { val := fun ⟨i, hi⟩ => (e i hi).val
      property := fun f => by dsimp; apply compatibility }
  map_zero := by
    rw [d.map_lift _ _ _ _ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)]
    simpa using (e ⊥ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)).map_zero
  map_succ i hi := by
    convert!
      (e (Order.succ i) ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)).map_succ i
        (by
          simp only [Order.lt_succ_iff_not_isMax, not_isMax_iff]
          exact ⟨_, hi⟩) using 1
    · dsimp
      rw [map_id]; rw [id_apply]; rw [d.map_lift _ _ _ _ ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)]
    · congr 1
      rw [d.map_lift _ _ _ _ hi]
      symm
      apply compatibility
  map_limit i hi hij := by
    obtain hij' | rfl := hij.lt_or_eq
    · have := (e i hij').map_limit i hi (by rfl)
      dsimp at this ⊢
      rw [map_id]; rw [id_apply] at this
      rw [d.map_lift _ _ _ _ hij']
      dsimp
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [map_lift _ _ _ _ _ (hl.trans hij')]
      apply compatibility
    · dsimp
      rw [map_id]; rw [id_apply]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [d.map_lift _ _ _ _ hl]

instance (j : J) : Nonempty (d.Extension val₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    exact ⟨zero d val₀⟩
  | succ i hi hi' => exact ⟨hi'.some.succ hi⟩
  | isSuccLimit i hi hi' => exact ⟨limit i hi (fun l hl => (hi' l hl).some)⟩

noncomputable instance (j : J) : Unique (d.Extension val₀ j) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

end Extension

variable [WellFoundedLT J]

/--
Definition of `sectionsMk` / `sectionsMk` 的定义

English:
definition sectionsMk
  signature: (val₀ : F.obj (op ⊥))
  body: (default : d.Extension val₀ j.unop).val
  property := fun f => by apply Extension.compatibility

中文:
定义 sectionsMk
  签名: (val₀ : F.obj (op ⊥))
  定义体: (default : d.Extension val₀ j.unop).val
  property := fun f => by apply Extension.compatibility

Depends on / 依赖: Extension, d.Extension, j.unop
-/
noncomputable def sectionsMk (val₀ : F.obj (op ⊥)) : F.sections where
  val j := (default : d.Extension val₀ j.unop).val
  property := fun f => by apply Extension.compatibility

/--
lemma `sectionsMk_val_op_bot` / 引理 `sectionsMk_val_op_bot`

English:
lemma sectionsMk_val_op_bot
  given: (val₀ : F.obj (op ⊥))
  proof: by
  simpa using! (default : d.Extension val₀ ⊥).map_zero

include d in

中文:
引理 sectionsMk_val_op_bot
  条件: (val₀ : F.obj (op ⊥))
  证明: by
  simpa using! (default : d.Extension val₀ ⊥).map_zero

include d in

Depends on / 依赖: Extension, d.Extension, map_zero
-/
lemma sectionsMk_val_op_bot (val₀ : F.obj (op ⊥)) :
    (d.sectionsMk val₀).val (op ⊥) = val₀ := by
  simpa using! (default : d.Extension val₀ ⊥).map_zero

include d in
/--
lemma `surjective` / 引理 `surjective`

English:
lemma surjective
  proof: fun val₀ => ⟨d.sectionsMk val₀, d.sectionsMk_val_op_bot val₀⟩

中文:
引理 surjective
  证明: fun val₀ => ⟨d.sectionsMk val₀, d.sectionsMk_val_op_bot val₀⟩

Depends on / 依赖: d.sectionsMk, d.sectionsMk_val_op_bot, sectionsMk, sectionsMk_val_op_bot
-/
lemma surjective :
    Function.Surjective ((fun s => s (op ⊥)) ∘ Subtype.val : F.sections -> F.obj (op ⊥)) :=
  fun val₀ => ⟨d.sectionsMk val₀, d.sectionsMk_val_op_bot val₀⟩

end WellOrderInductionData

end Functor

end CategoryTheory
