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

/-- Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type, this data
allows to construct a section of `F` from an element in `F.obj (op ⊥)`,
see `WellOrderInductionData.sectionsMk`. -/
/-
**CategoryTheory.Functor.WellOrderInductionData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{J : Type u} → [inst : LinearOrder J] → [SuccOrder J] → CategoryTheory.Fun
ctor Jᵒᵖ (Type v) → Type (max u v)
参数：Type v；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type, this data
allows to construct a section of `F` from an element in `F.obj (op ⊥)`,
see `WellOrderInductionData.sectionsMk`.
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
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections) :
      F.obj (op j)
  map_lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections)
    (i : J) (hi : i < j) :
        F.map (homOfLE hi.le).op (lift j hj x) = x.val (op ⟨i, hi⟩)

namespace WellOrderInductionData

variable {F} in
/-- Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type,
this is a constructor for `F.WellOrderInductionData` which does not take
data as inputs but proofs of the existence of certain elements. -/
/-
**CategoryTheory.Functor.WellOrderInductionData.ofExists** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.WellOrderInductionData`。
形式化陈述：ofExists (h₁ : forall (j : J) (_ : ¬IsMax j), Function.Surjective (F.map (
homOfLE (Order.le_succ j)).op)) (h₂ : forall (j : J) (_ : Order.IsSuccLimit j) (
x : ((OrderHom.Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections),
 exists (y : F.obj (op j)), forall (i : J) (hi : i < j), F.map (homOfLE hi.le).o
p y = x.val (op ⟨i, hi⟩)) : F.WellOrderInductionData where succ j hj x
参数：h₁ : forall (j : J) (_ : ¬IsMax j), Function.Surjective (F.map (homOfLE (Orde
r.le_succ j)).op)；h₂ : forall (j : J) (_ : Order.IsSuccLimit j) (x : ((OrderHom.
Subtype.val (· in Set.Iio j)).monotone.functor.op ⋙ F).sections), exists (y : F.
obj (op j)), forall (i : J) (hi : i < j), F.map (homOfLE hi.le).op y = x.val (op
 ⟨i, hi⟩)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type,
this is a constructor for `F.WellOrderInductionData` which does not take
data as inputs but proofs of the existence of certain elements.
-/
noncomputable def ofExists
    (h₁ : ∀ (j : J) (_ : ¬IsMax j), Function.Surjective (F.map (homOfLE (Order.le_succ j)).op))
    (h₂ : ∀ (j : J) (_ : Order.IsSuccLimit j)
      (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections),
      ∃ (y : F.obj (op j)), ∀ (i : J) (hi : i < j),
        F.map (homOfLE hi.le).op y = x.val (op ⟨i, hi⟩)) :
    F.WellOrderInductionData where
  succ j hj x := (h₁ j hj x).choose
  map_succ j hj x := (h₁ j hj x).choose_spec
  lift j hj x := (h₂ j hj x).choose
  map_lift j hj x := (h₂ j hj x).choose_spec

variable {F} (d : F.WellOrderInductionData) [OrderBot J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `d : F.WellOrderInductionData`, `val₀ : F.obj (op ⊥)` and `j : J`,
this is the data of an element `val : F.obj (op j)` such that the induced
compatible family of elements in all `F.obj (op i)` for `i ≤ j`
is determined by `val₀` and the choice of "liftings" given by `d`. -/
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension** 是 Mathlib 中的一个结构，位于命
名空间 `CategoryTheory.Functor.WellOrderInductionData`。
形式化陈述：Extension (val₀ : F.obj (op ⊥)) (j : J) where /-- An element in `F.obj (op
 j)`, which, by restriction, induces elements in `F.obj (op i)` for all `i ≤ j`.
 -/ val : F.obj (op j) map_zero : F.map (homOfLE bot_le).op val = val₀ map_succ 
(i : J) (hi : i < j) : F.map (homOfLE (Order.succ_le_of_lt hi)).op val = d.succ 
i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val) map_limit (i : J) (hi
 : Order.IsSuccLimit i) (hij : i <= j) : F.map (homOfLE hij).op val = d.lift i h
i { val
参数：val₀ : F.obj (op ⊥)；j : J；op j；op i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `d : F.WellOrderInductionData`, `val₀ : F.obj (op ⊥)` and `j : J`,
this is the data of an element `val : F.obj (op j)` such that the induced
compatible family of elements in all `F.obj (op i)` for `i ≤ j`
is determined by `val₀` and the choice of "liftings" given by `d`.
-/
structure Extension (val₀ : F.obj (op ⊥)) (j : J) where
  /-- An element in `F.obj (op j)`, which, by restriction, induces elements
  in `F.obj (op i)` for all `i ≤ j`. -/
  val : F.obj (op j)
  map_zero : F.map (homOfLE bot_le).op val = val₀
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (Order.succ_le_of_lt hi)).op val =
      d.succ i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val)
  map_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    F.map (homOfLE hij).op val = d.lift i hi
      { val := fun ⟨⟨k, hk⟩⟩ ↦ F.map (homOfLE (hk.le.trans hij)).op val
        property := fun f ↦ by
          dsimp
          rw [← comp_apply, ← map_comp]
          rfl }

namespace Extension

variable {d} {val₀ : F.obj (op ⊥)}

/-- An element in `d.Extension val₀ j` induces an element in `d.Extension val₀ i` when `i ≤ j`. -/
@[simps]
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.ofLE** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
形式化陈述：ofLE {j : J} (e : d.Extension val₀ j) {i : J} (hij : i <= j) : d.Extension
 val₀ i where val
参数：e : d.Extension val₀ j；hij : i <= j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element in `d.Extension val₀ j` induces an element in `d.Extension val₀ i` wh
en `i ≤ j`.
-/
def ofLE {j : J} (e : d.Extension val₀ j) {i : J} (hij : i ≤ j) : d.Extension val₀ i where
  val := F.map (homOfLE hij).op e.val
  map_zero := by
    rw [← comp_apply, ← map_comp]
    exact e.map_zero
  map_succ k hk := by
    rw [← comp_apply, ← map_comp, ← comp_apply, ← map_comp, ← op_comp, ← op_comp,
      homOfLE_comp, homOfLE_comp, e.map_succ k (lt_of_lt_of_le hk hij)]
  map_limit k hk hki := by
    rw [← comp_apply, ← map_comp, ← op_comp, homOfLE_comp,
      e.map_limit k hk (hki.trans hij)]
    congr
    ext ⟨l, hl⟩
    dsimp
    rw [← comp_apply, ← map_comp]
    rfl
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.val_injective** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
形式化陈述：val_injective {j : J} {e e' : d.Extension val₀ j} (h : e.val = e'.val) : e
 = e'
参数：h : e.val = e'.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma val_injective {j : J} {e e' : d.Extension val₀ j} (h : e.val = e'.val) : e = e' := by
  cases e
  cases e'
  subst h
  rfl
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedLT J] (j : J) : Subsingleton (d.Extension val₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    refine Subsingleton.intro (fun e₁ e₂ ↦ val_injective ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    simp only [homOfLE_refl, op_id, map_id, id_apply] at h₁ h₂
    rw [h₁, h₂]
  | succ i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ ↦ val_injective ?_)
    have h₁ := e₁.map_succ i (Order.lt_succ_of_not_isMax hi)
    have h₂ := e₂.map_succ i (Order.lt_succ_of_not_isMax hi)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁, h₂]
    congr 1
    exact congrArg val (Subsingleton.elim (e₁.ofLE (Order.le_succ i)) (e₂.ofLE (Order.le_succ i)))
  | isSuccLimit i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ ↦ val_injective ?_)
    have h₁ := e₁.map_limit i hi (by rfl)
    have h₂ := e₂.map_limit i hi (by rfl)
    simp only [homOfLE_refl, op_id, map_id, id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁, h₂]
    congr
    ext ⟨⟨l, hl⟩⟩
    have := hi' l hl
    exact congr_arg val (Subsingleton.elim (e₁.ofLE hl.le) (e₂.ofLE hl.le))
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.compatibility** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
形式化陈述：compatibility [WellFoundedLT J] {j : J} (e : d.Extension val₀ j) {i : J} (
e' : d.Extension val₀ i) (h : i <= j) : F.map (homOfLE h).op e.val = e'.val
参数：e : d.Extension val₀ j；e' : d.Extension val₀ i；h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.WellOrderInductionData.Extension.instSubsingleton
OfWellFoundedLT`：∀ {J : Type u} [inst : LinearOrder J] [inst_1 : SuccOrder J] {F
 : CategoryTheory.Functor Jᵒᵖ (Type v)}   {d : F.WellOrderInductionData} [ins…
-/
lemma compatibility [WellFoundedLT J]
    {j : J} (e : d.Extension val₀ j) {i : J} (e' : d.Extension val₀ i) (h : i ≤ j) :
    F.map (homOfLE h).op e.val = e'.val := by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

variable (d val₀) in
/-- The obvious element in `d.Extension val₀ ⊥`. -/
@[simps]
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.zero** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
形式化陈述：zero : d.Extension val₀ ⊥ where val
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious element in `d.Extension val₀ ⊥`.
-/
def zero : d.Extension val₀ ⊥ where
  val := val₀
  map_zero := by simp
  map_succ i hi := by simp at hi
  map_limit i hi hij := by
    obtain rfl : i = ⊥ := by simpa using hij
    simpa using hi.not_isMin

/-- The element in `d.Extension val₀ (Order.succ j)` obtained by extending
an element in `d.Extension val₀ j` when `j` is not maximal. -/
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.succ** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
形式化陈述：succ {j : J} (e : d.Extension val₀ j) (hj : ¬IsMax j) : d.Extension val₀ (
Order.succ j) where val
参数：e : d.Extension val₀ j；hj : ¬IsMax j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element in `d.Extension val₀ (Order.succ j)` obtained by extending
an element in `d.Extension val₀ j` when `j` is not maximal.
-/
def succ {j : J} (e : d.Extension val₀ j) (hj : ¬IsMax j) :
    d.Extension val₀ (Order.succ j) where
  val := d.succ j hj e.val
  map_zero := by
    simp only [← e.map_zero]
    conv_rhs => rw [← d.map_succ j hj e.val]
    rw [← comp_apply, ← map_comp]
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
    · have hij' : i ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp hij
      have := congr_arg (F.map (homOfLE hij').op) (d.map_succ j hj e.val)
      rw [e.map_limit i hi, ← comp_apply, ← map_comp, ← op_comp, homOfLE_comp] at this
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      dsimp
      conv_lhs => rw [← d.map_succ j hj e.val]
      rw [← comp_apply, ← map_comp]
      rfl
    · exfalso
      exact hj hi.isMax

variable [WellFoundedLT J]

set_option backward.isDefEq.respectTransparency.types false in
/-- When `j` is a limit element, this is the extension to `d.Extension val₀ j`
of a family of elements in `d.Extension val₀ i` for all `i < j`. -/
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.limit** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
形式化陈述：limit (j : J) (hj : Order.IsSuccLimit j) (e : forall (i : J) (_ : i < j), 
d.Extension val₀ i) : d.Extension val₀ j where val
参数：j : J；hj : Order.IsSuccLimit j；e : forall (i : J) (_ : i < j), d.Extension va
l₀ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `j` is a limit element, this is the extension to `d.Extension val₀ j`
of a family of elements in `d.Extension val₀ i` for all `i < j`.
-/
def limit (j : J) (hj : Order.IsSuccLimit j)
    (e : ∀ (i : J) (_ : i < j), d.Extension val₀ i) :
    d.Extension val₀ j where
  val := d.lift j hj
    { val := fun ⟨i, hi⟩ ↦ (e i hi).val
      property := fun f ↦ by dsimp; apply compatibility }
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
      rw [map_id, id_apply, d.map_lift _ _ _ _ ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)]
    · congr 1
      rw [d.map_lift _ _ _ _ hi]
      symm
      apply compatibility
  map_limit i hi hij := by
    obtain hij' | rfl := hij.lt_or_eq
    · have := (e i hij').map_limit i hi (by rfl)
      dsimp at this ⊢
      rw [map_id, id_apply] at this
      rw [d.map_lift _ _ _ _ hij']
      dsimp
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [map_lift _ _ _ _ _ (hl.trans hij')]
      apply compatibility
    · dsimp
      rw [map_id, id_apply]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [d.map_lift _ _ _ _ hl]
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : J) : Nonempty (d.Extension val₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    exact ⟨zero d val₀⟩
  | succ i hi hi' => exact ⟨hi'.some.succ hi⟩
  | isSuccLimit i hi hi' => exact ⟨limit i hi (fun l hl ↦ (hi' l hl).some)⟩
/-
**CategoryTheory.Functor.WellOrderInductionData.Extension.** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Functor.WellOrderInductionData.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (j : J) : Unique (d.Extension val₀ j) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

end Extension

variable [WellFoundedLT J]

/-- When `J` is a well-ordered type, `F : Jᵒᵖ ⥤ Type v`, and `d : F.WellOrderInductionData`,
this is the section of `F` that is determined by `val₀ : F.obj (op ⊥)` -/
/-
**CategoryTheory.Functor.WellOrderInductionData.sectionsMk** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Functor.WellOrderInductionData`。
形式化陈述：sectionsMk (val₀ : F.obj (op ⊥)) : F.sections where val j
参数：val₀ : F.obj (op ⊥)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `J` is a well-ordered type, `F : Jᵒᵖ ⥤ Type v`, and `d : F.WellOrderInducti
onData`,
this is the section of `F` that is determined by `val₀ : F.obj (op ⊥)`
-/
noncomputable def sectionsMk (val₀ : F.obj (op ⊥)) : F.sections where
  val j := (default : d.Extension val₀ j.unop).val
  property := fun f ↦ by apply Extension.compatibility
/-
**CategoryTheory.Functor.WellOrderInductionData.sectionsMk_val_op_bot** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Functor.WellOrderInductionData`。
形式化陈述：sectionsMk_val_op_bot (val₀ : F.obj (op ⊥)) : (d.sectionsMk val₀).val (op 
⊥) = val₀
参数：val₀ : F.obj (op ⊥)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.WellOrderInductionData.Extension.map_zero`：∀ {J :
 Type u} [inst : LinearOrder J] [inst_1 : SuccOrder J] {F : CategoryTheory.Funct
or Jᵒᵖ (Type v)}   {d : F.WellOrderInductionData} [ins…
-/
lemma sectionsMk_val_op_bot (val₀ : F.obj (op ⊥)) :
    (d.sectionsMk val₀).val (op ⊥) = val₀ := by
  simpa using! (default : d.Extension val₀ ⊥).map_zero

include d in
/-
**CategoryTheory.Functor.WellOrderInductionData.surjective** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor.WellOrderInductionData`。
形式化陈述：surjective : Function.Surjective ((fun s => s (op ⊥)) ∘ Subtype.val : F.se
ctions -> F.obj (op ⊥))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.WellOrderInductionData.sectionsMk_val_op_bot`：sec
tionsMk_val_op_bot (val₀ : F.obj (op ⊥)) : (d.sectionsMk val₀).val (op ⊥) = val₀
-/
lemma surjective :
    Function.Surjective ((fun s ↦ s (op ⊥)) ∘ Subtype.val : F.sections → F.obj (op ⊥)) :=
  fun val₀ ↦ ⟨d.sectionsMk val₀, d.sectionsMk_val_op_bot val₀⟩

end WellOrderInductionData

end Functor

end CategoryTheory

