/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Equalizers in Type

The equalizer of a pair of maps `(g, h)` from `X` to `Y` is the subtype `{x : Y // g x = h x}`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
/-
**CategoryTheory.Limits.Types.typeEqualizerOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Types`。
形式化陈述：typeEqualizerOfUnique (t : forall y : Y, g y = h y -> exists! x : X, f x =
 y) : IsLimit (Fork.ofι _ w)
参数：t : forall y : Y, g y = h y -> exists! x : X, f x = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show the given fork in `Type u` is an equalizer given that any element in the "d
ifference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine ⟨↾fun i => ?_, ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_hom s.condition i
    · ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).1
    · intro m hm
      ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).2 _ (congr_hom hm i)

/-- The converse of `type_equalizer_of_unique`. -/
/-
**CategoryTheory.Limits.Types.unique_of_type_equalizer** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.Types`。
形式化陈述：unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = 
h y) : exists! x : X, f x = y
参数：t : IsLimit (Fork.ofι _ w)；y : Y；hy : g y = h y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The converse of `type_equalizer_of_unique`.
-/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := ↾fun _ => y
  have hy' : y' ≫ g = y' ≫ h := by ext; exact hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_hom (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply TypeCat.homEquiv.symm.injective
  apply Fork.IsLimit.hom_ext t
  ext ⟨⟩
  apply hx'.trans (congr_hom (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm
/-
**CategoryTheory.Limits.Types.type_equalizer_iff_unique** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.Types`。
形式化陈述：type_equalizer_iff_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y :
 Y, g y = h y -> exists! x : X, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.unique_of_type_equalizer`：unique_of_type_equ
alizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) : exists! x : X, f 
x = y
-/
theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
/-
**CategoryTheory.Limits.Types.equalizerLimit** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Types`。
形式化陈述：equalizerLimit : Limits.LimitCone (parallelPair g h) where cone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)
`.
-/
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (↾(Subtype.val : { x : Y // g x = h x } → Y))
    (by ext x; exact x.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨↾fun i => ⟨s.ι i, by apply congr_hom s.condition i⟩, rfl, fun hm =>
        by ext x; exact Subtype.ext (by exact congr_hom hm x)⟩

variable (g h)

/-- The categorical equalizer in `Type u` is `{x : Y // g x = h x}`. -/
/-
**CategoryTheory.Limits.Types.equalizerIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Types`。
形式化陈述：equalizerIso : equalizer g h ≅ { x : Y // g x = h x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical equalizer in `Type u` is `{x : Y // g x = h x}`.
-/
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.equalizerIso_hom_comp_subtype** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：equalizerIso_hom_comp_subtype : (equalizerIso g h).hom ≫ ↾Subtype.val = eq
ualizer.ι g h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem equalizerIso_hom_comp_subtype :
    (equalizerIso g h).hom ≫ ↾Subtype.val = equalizer.ι g h := by
  rfl

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.equalizerIso_inv_comp_** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizerIso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h =
    ↾Subtype.val :=
  limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero

end CategoryTheory.Limits.Types

