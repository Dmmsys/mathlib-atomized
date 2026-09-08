/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects

We shall say that an object `X` in a category `C` is Noetherian
(type class `IsNoetherianObject X`) if the ordered type `Subobject X`
satisfies the ascending chain condition. The corresponding property of
objects `isNoetherianObject : ObjectProperty C` is always
closed under subobjects.

## Future works

* show that `isNoetherian` is a Serre class when `C` is an abelian category
  (TODO @joelriou)

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

/-- An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Noetherian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsNoetherianObject` instead. -/
@[stacks 0FCG]
/-
**CategoryTheory.isNoetherianObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isNoetherianObject : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Noetherian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsNoetherianObject` instead.
-/
def isNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (Subobject X)

variable (X Y : C)

/-- An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition. -/
@[stacks 0FCG]
/-
**CategoryTheory.IsNoetherianObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`
。
形式化陈述：IsNoetherianObject : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in a category `C` is Noetherian if `Subobject X`
satisfies the ascending chain condition.
-/
abbrev IsNoetherianObject : Prop := isNoetherianObject.Is X
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherianObject X] : WellFoundedGT (Subobject X) :=
  isNoetherianObject.prop_of_is X
/-
**CategoryTheory.isNoetherianObject_iff_monotone_chain_condition** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isNoetherianObject_iff_monotone_chain_condition : IsNoetherianObject X ↔ f
orall (f : Nat ->o Subobject X), exists (n : Nat), forall (m : Nat), n <= m -> f
 n = f m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.is_iff`：∀ {C : Type u} [inst : CategoryThe
ory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C) (X : C),   P.
Is X ↔ P X
· 使用定理 `CategoryTheory.isNoetherianObject.eq_1`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] (X : C),   CategoryTheory.isNoetherianObject X = WellFo
undedGT (CategoryTheory.Subo…
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition`：wellFoundedGT_iff_monotone_c
hain_condition [PartialOrder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists
 n, forall m, n <= m -> a n = a …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isNoetherianObject_iff_monotone_chain_condition :
    IsNoetherianObject X ↔ ∀ (f : ℕ →o Subobject X),
      ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m := by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject,
    wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
/-
**CategoryTheory.monotone_chain_condition_of_isNoetherianObject** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory`。
形式化陈述：monotone_chain_condition_of_isNoetherianObject [IsNoetherianObject X] (f :
 Nat ->o Subobject X) : exists (n : Nat), forall (m : Nat), n <= m -> f n = f m
参数：f : Nat ->o Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`：isNoethe
rianObject_iff_monotone_chain_condition : IsNoetherianObject X ↔ forall (f : Nat
 ->o Subobject X), exists (n : Nat), forall (m : Nat…
-/
lemma monotone_chain_condition_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ →o Subobject X) :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m :=
  (isNoetherianObject_iff_monotone_chain_condition X).1 inferInstance f
/-
**CategoryTheory.isNoetherianObject_iff_not_strictMono** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory`。
形式化陈述：isNoetherianObject_iff_not_strictMono : IsNoetherianObject X ↔ forall (f :
 Nat -> Subobject X), ¬ StrictMono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_strictMono_of_wellFoundedGT`：not_strictMono_of_wellFoundedGT [Preord
er α] [WellFoundedGT α] (f : Nat -> α) : ¬ StrictMono f
· 使用定理 `CategoryTheory.instWellFoundedGTSubobjectOfIsNoetherianObject`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (X : C) [CategoryTheory.IsNoethe
rianObject X],   WellFoundedGT (CategoryTheory.Subo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.is_iff`：∀ {C : Type u} [inst : CategoryThe
ory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C) (X : C),   P.
Is X ↔ P X
· 使用定理 `CategoryTheory.isNoetherianObject.eq_1`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] (X : C),   CategoryTheory.isNoetherianObject X = WellFo
undedGT (CategoryTheory.Subo…
· 使用定理 `WellFoundedGT.eq_1`：∀ (α : Type u_1) [inst : LT α], WellFoundedGT α = Is
WellFounded α fun x1 x2 => x2 < x1
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `RelEmbedding.wellFounded_iff_isEmpty`：wellFounded_iff_isEmpty : WellFoun
ded r ↔ IsEmpty (((· > ·) : Nat -> Nat -> Prop) ↪r r) where mp
· 使用定理 `instIsStrictOrderGt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x2 < x1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
lemma isNoetherianObject_iff_not_strictMono :
    IsNoetherianObject X ↔ ∀ (f : ℕ → Subobject X), ¬ StrictMono f := by
  refine ⟨fun _ ↦ not_strictMono_of_wellFoundedGT, fun h ↦ ?_⟩
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject, WellFoundedGT,
    isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f ↦ h f.toFun (fun a b h ↦ f.map_rel_iff.2 h)⟩

variable {X} in
/-
**CategoryTheory.not_strictMono_of_isNoetherianObject** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：not_strictMono_of_isNoetherianObject [IsNoetherianObject X] (f : Nat -> Su
bobject X) : ¬ StrictMono f
参数：f : Nat -> Subobject X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isNoetherianObject_iff_not_strictMono`：isNoetherianObject
_iff_not_strictMono : IsNoetherianObject X ↔ forall (f : Nat -> Subobject X), ¬ 
StrictMono f
-/
lemma not_strictMono_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ → Subobject X) :
    ¬ StrictMono f :=
  (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isNoetherianObject_iff_isEventuallyConstant** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory`。
形式化陈述：isNoetherianObject_iff_isEventuallyConstant : IsNoetherianObject X ↔ foral
l (F : Nat ⥤ MonoOver X), IsFiltered.IsEventuallyConstant F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`：isNoethe
rianObject_iff_monotone_chain_condition : IsNoetherianObject X ↔ forall (f : Nat
 ->o Subobject X), exists (n : Nat), forall (m : Nat…
· 使用引理 `CategoryTheory.MonoOver.isIso_iff_subobjectMk_eq`：isIso_iff_subobjectMk_
eq : IsIso f ↔ Subobject.mk P.1.hom = Subobject.mk Q.1.hom
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Subobject.instIsEquivalenceMonoOverRepresentative`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C},   CategoryTheory.
Subobject.representative.IsEquivalence
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma isNoetherianObject_iff_isEventuallyConstant :
    IsNoetherianObject X ↔ ∀ (F : ℕ ⥤ MonoOver X),
      IsFiltered.IsEventuallyConstant F := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  refine ⟨fun h G ↦ ?_, fun h F ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h (G ⋙ (Subobject.equivMonoOver _).inverse).toOrderHom
    refine ⟨n, fun m hm ↦ ?_⟩
    rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ Subobject.representative)
    refine ⟨n, fun m hm ↦ ?_⟩
    simpa [← MonoOver.isIso_iff_isIso_hom_left, isIso_iff_of_reflects_iso,
      PartialOrder.isIso_iff_eq] using hn (homOfLE hm)

variable {X} in
/-
**CategoryTheory.isEventuallyConstant_of_isNoetherianObject** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory`。
形式化陈述：isEventuallyConstant_of_isNoetherianObject [IsNoetherianObject X] (F : Nat
 ⥤ MonoOver X) : IsFiltered.IsEventuallyConstant F
参数：F : Nat ⥤ MonoOver X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isNoetherianObject_iff_isEventuallyConstant`：isNoetherian
Object_iff_isEventuallyConstant : IsNoetherianObject X ↔ forall (F : Nat ⥤ MonoO
ver X), IsFiltered.IsEventuallyConstant F
-/
lemma isEventuallyConstant_of_isNoetherianObject [IsNoetherianObject X]
    (F : ℕ ⥤ MonoOver X) : IsFiltered.IsEventuallyConstant F :=
  (isNoetherianObject_iff_isEventuallyConstant X).1 inferInstance F

variable {X Y}
/-
**CategoryTheory.isNoetherianObject_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：isNoetherianObject_of_isZero (hX : IsZero X) : IsNoetherianObject X
参数：hX : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`：isNoethe
rianObject_iff_monotone_chain_condition : IsNoetherianObject X ↔ forall (f : Nat
 ->o Subobject X), exists (n : Nat), forall (m : Nat…
· 使用引理 `CategoryTheory.Subobject.subsingleton_of_isZero`：subsingleton_of_isZero 
{X : C} (hX : IsZero X) : Subsingleton (Subobject X)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma isNoetherianObject_of_isZero (hX : IsZero X) : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm ↦ Subsingleton.elim _ _⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : (isNoetherianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isNoetherianObject.is_iff]
    exact isNoetherianObject_of_isZero (isZero_zero C)⟩
/-
**CategoryTheory.isNoetherianObject_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isNoetherianObject_of_mono (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] : I
sNoetherianObject X
参数：i : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`：isNoethe
rianObject_iff_monotone_chain_condition : IsNoetherianObject X ↔ forall (f : Nat
 ->o Subobject X), exists (n : Nat), forall (m : Nat…
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
· 使用引理 `CategoryTheory.monotone_chain_condition_of_isNoetherianObject`：monotone_
chain_condition_of_isNoetherianObject [IsNoetherianObject X] (f : Nat ->o Subobj
ect X) : exists (n : Nat), forall (m : Nat), n <= m…
· 使用引理 `CategoryTheory.Subobject.map_obj_injective`：map_obj_injective {X Y : C} 
(f : X ⟶ Y) [Mono f] : Function.Injective (Subobject.map f).obj
-/
lemma isNoetherianObject_of_mono (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective i (hn m hm)⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isNoetherianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isNoetherianObject.is_iff] at hY ⊢
    exact isNoetherianObject_of_mono f

end CategoryTheory

