/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Order.OrderIsoNat
public import Mathlib.CategoryTheory.Simple

/-!
# Artinian objects

We shall say that an object `X` in a category `C` is Artinian
(type class `IsArtinianObject X`) if the ordered type `Subobject X`
satisfies the descending chain condition. The corresponding property of
objects `isArtinianObject : ObjectProperty C` is always
closed under subobjects.

## Future work

* when `C` is an abelian category, relate `IsArtinianObject` in `C`
  with `IsNoetherianObject` in `Cᵒᵖ`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

/-- An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Artinian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsArtinianObject` instead. -/
@[stacks 0FCF]
/-
**CategoryTheory.isArtinianObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isArtinianObject : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Artinian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsArtinianObject` instead.
-/
def isArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (Subobject X)

variable (X Y : C)

/-- An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. -/
@[stacks 0FCF]
/-
**CategoryTheory.IsArtinianObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsArtinianObject : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition.
-/
abbrev IsArtinianObject : Prop := isArtinianObject.Is X
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsArtinianObject X] : WellFoundedLT (Subobject X) :=
  isArtinianObject.prop_of_is X
/-
**CategoryTheory.isArtinianObject_iff_antitone_chain_condition** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory`。
形式化陈述：isArtinianObject_iff_antitone_chain_condition : IsArtinianObject X ↔ foral
l (f : Nat ->o (Subobject X)ᵒᵈ), exists (n : Nat), forall (m : Nat), n <= m -> f
 n = f m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.is_iff`：∀ {C : Type u} [inst : CategoryThe
ory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C) (X : C),   P.
Is X ↔ P X
· 使用定理 `CategoryTheory.isArtinianObject.eq_1`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] (X : C),   CategoryTheory.isArtinianObject X = WellFounde
dLT (CategoryTheory.Subobj…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wellFoundedGT_dual_iff`：wellFoundedGT_dual_iff (α : Type*) [LT α] : Well
FoundedGT αᵒᵈ ↔ WellFoundedLT α
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition`：wellFoundedGT_iff_monotone_c
hain_condition [PartialOrder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists
 n, forall m, n <= m -> a n = a …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isArtinianObject_iff_antitone_chain_condition :
    IsArtinianObject X ↔ ∀ (f : ℕ →o (Subobject X)ᵒᵈ),
      ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m := by
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff, isArtinianObject,
    ← wellFoundedGT_dual_iff,
    wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
/-
**CategoryTheory.antitone_chain_condition_of_isArtinianObject** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory`。
形式化陈述：antitone_chain_condition_of_isArtinianObject [IsArtinianObject X] (f : Nat
 ->o (Subobject X)ᵒᵈ) : exists (n : Nat), forall (m : Nat), n <= m -> f n = f m
参数：f : Nat ->o (Subobject X)ᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isArtinianObject_iff_antitone_chain_condition`：isArtinian
Object_iff_antitone_chain_condition : IsArtinianObject X ↔ forall (f : Nat ->o (
Subobject X)ᵒᵈ), exists (n : Nat), forall (m : Nat…
-/
lemma antitone_chain_condition_of_isArtinianObject
    [IsArtinianObject X] (f : ℕ →o (Subobject X)ᵒᵈ) :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m :=
  (isArtinianObject_iff_antitone_chain_condition X).1 inferInstance f
/-
**CategoryTheory.isArtinianObject_iff_not_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：isArtinianObject_iff_not_strictAnti : IsArtinianObject X ↔ forall (f : Nat
 -> Subobject X), ¬ StrictAnti f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_strictAnti_of_wellFoundedLT`：not_strictAnti_of_wellFoundedLT [Preord
er α] [WellFoundedLT α] (f : Nat -> α) : ¬ StrictAnti f
· 使用定理 `CategoryTheory.instWellFoundedLTSubobjectOfIsArtinianObject`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (X : C) [CategoryTheory.IsArtinian
Object X],   WellFoundedLT (CategoryTheory.Subobj…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.is_iff`：∀ {C : Type u} [inst : CategoryThe
ory.CategoryStruct.{v, u} C] (P : CategoryTheory.ObjectProperty C) (X : C),   P.
Is X ↔ P X
· 使用定理 `CategoryTheory.isArtinianObject.eq_1`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] (X : C),   CategoryTheory.isArtinianObject X = WellFounde
dLT (CategoryTheory.Subobj…
· 使用定理 `WellFoundedLT.eq_1`：∀ (α : Type u_1) [inst : LT α], WellFoundedLT α = Is
WellFounded α fun x1 x2 => x1 < x2
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `RelEmbedding.wellFounded_iff_isEmpty`：wellFounded_iff_isEmpty : WellFoun
ded r ↔ IsEmpty (((· > ·) : Nat -> Nat -> Prop) ↪r r) where mp
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
lemma isArtinianObject_iff_not_strictAnti :
    IsArtinianObject X ↔ ∀ (f : ℕ → Subobject X), ¬ StrictAnti f := by
  refine ⟨fun _ ↦ not_strictAnti_of_wellFoundedLT, fun h ↦ ?_⟩
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff, isArtinianObject, WellFoundedLT,
    isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f ↦ h f.toFun (fun a b h ↦ f.map_rel_iff.2 h)⟩

variable {X} in
/-
**CategoryTheory.not_strictAnti_of_isArtinianObject** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：not_strictAnti_of_isArtinianObject [IsArtinianObject X] (f : Nat -> Subobj
ect X) : ¬ StrictAnti f
参数：f : Nat -> Subobject X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isArtinianObject_iff_not_strictAnti`：isArtinianObject_iff
_not_strictAnti : IsArtinianObject X ↔ forall (f : Nat -> Subobject X), ¬ Strict
Anti f
-/
lemma not_strictAnti_of_isArtinianObject
    [IsArtinianObject X] (f : ℕ → Subobject X) :
    ¬ StrictAnti f :=
  (isArtinianObject_iff_not_strictAnti X).1 inferInstance f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isArtinianObject_iff_isEventuallyConstant** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory`。
形式化陈述：isArtinianObject_iff_isEventuallyConstant : IsArtinianObject X ↔ forall (F
 : Nat ⥤ (MonoOver X)ᵒᵖ), IsFiltered.IsEventuallyConstant F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isArtinianObject_iff_antitone_chain_condition`：isArtinian
Object_iff_antitone_chain_condition : IsArtinianObject X ↔ forall (f : Nat ->o (
Subobject X)ᵒᵈ), exists (n : Nat), forall (m : Nat…
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_unop_iff`：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : 
IsIso f.unop ↔ IsIso f
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
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
lemma isArtinianObject_iff_isEventuallyConstant :
    IsArtinianObject X ↔ ∀ (F : ℕ ⥤ (MonoOver X)ᵒᵖ),
      IsFiltered.IsEventuallyConstant F := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  refine ⟨fun h G ↦ ?_, fun h F ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver X).inverse.op ⋙
      (orderDualEquivalence _).inverse).monotone⟩
    refine ⟨n, fun m hm ↦ ?_⟩
    rw [← isIso_unop_iff, MonoOver.isIso_iff_subobjectMk_eq]
    exact (hn m (leOfHom hm)).symm
  · obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ (orderDualEquivalence _).functor ⋙
      Subobject.representative.op)
    refine ⟨n, fun m hm ↦ Eq.symm ?_⟩
    simpa [isIso_op_iff, isIso_iff_of_reflects_iso, PartialOrder.isIso_iff_eq]
      using hn (homOfLE hm)

variable {X} in
/-
**CategoryTheory.isEventuallyConstant_of_isArtinianObject** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：isEventuallyConstant_of_isArtinianObject [IsArtinianObject X] (F : Nat ⥤ (
MonoOver X)ᵒᵖ) : IsFiltered.IsEventuallyConstant F
参数：F : Nat ⥤ (MonoOver X)ᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isArtinianObject_iff_isEventuallyConstant`：isArtinianObje
ct_iff_isEventuallyConstant : IsArtinianObject X ↔ forall (F : Nat ⥤ (MonoOver X
)ᵒᵖ), IsFiltered.IsEventuallyConstant F
-/
lemma isEventuallyConstant_of_isArtinianObject [IsArtinianObject X]
    (F : ℕ ⥤ (MonoOver X)ᵒᵖ) : IsFiltered.IsEventuallyConstant F :=
  (isArtinianObject_iff_isEventuallyConstant X).1 inferInstance F

variable {X Y}
/-
**CategoryTheory.isArtinianObject_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isArtinianObject_of_isZero (hX : IsZero X) : IsArtinianObject X
参数：hX : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isArtinianObject_iff_antitone_chain_condition`：isArtinian
Object_iff_antitone_chain_condition : IsArtinianObject X ↔ forall (f : Nat ->o (
Subobject X)ᵒᵈ), exists (n : Nat), forall (m : Nat…
· 使用引理 `CategoryTheory.Subobject.subsingleton_of_isZero`：subsingleton_of_isZero 
{X : C} (hX : IsZero X) : Subsingleton (Subobject X)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `OrderDual.instSubsingleton`：∀ (α : Type u_2) [h : Subsingleton α], Subsi
ngleton αᵒᵈ
-/
lemma isArtinianObject_of_isZero (hX : IsZero X) : IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm ↦ Subsingleton.elim _ _⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : (isArtinianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isArtinianObject.is_iff]
    exact isArtinianObject_of_isZero (isZero_zero C)⟩
/-
**CategoryTheory.isArtinianObject_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isArtinianObject_of_mono (i : X ⟶ Y) [Mono i] [IsArtinianObject Y] : IsArt
inianObject X
参数：i : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isArtinianObject_iff_antitone_chain_condition`：isArtinian
Object_iff_antitone_chain_condition : IsArtinianObject X ↔ forall (f : Nat ->o (
Subobject X)ᵒᵈ), exists (n : Nat), forall (m : Nat…
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
· 使用引理 `CategoryTheory.antitone_chain_condition_of_isArtinianObject`：antitone_ch
ain_condition_of_isArtinianObject [IsArtinianObject X] (f : Nat ->o (Subobject X
)ᵒᵈ) : exists (n : Nat), forall (m : Nat), n <= m…
· 使用引理 `CategoryTheory.Subobject.map_obj_injective`：map_obj_injective {X Y : C} 
(f : X ⟶ Y) [Mono f] : Function.Injective (Subobject.map f).obj
-/
lemma isArtinianObject_of_mono (i : X ⟶ Y) [Mono i] [IsArtinianObject Y] :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject
    ⟨fun n ↦ (Subobject.map i).obj (f n),
      fun _ _ h ↦ (Subobject.map i).monotone (f.2 h)⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective i (hn m hm)⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isArtinianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isArtinianObject.is_iff] at hY ⊢
    exact isArtinianObject_of_mono f

open Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]
/-
**CategoryTheory.exists_simple_subobject** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：exists_simple_subobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) : exi
sts Y : Subobject X, Simple (Y : C)
参数：h : ¬IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.nontrivial_of_not_isZero`：nontrivial_of_not_isZ
ero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X)
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `instIsStronglyAtomicOfWellFoundedLT`：∀ {α : Type u_2} [inst : PartialOrd
er α] [WellFoundedLT α], IsStronglyAtomic α
· 使用定理 `CategoryTheory.instWellFoundedLTSubobjectOfIsArtinianObject`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (X : C) [CategoryTheory.IsArtinian
Object X],   WellFoundedLT (CategoryTheory.Subobj…
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.subobject_simple_iff_isAtom`：subobject_simple_iff_isAtom 
{X : C} (Y : Subobject X) : Simple (Y : C) ↔ IsAtom Y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exists_simple_subobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    ∃ Y : Subobject X, Simple (Y : C) := by
  have : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩

/-- Choose an arbitrary simple subobject of a non-zero Artinian object. -/
/-
**CategoryTheory.simpleSubobject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：simpleSubobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) : C
参数：h : ¬IsZero X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.exists_simple_subobject`：exists_simple_subobject {X : C} 
[IsArtinianObject X] (h : ¬IsZero X) : exists Y : Subobject X, Simple (Y : C)

--- 原说明 ---
Choose an arbitrary simple subobject of a non-zero Artinian object.
-/
noncomputable def simpleSubobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) : C :=
  (exists_simple_subobject h).choose

/-- The monomorphism from the arbitrary simple subobject of a non-zero Artinian object. -/
/-
**CategoryTheory.simpleSubobjectArrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) : simple
Subobject h ⟶ X
参数：h : ¬IsZero X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.exists_simple_subobject`：exists_simple_subobject {X : C} 
[IsArtinianObject X] (h : ¬IsZero X) : exists Y : Subobject X, Simple (Y : C)

--- 原说明 ---
The monomorphism from the arbitrary simple subobject of a non-zero Artinian obje
ct.
-/
noncomputable def simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    simpleSubobject h ⟶ X :=
  (exists_simple_subobject h).choose.arrow

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.mono_simpleSubobjectArrow** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：mono_simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) : M
ono (simpleSubobjectArrow h)
参数：h : ¬IsZero X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.exists_simple_subobject`：exists_simple_subobject {X : C} 
[IsArtinianObject X] (h : ¬IsZero X) : exists Y : Subobject X, Simple (Y : C)
-/
instance mono_simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    Mono (simpleSubobjectArrow h) := by
  dsimp only [simpleSubobjectArrow]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} [IsArtinianObject X] (h : ¬IsZero X) : Simple (simpleSubobject h) :=
  (exists_simple_subobject h).choose_spec

end CategoryTheory

