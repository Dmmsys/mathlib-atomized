/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Small sets in the category of structured arrows

Here we prove a technical result about small sets in the category of structured arrows that will
be used in the proof of the Special Adjoint Functor Theorem.
-/

public section

namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} C] [LocallySmall.{w} D] : Small.{w} (StructuredArrow S T) :=
  small_of_surjective (f := fun (f : Σ (X : C), S ⟶ T.obj X) ↦ StructuredArrow.mk f.2)
    (fun f ↦ by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)
/-
**CategoryTheory.StructuredArrow.small_inverseImage_proj_of_locallySmall** 是 Mat
hlib 中的一个实例，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：small_inverseImage_proj_of_locallySmall {P : ObjectProperty C} [ObjectProp
erty.Small.{v₁} P] [LocallySmall.{v₁} D] : ObjectProperty.Small.{v₁} (P.inverseI
mage (proj S T))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.StructuredArrow.proj_obj`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (S : D) (T : Categ…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
-/
instance small_inverseImage_proj_of_locallySmall
    {P : ObjectProperty C} [ObjectProperty.Small.{v₁} P] [LocallySmall.{v₁} D] :
    ObjectProperty.Small.{v₁} (P.inverseImage (proj S T)) := by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h ↦ ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩
/-
**CategoryTheory.StructuredArrow.essentiallySmall** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.StructuredArrow`。
形式化陈述：essentiallySmall [EssentiallySmall.{w} C] [LocallySmall.{w} D] : Essential
lySmall.{w} (StructuredArrow S T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.essentiallySmall_congr`：essentiallySmall_congr {C : Type 
u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (e : C ≌ D) : EssentiallySma
ll.{w} C ↔ EssentiallySmall…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.StructuredArrow.instSmallOfLocallySmall`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {S : D} {T : Categ…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
instance essentiallySmall [EssentiallySmall.{w} C] [LocallySmall.{w} D] :
    EssentiallySmall.{w} (StructuredArrow S T) := by
  rw [← essentiallySmall_congr
    (StructuredArrow.pre S (equivSmallModel.{w} C).inverse T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} C] [LocallySmall.{w} D] : Small.{w} (CostructuredArrow S T) :=
  small_of_surjective (f := fun (f : Σ (X : C), S.obj X ⟶ T) ↦ CostructuredArrow.mk f.2)
    (fun f ↦ by
      obtain ⟨X, f, rfl⟩ := f.mk_surjective
      exact ⟨⟨X, f⟩, rfl⟩)
/-
**CategoryTheory.CostructuredArrow.small_inverseImage_proj_of_locallySmall** 是 M
athlib 中的一个实例，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：small_inverseImage_proj_of_locallySmall {P : ObjectProperty C} [ObjectProp
erty.Small.{v₁} P] [LocallySmall.{v₁} D] : ObjectProperty.Small.{v₁} (P.inverseI
mage (proj S T))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CostructuredArrow.proj_obj`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (S : CategoryTheor…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
-/
instance small_inverseImage_proj_of_locallySmall
    {P : ObjectProperty C} [ObjectProperty.Small.{v₁} P] [LocallySmall.{v₁} D] :
    ObjectProperty.Small.{v₁} (P.inverseImage (proj S T)) := by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h ↦ ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩
/-
**CategoryTheory.CostructuredArrow.essentiallySmall** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.CostructuredArrow`。
形式化陈述：essentiallySmall [EssentiallySmall.{w} C] [LocallySmall.{w} D] : Essential
lySmall.{w} (CostructuredArrow S T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.essentiallySmall_congr`：essentiallySmall_congr {C : Type 
u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (e : C ≌ D) : EssentiallySma
ll.{w} C ↔ EssentiallySmall…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.CostructuredArrow.instSmallOfLocallySmall`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {S : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
instance essentiallySmall [EssentiallySmall.{w} C] [LocallySmall.{w} D] :
    EssentiallySmall.{w} (CostructuredArrow S T) := by
  rw [← essentiallySmall_congr
    (CostructuredArrow.pre (equivSmallModel.{w} C).inverse S T).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

end CostructuredArrow

end CategoryTheory

