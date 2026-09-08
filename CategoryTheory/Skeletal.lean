/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A category is skeletal if isomorphic objects are equal. -/
/-
**CategoryTheory.Skeletal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Skeletal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is skeletal if isomorphic objects are equal.
-/
def Skeletal : Prop :=
  ∀ ⦃X Y : C⦄, IsIsomorphic X Y → X = Y

/-- `IsSkeletonOf C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
/-
**CategoryTheory.IsSkeletonOf** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：IsSkeletonOf (F : D ⥤ C) : Prop where /-- The category `D` has isomorphic 
objects equal -/ skel : Skeletal D /-- The functor `F` is an equivalence -/ eqv 
: F.IsEquivalence
参数：F : D ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSkeletonOf C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subca
tegory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
structure IsSkeletonOf (F : D ⥤ C) : Prop where
  /-- The category `D` has isomorphic objects equal -/
  skel : Skeletal D
  /-- The functor `F` is an equivalence -/
  eqv : F.IsEquivalence := by infer_instance

attribute [local instance] isIsomorphicSetoid

variable {C D}

/-- If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are equal. -/
/-
**CategoryTheory.Functor.eq_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F₁ F₂ : CategoryTheory.Functor 
D C} [Quiver.IsThin C], CategoryTheory.Skeletal C → ∀ (hF : F₁ ≅ F₂), F₁ = F₂
参数：hF : F₁ ≅ F₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are e
qual.
-/
theorem Functor.eq_of_iso {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂) :
    F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

/-- If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`CategoryTheory.functor_thin` shows it is thin also.
-/
/-
**CategoryTheory.functor_skeletal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C)
参数：hC : Skeletal C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `CategoryTheory.Functor.eq_of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {F₁ F₂ : CategoryT…

--- 原说明 ---
If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`CategoryTheory.functor_thin` shows it is thin also.
-/
theorem functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C) := fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)

variable (C D)

noncomputable section

/-- Construct the skeleton category as the induced category on the isomorphism classes, and derive
its category structure.
-/
/-
**CategoryTheory.Skeleton** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Skeleton : Type u₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the skeleton category as the induced category on the isomorphism class
es, and derive
its category structure.
-/
def Skeleton : Type u₁ := InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out
deriving
  Category,
  [Inhabited C] → Inhabited _

-- Without this we get errors in Mathlib/RingTheory/PicardGroup.lean
set_option backward.inferInstanceAs.wrap.data false in
deriving instance (α : Sort _) → [CoeSort C α] → CoeSort _ α for Skeleton C

end

/-- The functor from the skeleton of `C` to `C`. -/
@[simps!]
/-
**CategoryTheory.fromSkeleton** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：fromSkeleton : Skeleton C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from the skeleton of `C` to `C`.
-/
noncomputable def fromSkeleton : Skeleton C ⥤ C :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
-- Note(kmill): `derive Functor.Full, Functor.Faithful` does not create instances
-- that are in terms of `Skeleton`, but rather `InducedCategory`, which can't be applied.
-- With `deriving @Functor.Full (Skeleton C)`, the instance can't be derived, for a similar reason.
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (fromSkeleton C).Full := by
  apply InducedCategory.full
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (fromSkeleton C).Faithful := by
  apply InducedCategory.faithful
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromSkeleton C).EssSurj where mem_essImage X := ⟨Quotient.mk' X, Quotient.mk_out X⟩
/-
**CategoryTheory.fromSkeleton.isEquivalence** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.fromSkeleton`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C], (CategoryTheo
ry.fromSkeleton C).IsEquivalence
参数：C : Type u₁；CategoryTheory.fromSkeleton C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instFaithfulSkeletonFromSkeleton`：∀ (C : Type u₁) [inst :
 CategoryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).Faithful
· 使用定理 `CategoryTheory.instFullSkeletonFromSkeleton`：∀ (C : Type u₁) [inst : Cat
egoryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).Full
· 使用定理 `CategoryTheory.instEssSurjSkeletonFromSkeleton`：∀ (C : Type u₁) [inst : 
CategoryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).EssSurj
-/
noncomputable instance fromSkeleton.isEquivalence : (fromSkeleton C).IsEquivalence where

variable {C}

/-- The class of an object in the skeleton. -/
/-
**CategoryTheory.toSkeleton** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：toSkeleton (X : C) : Skeleton C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of an object in the skeleton.
-/
abbrev toSkeleton (X : C) : Skeleton C := ⟦X⟧

/-- The isomorphism between `⟦X⟧.out` and `X`. -/
/-
**CategoryTheory.fromSkeletonToSkeletonIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：fromSkeletonToSkeletonIso (X : C) : (fromSkeleton C).obj (toSkeleton X) ≅ 
X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `⟦X⟧.out` and `X`.
-/
noncomputable def fromSkeletonToSkeletonIso (X : C) : (fromSkeleton C).obj (toSkeleton X) ≅ X :=
  Nonempty.some (Quotient.mk_out X)

@[reassoc, simp]
/-
**CategoryTheory.Skeleton.comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ske
leton`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Categ
oryTheory.Skeleton C} (f : X ⟶ Y) (g : Y ⟶ Z),   (CategoryTheory.CategoryStruct.
comp f g).hom = CategoryTheory.CategoryStruct.comp f.hom g.hom
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Skeleton.comp_hom {X Y Z : Skeleton C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
/-- An inverse to `fromSkeleton C` that forms an equivalence with it. -/
/-
**CategoryTheory.toSkeletonFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor C (CategoryTheory.Skeleton C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inverse to `fromSkeleton C` that forms an equivalence with it.
-/
@[simps] noncomputable def toSkeletonFunctor : C ⥤ Skeleton C where
  obj := toSkeleton
  map {X Y} f :=
    { hom := (fromSkeletonToSkeletonIso X).hom ≫ f ≫ (fromSkeletonToSkeletonIso Y).inv }
  map_id _ := by aesop
  map_comp _ _ := InducedCategory.hom_ext (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between the skeleton and the category itself. -/
/-
**CategoryTheory.skeletonEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Skeleton C ≌ C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the skeleton and the category itself.
-/
@[simps] noncomputable def skeletonEquivalence : Skeleton C ≌ C where
  functor := fromSkeleton C
  inverse := toSkeletonFunctor C
  unitIso := NatIso.ofComponents
    (fun X ↦ InducedCategory.isoMk (Nonempty.some <| Quotient.mk_out X.out).symm)
    (fun f ↦ InducedCategory.hom_ext (Iso.inv_hom_id_assoc _ _).symm)
  counitIso := NatIso.ofComponents fromSkeletonToSkeletonIso
  functor_unitIso_comp _ := Iso.inv_hom_id _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.skeleton_skeletal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：skeleton_skeletal : Skeletal (Skeleton C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem skeleton_skeletal : Skeletal (Skeleton C) := by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(fromSkeleton C).mapIso h⟩
  simpa using! Quotient.sound this

/-- The `skeleton` of `C` given by choice is a skeleton of `C`. -/
/-
**CategoryTheory.skeleton_isSkeleton** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：skeleton_isSkeleton : IsSkeletonOf C (Skeleton C) (fromSkeleton C) where s
kel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.skeleton_skeletal`：skeleton_skeletal : Skeletal (Skeleton
 C)
· 使用定理 `CategoryTheory.fromSkeleton.isEquivalence`：∀ (C : Type u₁) [inst : Categ
oryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).IsEquivalence

--- 原说明 ---
The `skeleton` of `C` given by choice is a skeleton of `C`.
-/
lemma skeleton_isSkeleton : IsSkeletonOf C (Skeleton C) (fromSkeleton C) where
  skel := skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C

variable {C D}
/-
**CategoryTheory.toSkeleton_fromSkeleton_obj** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：toSkeleton_fromSkeleton_obj (X : Skeleton C) : toSkeleton ((fromSkeleton C
).obj X) = X
参数：X : Skeleton C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
lemma toSkeleton_fromSkeleton_obj (X : Skeleton C) : toSkeleton ((fromSkeleton C).obj X) = X :=
  Quotient.out_eq _
/-
**CategoryTheory.toSkeleton_eq_toSkeleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：toSkeleton_eq_toSkeleton_iff {X Y : C} : toSkeleton X = toSkeleton Y ↔ Non
empty (X ≅ Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
lemma toSkeleton_eq_toSkeleton_iff {X Y : C} : toSkeleton X = toSkeleton Y ↔ Nonempty (X ≅ Y) :=
  Quotient.eq
/-
**CategoryTheory.congr_toSkeleton_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：congr_toSkeleton_of_iso {X Y : C} (e : X ≅ Y) : toSkeleton X = toSkeleton 
Y
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
lemma congr_toSkeleton_of_iso {X Y : C} (e : X ≅ Y) : toSkeleton X = toSkeleton Y :=
  Quotient.sound ⟨e⟩

/-- Provides a (noncomputable) isomorphism `X ≅ Y` given that `toSkeleton X = toSkeleton Y`. -/
/-
**CategoryTheory.Skeleton.isoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Skel
eton`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → CategoryTheory.toSkeleton X = CategoryTheory.toSkeleton Y → (X ≅ Y)
参数：X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Provides a (noncomputable) isomorphism `X ≅ Y` given that `toSkeleton X = toSkel
eton Y`.
-/
noncomputable def Skeleton.isoOfEq {X Y : C} (h : toSkeleton X = toSkeleton Y) :
    X ≅ Y :=
  Quotient.exact h |>.some
/-
**CategoryTheory.toSkeleton_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：toSkeleton_eq_iff {X : C} {Y : Skeleton C} : toSkeleton X = Y ↔ Nonempty (
X ≅ (fromSkeleton C).obj Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_eq_iff_out`：Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y
 : Quotient s} : ⟦x⟧ = y ↔ x ≈ Quotient.out y
-/
lemma toSkeleton_eq_iff {X : C} {Y : Skeleton C} :
    toSkeleton X = Y ↔ Nonempty (X ≅ (fromSkeleton C).obj Y) :=
  Quotient.mk_eq_iff_out

namespace Functor

/-- From a functor `C ⥤ D`, construct a map of skeletons `Skeleton C → Skeleton D`. -/
/-
**CategoryTheory.Functor.mapSkeleton** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapSkeleton (F : C ⥤ D) : Skeleton C ⥤ Skeleton D
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a functor `C ⥤ D`, construct a map of skeletons `Skeleton C → Skeleton D`.
-/
noncomputable def mapSkeleton (F : C ⥤ D) : Skeleton C ⥤ Skeleton D :=
  (skeletonEquivalence C).functor ⋙ F ⋙ (skeletonEquivalence D).inverse

variable (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.mapSkeleton_obj_toSkeleton** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：mapSkeleton_obj_toSkeleton (X : C) : F.mapSkeleton.obj (toSkeleton X) = to
Skeleton (F.obj X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.congr_toSkeleton_of_iso`：congr_toSkeleton_of_iso {X Y : C
} (e : X ≅ Y) : toSkeleton X = toSkeleton Y
-/
lemma mapSkeleton_obj_toSkeleton (X : C) :
    F.mapSkeleton.obj (toSkeleton X) = toSkeleton (F.obj X) :=
  congr_toSkeleton_of_iso <| F.mapIso <| fromSkeletonToSkeletonIso X
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Full] : F.mapSkeleton.Full := inferInstanceAs <| (_ ⋙ _).Full
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Faithful] : F.mapSkeleton.Faithful := inferInstanceAs <| (_ ⋙ _).Faithful
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.EssSurj] : F.mapSkeleton.EssSurj := inferInstanceAs <| (_ ⋙ _).EssSurj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural isomorphism between `X ↦ ⟦X⟧ ↦ ⟦FX⟧` and `X ↦ FX ↦ ⟦FX⟧`. On the level of
categories, these are `C ⥤ Skeleton C ⥤ Skeleton D` and `C ⥤ D ⥤ Skeleton D`. So this says that
the square formed by these 4 objects and 4 functors commutes. -/
/-
**CategoryTheory.Functor.toSkeletonFunctorCompMapSkeletonIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：toSkeletonFunctorCompMapSkeletonIso : toSkeletonFunctor C ⋙ F.mapSkeleton 
≅ F ⋙ toSkeletonFunctor D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between `X ↦ ⟦X⟧ ↦ ⟦FX⟧` and `X ↦ FX ↦ ⟦FX⟧`. On the level
 of
categories, these are `C ⥤ Skeleton C ⥤ Skeleton D` and `C ⥤ D ⥤ Skeleton D`. So
 this says that
the square formed by these 4 objects and 4 functors commutes.
-/
noncomputable def toSkeletonFunctorCompMapSkeletonIso :
    toSkeletonFunctor C ⋙ F.mapSkeleton ≅ F ⋙ toSkeletonFunctor D :=
  NatIso.ofComponents
    (fun X ↦ (toSkeletonFunctor D).mapIso <| F.mapIso <| fromSkeletonToSkeletonIso X)
    (fun f ↦ InducedCategory.hom_ext (show (_ ≫ _) ≫ _ = _ ≫ _ by simp))
/-
**CategoryTheory.Functor.mapSkeleton_injective** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：mapSkeleton_injective [F.Full] [F.Faithful] : Function.Injective F.mapSkel
eton.obj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.skeleton_skeletal`：skeleton_skeletal : Skeletal (Skeleton
 C)
· 使用定理 `CategoryTheory.Functor.instFullSkeletonMapSkeleton`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulSkeletonMapSkeleton`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma mapSkeleton_injective [F.Full] [F.Faithful] : Function.Injective F.mapSkeleton.obj :=
  fun _ _ h ↦ skeleton_skeletal C ⟨F.mapSkeleton.preimageIso <| eqToIso h⟩
/-
**CategoryTheory.Functor.mapSkeleton_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：mapSkeleton_surjective [F.EssSurj] : Function.Surjective F.mapSkeleton.obj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instEssSurjSkeletonMapSkeleton`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.skeleton_skeletal`：skeleton_skeletal : Skeletal (Skeleton
 C)
-/
lemma mapSkeleton_surjective [F.EssSurj] : Function.Surjective F.mapSkeleton.obj :=
  fun Y ↦ let ⟨X, h⟩ := EssSurj.mem_essImage F.mapSkeleton Y; ⟨X, skeleton_skeletal D h⟩

end Functor

/-- Two categories which are categorically equivalent have skeletons with equivalent objects.
-/
/-
**CategoryTheory.Equivalence.skeletonEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (C ≌ D) → Catego
ryTheory.Skeleton C ≃ CategoryTheory.Skeleton D
参数：C ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two categories which are categorically equivalent have skeletons with equivalent
 objects.
-/
noncomputable def Equivalence.skeletonEquiv (e : C ≌ D) : Skeleton C ≃ Skeleton D :=
  let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.functor.obj
    invFun := f.inverse.obj
    left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }

variable (C D)

/-- Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
If your original category is not thin, you probably want to be using `Skeleton` instead of this.
-/
@[implicit_reducible]
/-
**CategoryTheory.ThinSkeleton** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ThinSkeleton : Type u₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the skeleton category by taking the quotient of objects. This construc
tion gives a
preorder with nice definitional properties, but is only really appropriate for t
hin categories.
If your original category is not thin, you probably want to be using `Skeleton` 
instead of this.
-/
def ThinSkeleton : Type u₁ :=
  Quotient (isIsomorphicSetoid C)

variable {C} in
/-- Convenience constructor for `ThinSkeleton`. -/
/-
**CategoryTheory.ThinSkeleton.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ThinS
keleton`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → C → Category
Theory.ThinSkeleton C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
Convenience constructor for `ThinSkeleton`.
-/
abbrev ThinSkeleton.mk (c : C) : ThinSkeleton C := Quotient.mk' c
/-
**CategoryTheory.inhabitedThinSkeleton** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：inhabitedThinSkeleton [Inhabited C] : Inhabited (ThinSkeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedThinSkeleton [Inhabited C] : Inhabited (ThinSkeleton C) :=
  ⟨ThinSkeleton.mk default⟩
/-
**CategoryTheory.ThinSkeleton.preorder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ThinSkeleton`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → Preorder (Ca
tegoryTheory.ThinSkeleton C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ThinSkeleton.preorder : Preorder (ThinSkeleton C) where
  le :=
    @Quotient.lift₂ C C _ (isIsomorphicSetoid C) (isIsomorphicSetoid C)
      (fun X Y => Nonempty (X ⟶ Y))
        (by
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact
            propext
              ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom,
                Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine Quotient.ind fun a => ?_
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Nonempty.map2 (· ≫ ·)

/-- The functor from a category to its thin skeleton. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.toThinSkeleton** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：toThinSkeleton : C ⥤ ThinSkeleton C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from a category to its thin skeleton.
-/
def toThinSkeleton : C ⥤ ThinSkeleton C where
  obj := ThinSkeleton.mk
  map f := homOfLE (Nonempty.intro f)

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/


namespace ThinSkeleton

/-- The thin skeleton is thin. -/
/-
**CategoryTheory.ThinSkeleton.thin** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Thi
nSkeleton`。
形式化陈述：thin : Quiver.IsThin (ThinSkeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The thin skeleton is thin.
-/
instance thin : Quiver.IsThin (ThinSkeleton C) := fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨_⟩⟩
    rfl⟩

variable {C} {D}

set_option backward.isDefEq.respectTransparency.types false in
/-- A functor `C ⥤ D` computably lowers to a functor `ThinSkeleton C ⥤ ThinSkeleton D`. -/
@[simps]
/-
**CategoryTheory.ThinSkeleton.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Thin
Skeleton`。
形式化陈述：map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where obj
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `C ⥤ D` computably lowers to a functor `ThinSkeleton C ⥤ ThinSkeleton 
D`.
-/
def map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where
  obj := Quotient.map F.obj fun _ _ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map {X} {Y} := Quotient.recOnSubsingleton₂ X Y fun _ _ k => homOfLE (k.le.elim fun t => ⟨F.map t⟩)
/-
**CategoryTheory.ThinSkeleton.comp_toThinSkeleton** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ThinSkeleton`。
形式化陈述：comp_toThinSkeleton (F : C ⥤ D) : F ⋙ toThinSkeleton D = toThinSkeleton C 
⋙ map F
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toThinSkeleton (F : C ⥤ D) : F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F :=
  rfl

/-- Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F₁ ⟶ map F₂`. -/
/-
**CategoryTheory.ThinSkeleton.mapNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ThinSkeleton`。
形式化陈述：mapNatTrans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ where app X
参数：k : F₁ ⟶ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F
₁ ⟶ map F₂`.
-/
def mapNatTrans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ where
  app X := Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩

/- Porting note: `map₂ObjMap`, `map₂Functor`, and `map₂NatTrans` were all extracted
from the original `map₂` proof. Lean needed an extensive amount of explicit type
annotations to figure things out. This also translated into repeated deterministic
timeouts. The extracted defs allow for explicit motives for the multiple
descents to the quotients.

It would be better to prove that
`ThinSkeleton (C × D) ≌ ThinSkeleton C × ThinSkeleton D`
which is more immediate from comparing the preorders. Then one could get
`map₂` by currying.
-/
/-- Given a bifunctor, we descend to a function on objects of `ThinSkeleton` -/
/-
**CategoryTheory.ThinSkeleton.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Thin
Skeleton`。
形式化陈述：map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where obj
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a bifunctor, we descend to a function on objects of `ThinSkeleton`
-/
def map₂ObjMap (F : C ⥤ D ⥤ E) : ThinSkeleton C → ThinSkeleton D → ThinSkeleton E :=
  fun x y =>
    @Quotient.map₂ C D (isIsomorphicSetoid C) (isIsomorphicSetoid D) E (isIsomorphicSetoid E)
      (fun X Y => (F.obj X).obj Y)
          (fun X₁ _ ⟨hX⟩ _ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y

/-- For each `x : ThinSkeleton C`, we promote `map₂ObjMap F x` to a functor -/
/-
**CategoryTheory.ThinSkeleton.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Thin
Skeleton`。
形式化陈述：map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where obj
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `x : ThinSkeleton C`, we promote `map₂ObjMap F x` to a functor
-/
def map₂Functor (F : C ⥤ D ⥤ E) : ThinSkeleton C → ThinSkeleton D ⥤ ThinSkeleton E :=
  fun x =>
    { obj := fun y => map₂ObjMap F x y
      map := fun {y₁} {y₂} => @Quotient.recOnSubsingleton C (isIsomorphicSetoid C)
        (fun x => (y₁ ⟶ y₂) → (map₂ObjMap F x y₁ ⟶ map₂ObjMap F x y₂)) _ x fun X
          => Quotient.recOnSubsingleton₂ y₁ y₂ fun _ _ hY =>
            homOfLE (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }

/-- This provides natural transformations `map₂Functor F x₁ ⟶ map₂Functor F x₂` given
`x₁ ⟶ x₂` -/
/-
**CategoryTheory.ThinSkeleton.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Thin
Skeleton`。
形式化陈述：map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where obj
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This provides natural transformations `map₂Functor F x₁ ⟶ map₂Functor F x₂` give
n
`x₁ ⟶ x₂`
-/
def map₂NatTrans (F : C ⥤ D ⥤ E) : {x₁ x₂ : ThinSkeleton C} → (x₁ ⟶ x₂) →
    (map₂Functor F x₁ ⟶ map₂Functor F x₂) := fun {x₁} {x₂} =>
  @Quotient.recOnSubsingleton₂ C C (isIsomorphicSetoid C) (isIsomorphicSetoid C)
    (fun x x' : ThinSkeleton C => (x ⟶ x') → (map₂Functor F x ⟶ map₂Functor F x')) _ x₁ x₂
    (fun X₁ X₂ f => { app := fun y =>
      Quotient.recOnSubsingleton y fun Y => homOfLE (f.le.elim fun f' => ⟨(F.map f').app Y⟩) })

-- TODO: state the lemmas about what happens when you compose with `toThinSkeleton`
/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E` -/
@[simps]
/-
**CategoryTheory.ThinSkeleton.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Thin
Skeleton`。
形式化陈述：map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where obj
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `C ⥤ D ⥤ E` computably lowers to a functor
`ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E`
-/
def map₂ (F : C ⥤ D ⥤ E) : ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E where
  obj := map₂Functor F
  map := map₂NatTrans F

variable (C)

section

variable [Quiver.IsThin C]

/-
**CategoryTheory.ThinSkeleton.toThinSkeleton_faithful** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ThinSkeleton`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] [Quiver.IsThin
 C],   (CategoryTheory.toThinSkeleton C).Faithful
参数：C : Type u₁；CategoryTheory.toThinSkeleton C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance toThinSkeleton_faithful : (toThinSkeleton C).Faithful where

/-- Use `Quotient.out` to create a functor out of the thin skeleton. -/
@[simps]
/-
**CategoryTheory.ThinSkeleton.fromThinSkeleton** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ThinSkeleton`。
形式化陈述：fromThinSkeleton : ThinSkeleton C ⥤ C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `Quotient.out` to create a functor out of the thin skeleton.
-/
noncomputable def fromThinSkeleton : ThinSkeleton C ⥤ C where
  obj := Quotient.out
  map {x} {y} :=
    Quotient.recOnSubsingleton₂ x y fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv

/-- The equivalence between the thin skeleton and the category itself. -/
/-
**CategoryTheory.ThinSkeleton.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ThinSkeleton`。
形式化陈述：equivalence : ThinSkeleton C ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the thin skeleton and the category itself.
-/
noncomputable def equivalence : ThinSkeleton C ≌ C where
  functor := fromThinSkeleton C
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents fun X => Nonempty.some (Quotient.mk_out X)
  unitIso := NatIso.ofComponents fun x => Quotient.recOnSubsingleton x fun X =>
    eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩)
/-
**CategoryTheory.ThinSkeleton.fromThinSkeleton_isEquivalence** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.ThinSkeleton`。
形式化陈述：fromThinSkeleton_isEquivalence : (fromThinSkeleton C).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
noncomputable instance fromThinSkeleton_isEquivalence : (fromThinSkeleton C).IsEquivalence :=
  (equivalence C).isEquivalence_functor

variable {C}
/-
**CategoryTheory.ThinSkeleton.equiv_of_both_ways** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ThinSkeleton`。
形式化陈述：equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y
参数：f : X ⟶ Y；g : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  ⟨iso_of_both_ways f g⟩
/-
**CategoryTheory.ThinSkeleton.thinSkeletonPartialOrder** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ThinSkeleton`。
形式化陈述：thinSkeletonPartialOrder : PartialOrder (ThinSkeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance thinSkeletonPartialOrder : PartialOrder (ThinSkeleton C) :=
  { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }
/-
**CategoryTheory.ThinSkeleton.skeletal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ThinSkeleton`。
形式化陈述：skeletal : Skeletal (ThinSkeleton C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
theorem skeletal : Skeletal (ThinSkeleton C) := fun X Y =>
  Quotient.inductionOn₂ X Y fun _ _ h => h.elim fun i => i.1.le.antisymm i.2.le
/-
**CategoryTheory.ThinSkeleton.map_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ThinSkeleton`。
形式化陈述：map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G
参数：F : E ⥤ D；G : D ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.eq_of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {F₁ F₂ : CategoryT…
· 使用定理 `CategoryTheory.ThinSkeleton.skeletal`：skeletal : Skeletal (ThinSkeleton 
C)
-/
theorem map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
  Functor.eq_of_iso skeletal <|
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _
/-
**CategoryTheory.ThinSkeleton.map_id_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ThinSkeleton`。
形式化陈述：map_id_eq : map (𝟭 C) = 𝟭 (ThinSkeleton C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.eq_of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {F₁ F₂ : CategoryT…
· 使用定理 `CategoryTheory.ThinSkeleton.skeletal`：skeletal : Skeletal (ThinSkeleton 
C)
-/
theorem map_id_eq : map (𝟭 C) = 𝟭 (ThinSkeleton C) :=
  Functor.eq_of_iso skeletal <|
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _
/-
**CategoryTheory.ThinSkeleton.map_iso_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ThinSkeleton`。
形式化陈述：map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂
参数：h : F₁ ≅ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.eq_of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {F₁ F₂ : CategoryT…
· 使用定理 `CategoryTheory.ThinSkeleton.skeletal`：skeletal : Skeletal (ThinSkeleton 
C)
-/
theorem map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  Functor.eq_of_iso skeletal
    { hom := mapNatTrans h.hom
      inv := mapNatTrans h.inv }

/--
Applying `fromThinSkeleton`, `F` and then `toThinSkeleton` is isomorphic to applying `map F`.
-/
/-
**CategoryTheory.ThinSkeleton.fromThinSkeletonCompToThinSkeletonIso** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.ThinSkeleton`。
形式化陈述：fromThinSkeletonCompToThinSkeletonIso (F : C ⥤ D) : fromThinSkeleton C ⋙ F
 ⋙ toThinSkeleton D ≅ map F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `fromThinSkeleton`, `F` and then `toThinSkeleton` is isomorphic to appl
ying `map F`.
-/
noncomputable def fromThinSkeletonCompToThinSkeletonIso (F : C ⥤ D) :
    fromThinSkeleton C ⋙ F ⋙ toThinSkeleton D ≅ map F :=
  Functor.isoWhiskerLeft (fromThinSkeleton C) (Iso.refl _) ≪≫
    Functor.isoWhiskerRight (equivalence C).unitIso.symm (map F) ≪≫
    Functor.leftUnitor (map F)

/--
Applying `map F` and then `fromThinSkeleton` is isomorphic to first applying `fromThinSkeleton`
and then applying `F`.
-/
/-
**CategoryTheory.ThinSkeleton.mapCompFromThinSkeletonIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ThinSkeleton`。
形式化陈述：mapCompFromThinSkeletonIso [Quiver.IsThin D] (F : C ⥤ D) : map F ⋙ fromThi
nSkeleton D ≅ fromThinSkeleton C ⋙ F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `map F` and then `fromThinSkeleton` is isomorphic to first applying `fr
omThinSkeleton`
and then applying `F`.
-/
noncomputable def mapCompFromThinSkeletonIso [Quiver.IsThin D] (F : C ⥤ D) :
    map F ⋙ fromThinSkeleton D ≅ fromThinSkeleton C ⋙ F :=
  Functor.isoWhiskerRight (fromThinSkeletonCompToThinSkeletonIso F).symm _ ≪≫
    Functor.isoWhiskerLeft (fromThinSkeleton C ⋙ F) (equivalence D).counitIso ≪≫
    Functor.rightUnitor (fromThinSkeleton C ⋙ F)

/-- `fromThinSkeleton C` exhibits the thin skeleton as a skeleton. -/
/-
**CategoryTheory.ThinSkeleton.thinSkeleton_isSkeleton** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ThinSkeleton`。
形式化陈述：thinSkeleton_isSkeleton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleto
n C) where skel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ThinSkeleton.skeletal`：skeletal : Skeletal (ThinSkeleton 
C)

--- 原说明 ---
`fromThinSkeleton C` exhibits the thin skeleton as a skeleton.
-/
lemma thinSkeleton_isSkeleton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  skel := skeletal
/-
**CategoryTheory.ThinSkeleton.isSkeletonOfInhabited** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.ThinSkeleton`。
形式化陈述：isSkeletonOfInhabited : Inhabited (IsSkeletonOf C (ThinSkeleton C) (fromTh
inSkeleton C))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ThinSkeleton.thinSkeleton_isSkeleton`：thinSkeleton_isSkel
eton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where skel
-/
instance isSkeletonOfInhabited :
    Inhabited (IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C)) :=
  ⟨thinSkeleton_isSkeleton⟩

end

variable {C}

/-- An adjunction between thin categories gives an adjunction between their thin skeletons. -/
/-
**CategoryTheory.ThinSkeleton.lowerAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ThinSkeleton`。
形式化陈述：lowerAdjunction (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) : ThinSkeleton.map L ⊣
 ThinSkeleton.map R where unit
参数：R : D ⥤ C；L : C ⥤ D；h : L ⊣ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An adjunction between thin categories gives an adjunction between their thin ske
letons.
-/
def lowerAdjunction (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) :
    ThinSkeleton.map L ⊣ ThinSkeleton.map R where
  unit :=
    { app := fun X => by
        letI := isIsomorphicSetoid C
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.unit.app x⟩ }
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
  counit :=
    { app := fun X => by
        letI := isIsomorphicSetoid D
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.counit.app x⟩ }

end ThinSkeleton

open ThinSkeleton

section

variable {C} {α : Type*} [PartialOrder α]

/--
When `e : C ≌ α` is a categorical equivalence from a thin category `C` to some partial order `α`,
the `ThinSkeleton C` is order isomorphic to `α`.
-/
/-
**CategoryTheory.Equivalence.thinSkeletonOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {α : T
ype u_1} → [inst_1 : PartialOrder α] → [Quiver.IsThin C] → (C ≌ α) → CategoryThe
ory.ThinSkeleton C ≃o α
参数：C ≌ α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `e : C ≌ α` is a categorical equivalence from a thin category `C` to some p
artial order `α`,
the `ThinSkeleton C` is order isomorphic to `α`.
-/
noncomputable def Equivalence.thinSkeletonOrderIso [Quiver.IsThin C] (e : C ≌ α) :
    ThinSkeleton C ≃o α :=
  ((ThinSkeleton.equivalence C).trans e).toOrderIso

end

end CategoryTheory

