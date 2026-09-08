/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The homotopy category of fibrant objects

Let `C` be a model category. By using the left homotopy relation,
we introduce the homotopy category `FibrantObject.HoCat C` of fibrant objects
in `C`, and we define a fibrant resolution functor
`FibrantObject.HoCat.resolution : C ⥤ FibrantObject.HoCat C`.

This file was obtained by dualizing the definitions in
`Mathlib/AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace FibrantObject

variable (C) in
/-- The left homotopy relation on the category of fibrant objects. -/
/-
**HomotopicalAlgebra.FibrantObject.homRel** 是 Mathlib 中的一个定义，位于命名空间 `Homotopical
Algebra.FibrantObject`。
形式化陈述：homRel : HomRel (FibrantObject C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homotopy relation on the category of fibrant objects.
-/
def homRel : HomRel (FibrantObject C) :=
  fun _ _ f g ↦ LeftHomotopyRel f.hom g.hom
/-
**HomotopicalAlgebra.FibrantObject.homRel_iff_leftHomotopyRel** 是 Mathlib 中的一个引理
，位于命名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} : homRel 
C f g ↔ LeftHomotopyRel f.hom g.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma homRel_iff_leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := Iff.rfl
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _
/-
**HomotopicalAlgebra.FibrantObject.homRel_equivalence_of_isCofibrant_src** 是 Mat
hlib 中的一个引理，位于命名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：homRel_equivalence_of_isCofibrant_src {X Y : FibrantObject C} [IsCofibrant
 X.obj] : Equivalence (homRel C (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Equivalence.comap`：Equivalence.comap (h : Equivalence r) (f : α -> β) : 
Equivalence (r on f)
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.equivalence`：equivalence [ModelCatego
ry C] (X Y : C) [IsCofibrant X] : _root_.Equivalence (LeftHomotopyRel (X
-/
lemma homRel_equivalence_of_isCofibrant_src {X Y : FibrantObject C} [IsCofibrant X.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (LeftHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) ↦ f.hom)

variable (C) in
/-- The homotopy category of fibrant objects. -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopica
lAlgebra.FibrantObject`。
形式化陈述：HoCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy category of fibrant objects.
-/
abbrev HoCat := Quotient (FibrantObject.homRel C)

/-- The quotient functor from the category of fibrant objects to its
homotopy category. -/
/-
**HomotopicalAlgebra.FibrantObject.toHoCat** 是 Mathlib 中的一个定义，位于命名空间 `Homotopica
lAlgebra.FibrantObject`。
形式化陈述：toHoCat : FibrantObject C ⥤ HoCat C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient functor from the category of fibrant objects to its
homotopy category.
-/
def toHoCat : FibrantObject C ⥤ HoCat C := Quotient.functor _
/-
**HomotopicalAlgebra.FibrantObject.toHoCat_obj_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：toHoCat_obj_surjective : Function.Surjective (toHoCat (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance
/-
**HomotopicalAlgebra.FibrantObject.toHoCat_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `Hom
otopicalAlgebra.FibrantObject`。
形式化陈述：toHoCat_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y} (h : homRel C f g) : 
toHoCat.map f = toHoCat.map g
参数：h : homRel C f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
lemma toHoCat_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h
/-
**HomotopicalAlgebra.FibrantObject.toHoCat_map_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.FibrantObject`。
形式化陈述：toHoCat_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ 
Y) : toHoCat.map f = toHoCat.map g ↔ homRel C f g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.homRel_iff`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen`：functor_ho
mRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) : (functor r).homRel f g ↔ Re
lation.EqvGen (@HomRel.CompClosure C _ r X Y) f g
· 使用定理 `CategoryTheory.HomRel.compClosure_eq_self`：compClosure_eq_self : CompClo
sure r = r
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsStableUnderPrecompHomRel`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlg
ebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsStableUnderPostcompHomRel`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAl
gebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `Equivalence.eqvGen_eq`：Equivalence.eqvGen_eq (h : Equivalence r) : EqvGe
n r = r
· 使用引理 `HomotopicalAlgebra.FibrantObject.homRel_equivalence_of_isCofibrant_src`：
homRel_equivalence_of_isCofibrant_src {X Y : FibrantObject C} [IsCofibrant X.obj
] : Equivalence (homRel C (X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toHoCat_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    HomRel.compClosure_eq_self, homRel_equivalence_of_isCofibrant_src.eqvGen_eq]
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (weakEquivalences (FibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithWeakEquivalences (FibrantObject.HoCat C) where
  weakEquivalences := (weakEquivalences _).quotient _
/-
**HomotopicalAlgebra.FibrantObject.weakEquivalence_toHoCat_map_iff** 是 Mathlib 中
的一个引理，位于命名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：weakEquivalence_toHoCat_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) : Weak
Equivalence (toHoCat.map f) ↔ WeakEquivalence f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.quotient_iff`：quotient_iff {X Y : C} (f 
: X ⟶ Y) : W.quotient homRel ((Quotient.functor homRel).map f) ↔ W f
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsStableUnderPrecompHomRel`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlg
ebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsStableUnderPostcompHomRel`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAl
gebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instHasQuotientWeakEquivalencesHomRel`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C],   (HomotopicalAlgebra.weakEqui…
-/
lemma weakEquivalence_toHoCat_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toHoCat.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/-- The functor `FibrantObject C ⥤ HoCat C`, considered as a localizer morphism. -/
/-
**HomotopicalAlgebra.FibrantObject.toHoCatLocalizerMorphism** 是 Mathlib 中的一个定义，位
于命名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：toHoCatLocalizerMorphism : LocalizerMorphism (weakEquivalences (FibrantObj
ect C)) (weakEquivalences (FibrantObject.HoCat C)) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `FibrantObject C ⥤ HoCat C`, considered as a localizer morphism.
-/
def toHoCatLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (FibrantObject C))
      (weakEquivalences (FibrantObject.HoCat C)) where
  functor := toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

variable (C) in
/-
**HomotopicalAlgebra.FibrantObject.factorsThroughLocalization** 是 Mathlib 中的一个引理
，位于命名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：factorsThroughLocalization : (homRel C).FactorsThroughLocalization (weakEq
uivalences (FibrantObject C))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.exists_very_good_cylinder`：exists_ver
y_good_cylinder [ModelCategory C] {f g : X ⟶ Y} [IsFibrant Y] (h : LeftHomotopyR
el f g) : exists (P : Cylinder X), P.IsVeryGood ∧ …
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsFibrantObjFibrantObjects`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.C
ategoryWithFibrations C]   [inst_2 : CategoryTheory.L…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.areEqualizedByLocalization_iff`：areEqualizedByLocalizatio
n_iff [L.IsLocalization W] : AreEqualizedByLocalization W f g ↔ L.map f = L.map 
g
· 使用定理 `HomotopicalAlgebra.Cylinder.instIsFibrantIOfIsVeryGood`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C] (P : Homotop…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeFibrations`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWea
kEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemTrivialCof
ibrationsFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.trivialCofibr
a…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomotopicalAlgebra.Cylinder.weakEquivalence_π`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakEqu
ivalences C]   {A : C} (self : Homo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₀_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.Precylinder.i₁_π`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.Precylinder A),   Categ
oryTheory.CategoryStruct.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 33 条，此处仅展示前 30 条）
-/
lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (FibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_cylinder
  let L := (weakEquivalences (FibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.i₀) = L.map (homMk P.i₁) by
    simp only [show f = homMk P.i₀ ≫ homMk h.h by cat_disch,
      show g = homMk P.i₁ ≫ homMk h.h by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.π) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp [← cancel_mono (L.map (homMk P.π)), ← L.map_comp]
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toHoCatLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : FibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toHoCat ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((toHoCatLocalizerMorphism C).functor ⋙ L).IsLocalization _)
/-
**HomotopicalAlgebra.FibrantObject.HoCat.exists_resolution** 是 Mathlib 中的一个定理，位于
命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] (X : C),   ∃ X',     ∃ (_ : HomotopicalAlgebr
a.IsFibrant X'),       ∃ i, HomotopicalAlgebra.Cofibration i ∧ HomotopicalAlgebr
a.WeakEquivalence i
参数：X : C；_ : HomotopicalAlgebra.IsFibrant X'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.trivialCofibrati…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.isFibrant_iff_of_isTerminal`：isFibrant_iff_of_isTermi
nal [(fibrations C).RespectsIso] {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) : IsF
ibrant X ↔ Fibration p
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoOfIsStableUnderRetracts`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [P.IsStableUnderRetracts], P.RespectsIso
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm3b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.fibrations C).Is…
· 使用定理 `HomotopicalAlgebra.instFibrationPTrivialCofibrationsFibrations`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.instCofibrationITrivialCofibrationsFibrations`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceITrivialCofibrationsFibrations`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
-/
lemma HoCat.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsFibrant X') (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
  infer_instance

/-- Given `X : C`, this is a fibrant object `X'` equipped with a
trivial cofibration `X ⟶ X'` (see `HoCat.iResolutionObj`). -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.resolutionObj** 是 Mathlib 中的一个定义，位于命名空间
 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → [Homotopi
calAlgebra.ModelCategory C] → C → C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.FibrantObject.HoCat.exists_resolution`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.Mo
delCategory C] (X : C),   ∃ X',     ∃ (_ : Hom…

--- 原说明 ---
Given `X : C`, this is a fibrant object `X'` equipped with a
trivial cofibration `X ⟶ X'` (see `HoCat.iResolutionObj`).
-/
noncomputable def HoCat.resolutionObj (X : C) : C :=
    (exists_resolution X).choose
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : IsFibrant (HoCat.resolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose

/-- This is a trivial cofibration `X ⟶ resolutionObj X` where
`resolutionObj X` is a choice of a fibrant resolution of `X`. -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj** 是 Mathlib 中的一个定义，位于命名空
间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] → (X : C) → X ⟶ HomotopicalAlgebra.Fi
brantObject.HoCat.resolutionObj X
参数：X : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.FibrantObject.HoCat.exists_resolution`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.Mo
delCategory C] (X : C),   ∃ X',     ∃ (_ : Hom…

--- 原说明 ---
This is a trivial cofibration `X ⟶ resolutionObj X` where
`resolutionObj X` is a choice of a fibrant resolution of `X`.
-/
noncomputable def HoCat.iResolutionObj (X : C) : X ⟶ resolutionObj X :=
  (exists_resolution X).choose_spec.choose_spec.choose
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Cofibration (HoCat.iResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : WeakEquivalence (HoCat.iResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [IsCofibrant X] : IsCofibrant (HoCat.resolutionObj X) :=
  isCofibrant_of_cofibration (HoCat.iResolutionObj X)
/-
**HomotopicalAlgebra.FibrantObject.HoCat.exists_resolution_map** 是 Mathlib 中的一个定
理，位于命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   ∃ g,     CategoryT
heory.CategoryStruct.comp (HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj
 X) g =       CategoryTheory.CategoryStruct.comp f (HomotopicalAlgebra.FibrantOb
ject.HoCat.iResolutionObj Y)
参数：f : X ⟶ Y；HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj X；Homotopical
Algebra.FibrantObject.HoCat.iResolutionObj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instCofibrationIResolutionObj`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] (X : C),   HomotopicalAlgebra.C…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instWeakEquivalenceIResolutionObj`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopical
Algebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsFibrantResolutionObj`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra
.ModelCategory C] (X : C),   HomotopicalAlgebra.I…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
-/
lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      iResolutionObj X ≫ g = f ≫ iResolutionObj Y := by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- A lifting of a morphism `f : X ⟶ Y` on fibrant resolutions.
(This is functorial only up to homotopy, see `HoCat.resolution`.) -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.resolutionMap** 是 Mathlib 中的一个定义，位于命名空间
 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {X Y : C} →         (X ⟶ Y) →
           (HomotopicalAlgebra.FibrantObject.HoCat.resolutionObj X ⟶            
 HomotopicalAlgebra.FibrantObject.HoCat.resolutionObj Y)
参数：X ⟶ Y；HomotopicalAlgebra.FibrantObject.HoCat.resolutionObj X ⟶             Ho
motopicalAlgebra.FibrantObject.HoCat.resolutionObj Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.FibrantObject.HoCat.exists_resolution_map`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebr
a.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   ∃ g,…

--- 原说明 ---
A lifting of a morphism `f : X ⟶ Y` on fibrant resolutions.
(This is functorial only up to homotopy, see `HoCat.resolution`.)
-/
noncomputable def HoCat.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.FibrantObject.HoCat.resolutionMap_fac** 是 Mathlib 中的一个定理，位于
命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   CategoryTheory.Cat
egoryStruct.comp (HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj X)      
 (HomotopicalAlgebra.FibrantObject.HoCat.resolutionMap f) =     CategoryTheory.C
ategoryStruct.comp f (HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj Y)
参数：f : X ⟶ Y；HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj X；Homotopical
Algebra.FibrantObject.HoCat.resolutionMap f；HomotopicalAlgebra.FibrantObject.HoC
at.iResolutionObj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `HomotopicalAlgebra.FibrantObject.HoCat.exists_resolution_map`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebr
a.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   ∃ g,…
-/
lemma HoCat.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    iResolutionObj X ≫ resolutionMap f =
      f ≫ iResolutionObj Y :=
  (exists_resolution_map f).choose_spec

@[simp]
/-
**HomotopicalAlgebra.FibrantObject.HoCat.weakEquivalence_resolutionMap_iff** 是 M
athlib 中的一个定理，位于命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   HomotopicalAlgebra
.WeakEquivalence (HomotopicalAlgebra.FibrantObject.HoCat.resolutionMap f) ↔     
HomotopicalAlgebra.WeakEquivalence f
参数：f : X ⟶ Y；HomotopicalAlgebra.FibrantObject.HoCat.resolutionMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.weakEquivalence_precomp_iff`：weakEquivalence_precomp_
iff [WeakEquivalence f] : WeakEquivalence (f ≫ g) ↔ WeakEquivalence g
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instWeakEquivalenceIResolutionObj`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopical
Algebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
· 使用定理 `HomotopicalAlgebra.FibrantObject.HoCat.resolutionMap_fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.Mo
delCategory C] {X Y : C}   (f : X ⟶ Y),   Cate…
· 使用引理 `HomotopicalAlgebra.weakEquivalence_postcomp_iff`：weakEquivalence_postcom
p_iff [WeakEquivalence g] : WeakEquivalence (f ≫ g) ↔ WeakEquivalence f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma HoCat.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_precomp_iff (iResolutionObj X),
    HoCat.resolutionMap_fac, weakEquivalence_postcomp_iff]
/-
**HomotopicalAlgebra.FibrantObject.HoCat.resolutionObj_hom_ext** 是 Mathlib 中的一个定
理，位于命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   [inst_2 : HomotopicalAlgebra.IsFi
brant Y] {f g : HomotopicalAlgebra.FibrantObject.HoCat.resolutionObj X ⟶ Y},   H
omotopicalAlgebra.RightHomotopyRel       (CategoryTheory.CategoryStruct.comp (Ho
motopicalAlgebra.FibrantObject.HoCat.iResolutionObj X) f)       (CategoryTheory.
CategoryStruct.comp (HomotopicalAlgebra.FibrantObject.HoCat.iResolutionObj X) g)
 →     HomotopicalAlgebra.FibrantObject.toHoCat.map (HomotopicalAlgebra.FibrantO
bject.homMk f) =       HomotopicalAlgebra.FibrantObject.toHoCat.map (Homotopical
Algebra.FibrantObject.homMk g)
参数：CategoryTheory.CategoryStruct.comp (HomotopicalAlgebra.FibrantObject.HoCat.iR
esolutionObj X) f；CategoryTheory.CategoryStruct.comp (HomotopicalAlgebra.Fibrant
Object.HoCat.iResolutionObj X) g；HomotopicalAlgebra.FibrantObject.homMk f；Homoto
picalAlgebra.FibrantObject.homMk g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `HomotopicalAlgebra.FibrantObject.toHoCat_map_eq`：toHoCat_map_eq {X Y : F
ibrantObject C} {f g : X ⟶ Y} (h : homRel C f g) : toHoCat.map f = toHoCat.map g
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsFibrantResolutionObj`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra
.ModelCategory C] (X : C),   HomotopicalAlgebra.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.FibrantObject.homRel_iff_leftHomotopyRel`：homRel_iff_
leftHomotopyRel {X Y : FibrantObject C} {f g : X ⟶ Y} : homRel C f g ↔ LeftHomot
opyRel f.hom g.hom
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.leftHomotopyRel`：leftHomotopyRel (h 
: RightHomotopyRel f g) : LeftHomotopyRel f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelC
ategory C] [IsFibrant Y] (f g : X ⟶ Y) : mk f = mk g ↔ RightHomotopyRel f g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_cofibration_o
f_weakEquivalence`：precomp_bijective_of_cofibration_of_weakEquivalence [IsFibran
t Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] : Function.Bijective (fun …
· 使用定理 `HomotopicalAlgebra.FibrantObject.instCofibrationIResolutionObj`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] (X : C),   HomotopicalAlgebra.C…
· 使用定理 `HomotopicalAlgebra.FibrantObject.instWeakEquivalenceIResolutionObj`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopical
Algebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
-/
lemma HoCat.resolutionObj_hom_ext {X Y : C} [IsFibrant Y] {f g : resolutionObj X ⟶ Y}
    (h : RightHomotopyRel (iResolutionObj X ≫ f) (iResolutionObj X ≫ g)) :
    toHoCat.map (homMk f) = toHoCat.map (homMk g) := by
  apply toHoCat_map_eq
  rw [homRel_iff_leftHomotopyRel]
  apply RightHomotopyRel.leftHomotopyRel
  rw [← RightHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    (f := iResolutionObj X) (Z := Y)).1 h

/-- A fibrant resolution functor from a model category to the homotopy category
of fibrant objects. -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.resolution** 是 Mathlib 中的一个定义，位于命名空间 `H
omotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] → CategoryTheory.Functor C (Homotopic
alAlgebra.FibrantObject.HoCat C)
参数：HomotopicalAlgebra.FibrantObject.HoCat C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.FibrantObject.instIsFibrantResolutionObj`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra
.ModelCategory C] (X : C),   HomotopicalAlgebra.I…

--- 原说明 ---
A fibrant resolution functor from a model category to the homotopy category
of fibrant objects.
-/
noncomputable def HoCat.resolution : C ⥤ FibrantObject.HoCat C where
  obj X := toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The fibrant resolution functor `HoCat.resolution`, as a localizer morphism. -/
@[simps]
/-
**HomotopicalAlgebra.FibrantObject.HoCat.localizerMorphismResolution** 是 Mathlib
 中的一个定义，位于命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.LocalizerMorph
ism (HomotopicalAlgebra.weakEquivalences C)         (HomotopicalAlgebra.weakEqui
valences (HomotopicalAlgebra.FibrantObject.HoCat C))
参数：HomotopicalAlgebra.FibrantObject.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fibrant resolution functor `HoCat.resolution`, as a localizer morphism.
-/
noncomputable def HoCat.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (FibrantObject.HoCat C)) where
  functor := HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `HoCat.iResolutionObj`, when applied to already fibrant objects, gives
a natural transformation `toHoCat ⟶ ι ⋙ HoCat.resolution`. -/
@[simps]
/-
**HomotopicalAlgebra.FibrantObject.HoCat.** 是 Mathlib 中的一个定义，位于命名空间 `Homotopical
Algebra.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `HoCat.iResolutionObj`, when applied to already fibrant objects, gives
a natural transformation `toHoCat ⟶ ι ⋙ HoCat.resolution`.
-/
noncomputable def HoCat.ιCompResolutionNatTrans : toHoCat ⟶ ι ⋙ HoCat.resolution (C := C) where
  app X := toHoCat.map { hom := (HoCat.iResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact (HoCat.resolutionMap_fac f.hom).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FibrantObject C) :
    WeakEquivalence (HoCat.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toHoCat_map_iff, weakEquivalence_iff_of_objectProperty]
  infer_instance
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : FibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (Functor.whiskerRight HoCat.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- The induced functor `FibrantObject.HoCat C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences. -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.toLocalization** 是 Mathlib 中的一个定义，位于命名空
间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {D : Type u_2} →         [ins
t_2 : CategoryTheory.Category.{v_2, u_2} D] →           (L : CategoryTheory.Func
tor C D) →             [L.IsLocalization (HomotopicalAlgebra.weakEquivalences C)
] →               CategoryTheory.Functor (HomotopicalAlgebra.FibrantObject.HoCat
 C) D
参数：L : CategoryTheory.Functor C D；HomotopicalAlgebra.weakEquivalences C；Homotopi
calAlgebra.FibrantObject.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced functor `FibrantObject.HoCat C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences.
-/
def HoCat.toLocalization : HoCat C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h ↦ (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ ↦ Localization.inverts L (weakEquivalences _) _))

/-- The isomorphism `toHoCat ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of fibrant objects factors through the homotopy category
of fibrant objects. -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.toHoCatCompToLocalizationIso** 是 Mathli
b 中的一个定义，位于命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {D : Type u_2} →         [ins
t_2 : CategoryTheory.Category.{v_2, u_2} D] →           (L : CategoryTheory.Func
tor C D) →             [inst_3 : L.IsLocalization (HomotopicalAlgebra.weakEquiva
lences C)] →               HomotopicalAlgebra.FibrantObject.toHoCat.comp (Homoto
picalAlgebra.FibrantObject.HoCat.toLocalization L) ≅                 Homotopical
Algebra.FibrantObject.ι.comp L
参数：L : CategoryTheory.Functor C D；HomotopicalAlgebra.weakEquivalences C；Homotopi
calAlgebra.FibrantObject.HoCat.toLocalization L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `toHoCat ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of fibrant objects factors through the homotopy category
of fibrant objects.
-/
def HoCat.toHoCatCompToLocalizationIso : toHoCat ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

/-- The natural isomorphism `L ⟶ HoCat.resolution ⋙ HoCat.toLocalization L` when
`L : C ⥤ D` is a localization functor. -/
/-
**HomotopicalAlgebra.FibrantObject.HoCat.resolutionCompToLocalizationNatTrans** 
是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra.FibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {D : Type u_2} →         [ins
t_2 : CategoryTheory.Category.{v_2, u_2} D] →           (L : CategoryTheory.Func
tor C D) →             [inst_3 : L.IsLocalization (HomotopicalAlgebra.weakEquiva
lences C)] →               L ⟶                 HomotopicalAlgebra.FibrantObject.
HoCat.resolution.comp                   (HomotopicalAlgebra.FibrantObject.HoCat.
toLocalization L)
参数：L : CategoryTheory.Functor C D；HomotopicalAlgebra.weakEquivalences C；Homotopi
calAlgebra.FibrantObject.HoCat.toLocalization L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `L ⟶ HoCat.resolution ⋙ HoCat.toLocalization L` when
`L : C ⥤ D` is a localization functor.
-/
noncomputable def HoCat.resolutionCompToLocalizationNatTrans :
    L ⟶ HoCat.resolution ⋙ HoCat.toLocalization L where
  app X := L.map (iResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f).symm

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (HoCat.resolutionCompToLocalizationNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

end

variable (C) in
/-- The inclusion `FibrantObject C ⥤ C`, as a localizer morphism. -/
@[simps]
/-
**HomotopicalAlgebra.FibrantObject.localizerMorphism** 是 Mathlib 中的一个定义，位于命名空间 `
HomotopicalAlgebra.FibrantObject`。
形式化陈述：localizerMorphism : LocalizerMorphism (weakEquivalences (FibrantObject C))
 (weakEquivalences C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `FibrantObject C ⥤ C`, as a localizer morphism.
-/
def localizerMorphism : LocalizerMorphism (weakEquivalences (FibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

open Functor in
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hfib := (weakEquivalences (HoCat C)).Localization
  let Lfibπ : HoCat C ⥤ Hfib := (weakEquivalences (FibrantObject.HoCat C)).Q
  let Lfib : FibrantObject C ⥤ Hfib := toHoCat ⋙ Lfibπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lfib L
  let eF : ι ⋙ L ≅ Lfib ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lfib L F
  let eF' : HoCat.toLocalization L ≅ Lfibπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hfib := (HoCat.localizerMorphismResolution C).localizedFunctor L Lfibπ
  let eG : HoCat.resolution ⋙ Lfibπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lfibπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lfib (weakEquivalences (FibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lfibπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hfib ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lfib (weakEquivalences _) Lfib (ι ⋙ HoCat.resolution ⋙ Lfibπ) _ _
        (asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lfibπ) ≪≫ associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)).symm)
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lfib L F

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FibrantObject C) :
    IsFibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (FibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end FibrantObject

end HomotopicalAlgebra

