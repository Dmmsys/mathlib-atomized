/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
public import Mathlib.CategoryTheory.Quotient.LocallySmall

/-!
# The homotopy category of bifibrant objects

We construct the homotopy category `BifibrantObject.HoCat C` of bifibrant
objects in a model category `C` and show that the functor
`BifibrantObject.toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`
is a localization functor with respect to weak equivalences.
We also show that certain localizer morphisms are localized weak equivalences,
which can be understood by saying that we obtain the same localized
category (up to equivalence) by inverting weak equivalences in `C`,
`CofibrantObject C`, `FibrantObject C` or `BifibrantObject C`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

namespace BifibrantObject

variable (C) in
/-- The homotopy relation on the category of bifibrant objects. -/
/-
**HomotopicalAlgebra.BifibrantObject.homRel** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
形式化陈述：homRel : HomRel (BifibrantObject C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy relation on the category of bifibrant objects.
-/
def homRel : HomRel (BifibrantObject C) :=
  fun _ _ f g ↦ RightHomotopyRel f.hom g.hom
/-
**HomotopicalAlgebra.BifibrantObject.homRel_iff_rightHomotopyRel** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：homRel_iff_rightHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} : homR
el C f g ↔ RightHomotopyRel f.hom g.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma homRel_iff_rightHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel f.hom g.hom := Iff.rfl
/-
**HomotopicalAlgebra.BifibrantObject.homRel_iff_leftHomotopyRel** 是 Mathlib 中的一个
引理，位于命名空间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：homRel_iff_leftHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} : homRe
l C f g ↔ LeftHomotopyRel f.hom g.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.BifibrantObject.homRel_iff_rightHomotopyRel`：homRel_i
ff_rightHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} : homRel C f g ↔ Rig
htHomotopyRel f.hom g.hom
· 使用引理 `HomotopicalAlgebra.leftHomotopyRel_iff_rightHomotopyRel`：leftHomotopyRel
_iff_rightHomotopyRel : LeftHomotopyRel f g ↔ RightHomotopyRel f g
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsCofibrantObjBifibrantObjects`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlg
ebra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsFibrantObjBifibrantObjects`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgeb
ra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma homRel_iff_leftHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ LeftHomotopyRel f.hom g.hom := by
  rw [homRel_iff_rightHomotopyRel, leftHomotopyRel_iff_rightHomotopyRel]
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Congruence (homRel C) where
  equivalence :=
    { refl _ := .refl _
      symm h := .symm h
      trans h₁ h₂ := .trans h₁ h₂ }

variable (C) in
/-- The homotopy category of bifibrant objects. -/
/-
**HomotopicalAlgebra.BifibrantObject.HoCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopi
calAlgebra.BifibrantObject`。
形式化陈述：HoCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy category of bifibrant objects.
-/
abbrev HoCat := Quotient (BifibrantObject.homRel C)

/-- The quotient functor from the category of bifibrant objects to its
homotopy category. -/
@[implicit_reducible]
/-
**HomotopicalAlgebra.BifibrantObject.toHoCat** 是 Mathlib 中的一个定义，位于命名空间 `Homotopi
calAlgebra.BifibrantObject`。
形式化陈述：toHoCat : BifibrantObject C ⥤ HoCat C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient functor from the category of bifibrant objects to its
homotopy category.
-/
def toHoCat : BifibrantObject C ⥤ HoCat C := Quotient.functor _
/-
**HomotopicalAlgebra.BifibrantObject.toHoCat_obj_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：toHoCat_obj_surjective : Function.Surjective (toHoCat (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
-/
lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance
/-
**HomotopicalAlgebra.BifibrantObject.toHoCat_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopicalAlgebra.BifibrantObject`。
形式化陈述：toHoCat_map_eq {X Y : BifibrantObject C} {f g : X ⟶ Y} (h : homRel C f g) 
: toHoCat.map f = toHoCat.map g
参数：h : homRel C f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
lemma toHoCat_map_eq {X Y : BifibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h
/-
**HomotopicalAlgebra.BifibrantObject.toHoCat_map_eq_iff** 是 Mathlib 中的一个引理，位于命名空
间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：toHoCat_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) : toHoCat.map f
 = toHoCat.map g ↔ homRel C f g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `CategoryTheory.Quotient.functor_map_eq_iff`：functor_map_eq_iff [h : Cong
ruence r] {X Y : C} (f f' : X ⟶ Y) : (functor r).map f = (functor r).map f' ↔ r 
f f'
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instCongruenceHomRel`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCate
gory C],   CategoryTheory.Congruence (Homotop…
-/
lemma toHoCat_map_eq_iff {X Y : BifibrantObject C} (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g :=
  Quotient.functor_map_eq_iff _ _ _
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] : LocallySmall.{w} (HoCat C) := by
  dsimp [HoCat]
  infer_instance

section

variable {D : Type*} [Category* D]

/-
**HomotopicalAlgebra.BifibrantObject.inverts_iff_factors** 是 Mathlib 中的一个引理，位于命名
空间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：inverts_iff_factors (F : BifibrantObject C ⥤ D) : (weakEquivalences _).IsI
nvertedBy F ↔ forall ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L), homRel C f g -> F.
map f = F.map g
参数：F : BifibrantObject C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_very_good_pathObject`：exists_
very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightH
omotopyRel f g) : exists (P : PathObject Y), P.IsVery…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsCofibrantObjBifibrantObjects`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlg
ebra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用引理 `HomotopicalAlgebra.isCofibrant_of_cofibration`：isCofibrant_of_cofibratio
n [(cofibrations C).IsStableUnderComposition] {X Y : C} (i : X ⟶ Y) [Cofibration
 i] [hX : IsCofibrant X] : IsCofibr…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeCofibrations`：∀ (C : Type u) [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithW
eakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemCofibratio
nsTrivialFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.cofibrations 
C…
· 使用定理 `HomotopicalAlgebra.PathObject.IsVeryGood.cofibration_ι`：∀ {C : Type u} {
inst : CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsFibrantObjBifibrantObjects`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgeb
ra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `HomotopicalAlgebra.PathObject.instIsFibrantP`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlgebra.CategoryWi
thWeakEquivalences C] (P : Homotop…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeFibrations`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWea
kEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemTrivialCof
ibrationsFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.trivialCofibr
a…
· 使用定理 `HomotopicalAlgebra.instIsStableUnderBaseChangeFibrations`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Category
WithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.PathObject.IsVeryGood.toIsGood`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Categ
oryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用引理 `HomotopicalAlgebra.weakEquivalence_iff_of_objectProperty`：weakEquivalenc
e_iff_of_objectProperty {X Y : P.FullSubcategory} (f : X ⟶ Y) : WeakEquivalence 
f ↔ WeakEquivalence f.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₁`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
（共 36 条，此处仅展示前 30 条）
-/
lemma inverts_iff_factors (F : BifibrantObject C ⥤ D) :
    (weakEquivalences _).IsInvertedBy F ↔
    ∀ ⦃K L : BifibrantObject C⦄ (f g : K ⟶ L),
      homRel C f g → F.map f = F.map g := by
  refine ⟨fun H K L f g h ↦ ?_, fun h X Y f hf ↦ ?_⟩
  · obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
    have := isCofibrant_of_cofibration P.ι
    have : IsIso (F.map (homMk P.ι)) := H _ (by
      rw [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
      exact inferInstanceAs (WeakEquivalence P.ι))
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp]
    congr 1
    simp [← cancel_epi (F.map (homMk P.ι)), ← Functor.map_comp]
  · rw [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty] at hf
    obtain ⟨g', h₁, h₂⟩ := RightHomotopyClass.whitehead f.hom
    refine ⟨F.map (homMk g'), ?_, ?_⟩
    all_goals
      rw [← F.map_comp, ← F.map_id]
      apply h
      assumption

/-- The strict universal property of the localization with respect
to weak equivalences for the quotient functor
`toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.strictUniversalPropertyFixedTargetToHoCat**
 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：strictUniversalPropertyFixedTargetToHoCat : Localization.StrictUniversalPr
opertyFixedTarget toHoCat (weakEquivalences (BifibrantObject C)) D where inverts
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strict universal property of the localization with respect
to weak equivalences for the quotient functor
`toHoCat : BifibrantObject C ⥤ BifibrantObject.HoCat C`.
-/
def strictUniversalPropertyFixedTargetToHoCat :
    Localization.StrictUniversalPropertyFixedTarget
      toHoCat (weakEquivalences (BifibrantObject C)) D where
  inverts := by
    rw [inverts_iff_factors]
    intro K L f g h
    exact CategoryTheory.Quotient.sound _ h
  lift F hF := CategoryTheory.Quotient.lift _ F
    (by rwa [inverts_iff_factors] at hF)
  fac F hF := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end

/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : toHoCat.IsLocalization (weakEquivalences (BifibrantObject C)) :=
  .mk' _ _ strictUniversalPropertyFixedTargetToHoCat
    strictUniversalPropertyFixedTargetToHoCat
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : BifibrantObject C} (f : X ⟶ Y) [hf : WeakEquivalence f] :
    IsIso (toHoCat.map f) :=
  Localization.inverts toHoCat (weakEquivalences _) f (by rwa [weakEquivalence_iff] at hf)

section

variable {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]

set_option backward.isDefEq.respectTransparency.types false in
/-- Right homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.HoCat`. -/
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.homEquivRight** 是 Mathlib 中的一个定义，位于命名
空间 `HomotopicalAlgebra.BifibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       {X Y : C} →         [inst_2 : Homot
opicalAlgebra.IsCofibrant X] →           [inst_3 : HomotopicalAlgebra.IsCofibran
t Y] →             [inst_4 : HomotopicalAlgebra.IsFibrant X] →               [in
st_5 : HomotopicalAlgebra.IsFibrant Y] →                 HomotopicalAlgebra.Righ
tHomotopyClass X Y ≃                   (HomotopicalAlgebra.BifibrantObject.toHoC
at.obj (HomotopicalAlgebra.BifibrantObject.mk X) ⟶                     Homotopic
alAlgebra.BifibrantObject.toHoCat.obj (HomotopicalAlgebra.BifibrantObject.mk Y))
参数：HomotopicalAlgebra.BifibrantObject.toHoCat.obj (HomotopicalAlgebra.BifibrantO
bject.mk X) ⟶                     HomotopicalAlgebra.BifibrantObject.toHoCat.obj
 (HomotopicalAlgebra.BifibrantObject.mk Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.HoCat`.
-/
def HoCat.homEquivRight :
    RightHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) where
  toFun := Quot.lift (fun f ↦ toHoCat.map (homMk f)) (fun _ _ h ↦ by rwa [toHoCat_map_eq_iff])
  invFun := Quot.lift (fun f ↦ .mk f.hom) (fun _ _ h ↦ by
    simpa [RightHomotopyClass.mk_eq_mk_iff] using! h)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.homEquivRight_apply** 是 Mathlib 中的一个定
理，位于命名空间 `HomotopicalAlgebra.BifibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C] {X Y : C}   [inst_2 : HomotopicalAlgebra.IsCofibran
t X] [inst_3 : HomotopicalAlgebra.IsCofibrant Y]   [inst_4 : HomotopicalAlgebra.
IsFibrant X] [inst_5 : HomotopicalAlgebra.IsFibrant Y] (f : X ⟶ Y),   Homotopica
lAlgebra.BifibrantObject.HoCat.homEquivRight (HomotopicalAlgebra.RightHomotopyCl
ass.mk f) =     HomotopicalAlgebra.BifibrantObject.toHoCat.map (HomotopicalAlgeb
ra.BifibrantObject.homMk f)
参数：f : X ⟶ Y；HomotopicalAlgebra.RightHomotopyClass.mk f；HomotopicalAlgebra.Bifib
rantObject.homMk f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
-/
lemma HoCat.homEquivRight_apply (f : X ⟶ Y) :
    HoCat.homEquivRight (.mk f) = toHoCat.map (homMk f) := rfl

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.homEquivRight_symm_apply** 是 Mathlib 
中的一个定理，位于命名空间 `HomotopicalAlgebra.BifibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C] {X Y : C}   [inst_2 : HomotopicalAlgebra.IsCofibran
t X] [inst_3 : HomotopicalAlgebra.IsCofibrant Y]   [inst_4 : HomotopicalAlgebra.
IsFibrant X] [inst_5 : HomotopicalAlgebra.IsFibrant Y] (f : X ⟶ Y),   Homotopica
lAlgebra.BifibrantObject.HoCat.homEquivRight.symm       (HomotopicalAlgebra.Bifi
brantObject.toHoCat.map (HomotopicalAlgebra.BifibrantObject.homMk f)) =     Homo
topicalAlgebra.RightHomotopyClass.mk f
参数：f : X ⟶ Y；HomotopicalAlgebra.BifibrantObject.toHoCat.map (HomotopicalAlgebra.
BifibrantObject.homMk f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma HoCat.homEquivRight_symm_apply (f : X ⟶ Y) :
    HoCat.homEquivRight.symm (toHoCat.map (homMk f)) = .mk f := rfl

/-- Left homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.HoCat`. -/
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.homEquivLeft** 是 Mathlib 中的一个定义，位于命名空
间 `HomotopicalAlgebra.BifibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       {X Y : C} →         [inst_2 : Homot
opicalAlgebra.IsCofibrant X] →           [inst_3 : HomotopicalAlgebra.IsCofibran
t Y] →             [inst_4 : HomotopicalAlgebra.IsFibrant X] →               [in
st_5 : HomotopicalAlgebra.IsFibrant Y] →                 HomotopicalAlgebra.Left
HomotopyClass X Y ≃                   (HomotopicalAlgebra.BifibrantObject.toHoCa
t.obj (HomotopicalAlgebra.BifibrantObject.mk X) ⟶                     Homotopica
lAlgebra.BifibrantObject.toHoCat.obj (HomotopicalAlgebra.BifibrantObject.mk Y))
参数：HomotopicalAlgebra.BifibrantObject.toHoCat.obj (HomotopicalAlgebra.BifibrantO
bject.mk X) ⟶                     HomotopicalAlgebra.BifibrantObject.toHoCat.obj
 (HomotopicalAlgebra.BifibrantObject.mk Y)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Left homotopy classes of maps between bifibrant objects identify
to morphisms in the homotopy category `BifibrantObject.HoCat`.
-/
def HoCat.homEquivLeft :
    LeftHomotopyClass X Y ≃ (toHoCat.obj (mk X) ⟶ toHoCat.obj (mk Y)) :=
  leftHomotopyClassEquivRightHomotopyClass.trans HoCat.homEquivRight

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.homEquivLeft_apply** 是 Mathlib 中的一个定理
，位于命名空间 `HomotopicalAlgebra.BifibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C] {X Y : C}   [inst_2 : HomotopicalAlgebra.IsCofibran
t X] [inst_3 : HomotopicalAlgebra.IsCofibrant Y]   [inst_4 : HomotopicalAlgebra.
IsFibrant X] [inst_5 : HomotopicalAlgebra.IsFibrant Y] (f : X ⟶ Y),   Homotopica
lAlgebra.BifibrantObject.HoCat.homEquivLeft (HomotopicalAlgebra.LeftHomotopyClas
s.mk f) =     HomotopicalAlgebra.BifibrantObject.toHoCat.map (HomotopicalAlgebra
.BifibrantObject.homMk f)
参数：f : X ⟶ Y；HomotopicalAlgebra.LeftHomotopyClass.mk f；HomotopicalAlgebra.Bifibr
antObject.homMk f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HoCat.homEquivLeft_apply (f : X ⟶ Y) :
    HoCat.homEquivLeft (.mk f) = toHoCat.map (homMk f) := by
  simp [homEquivLeft]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.homEquivLeft_symm_apply** 是 Mathlib 中
的一个定理，位于命名空间 `HomotopicalAlgebra.BifibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C] {X Y : C}   [inst_2 : HomotopicalAlgebra.IsCofibran
t X] [inst_3 : HomotopicalAlgebra.IsCofibrant Y]   [inst_4 : HomotopicalAlgebra.
IsFibrant X] [inst_5 : HomotopicalAlgebra.IsFibrant Y] (f : X ⟶ Y),   Homotopica
lAlgebra.BifibrantObject.HoCat.homEquivRight.symm       (HomotopicalAlgebra.Bifi
brantObject.toHoCat.map (HomotopicalAlgebra.BifibrantObject.homMk f)) =     Homo
topicalAlgebra.RightHomotopyClass.mk f
参数：f : X ⟶ Y；HomotopicalAlgebra.BifibrantObject.toHoCat.map (HomotopicalAlgebra.
BifibrantObject.homMk f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma HoCat.homEquivLeft_symm_apply (f : X ⟶ Y) :
    HoCat.homEquivRight.symm (toHoCat.map (homMk f)) = .mk f := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion functor `BifibrantObject.HoCat C ⥤ FibrantObject.HoCat C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `BifibrantObject.HoCat C ⥤ FibrantObject.HoCat C`.
-/
def HoCat.ιFibrantObject : HoCat C ⥤ FibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιFibrantObject ⋙ FibrantObject.toHoCat) (fun _ _ _ _ h ↦ by
      simpa [FibrantObject.toHoCat_map_eq_iff, FibrantObject.homRel_iff_leftHomotopyRel,
        homRel_iff_leftHomotopyRel] using h)

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HoCat.ιFibrantObject_obj (X : BifibrantObject C) :
    HoCat.ιFibrantObject.obj (toHoCat.obj X) =
      FibrantObject.toHoCat.obj (BifibrantObject.ιFibrantObject.obj X) :=
  rfl

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HoCat.ιFibrantObject_map_toHoCat_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    HoCat.ιFibrantObject.map (toHoCat.map f) =
      FibrantObject.toHoCat.map (FibrantObject.homMk f.hom) :=
  rfl

/-- The isomorphism `toHoCat ⋙ HoCat.ιFibrantObject ≅ ιFibrantObject ⋙ FibrantObject.toHoCat`
between functors `BifibrantObject C ⥤ FibrantObject.HoCat C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.toHoCatComp** 是 Mathlib 中的一个定义，位于命名空间 `Homo
topicalAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `toHoCat ⋙ HoCat.ιFibrantObject ≅ ιFibrantObject ⋙ FibrantObject
.toHoCat`
between functors `BifibrantObject C ⥤ FibrantObject.HoCat C`.
-/
def toHoCatCompιFibrantObject :
    toHoCat (C := C) ⋙ HoCat.ιFibrantObject ≅
      ιFibrantObject ⋙ FibrantObject.toHoCat := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion functor `BifibrantObject.HoCat C ⥤ CofibrantObject.HoCat C`. -/
@[implicit_reducible]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `BifibrantObject.HoCat C ⥤ CofibrantObject.HoCat C`.
-/
def HoCat.ιCofibrantObject : HoCat C ⥤ CofibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _
    (BifibrantObject.ιCofibrantObject ⋙ CofibrantObject.toHoCat) (fun _ _ _ _ h ↦ by
      simpa [CofibrantObject.toHoCat_map_eq_iff])

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HoCat.ιCofibrantObject_obj (X : BifibrantObject C) :
    HoCat.ιCofibrantObject.obj (toHoCat.obj X) =
      CofibrantObject.toHoCat.obj (BifibrantObject.ιCofibrantObject.obj X) :=
  rfl

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.HoCat.** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HoCat.ιCofibrantObject_map_toHoCat_map {X Y : BifibrantObject C} (f : X ⟶ Y) :
    HoCat.ιCofibrantObject.map (toHoCat.map f) =
      CofibrantObject.toHoCat.map (CofibrantObject.homMk f.hom) :=
  rfl

/-- The isomorphism
`toHoCat ⋙ HoCat.ιCofibrantObject ≅ ιCofibrantObject ⋙ CofibrantObject.toHoCat`
between functors `BifibrantObject C ⥤ CofibrantObject.HoCat C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.toHoCatComp** 是 Mathlib 中的一个定义，位于命名空间 `Homo
topicalAlgebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism
`toHoCat ⋙ HoCat.ιCofibrantObject ≅ ιCofibrantObject ⋙ CofibrantObject.toHoCat`
between functors `BifibrantObject C ⥤ CofibrantObject.HoCat C`.
-/
def toHoCatCompιCofibrantObject :
    toHoCat (C := C) ⋙ HoCat.ιCofibrantObject ≅
      ιCofibrantObject ⋙ CofibrantObject.toHoCat := Iso.refl _

end BifibrantObject

namespace CofibrantObject

/-
**HomotopicalAlgebra.CofibrantObject.exists_bifibrant** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.CofibrantObject`。
形式化陈述：exists_bifibrant (X : CofibrantObject C) : exists (Y : BifibrantObject C) 
(i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y), Cofibration (ι.map i) ∧ WeakEq
uivalence (ι.map i)
参数：X : CofibrantObject C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.trivialCofibrati…
· 使用引理 `HomotopicalAlgebra.isCofibrant_of_cofibration`：isCofibrant_of_cofibratio
n [(cofibrations C).IsStableUnderComposition] {X Y : C} (i : X ⟶ Y) [Cofibration
 i] [hX : IsCofibrant X] : IsCofibr…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `HomotopicalAlgebra.instIsMultiplicativeCofibrations`：∀ (C : Type u) [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithW
eakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.ModelCategory.instIsWeakFactorizationSystemCofibratio
nsTrivialFibrations`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [i
nst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.cofibrations 
C…
· 使用定理 `HomotopicalAlgebra.instCofibrationITrivialCofibrationsFibrations`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsCofibrantObjCofibrantObjects`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlg
ebra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
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
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `HomotopicalAlgebra.bifibrantObjects_le_cofibrantObject`：bifibrantObjects
_le_cofibrantObject : bifibrantObjects C <= cofibrantObjects C
-/
lemma exists_bifibrant (X : CofibrantObject C) :
    ∃ (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.ιCofibrantObject.obj Y),
      Cofibration (ι.map i) ∧ WeakEquivalence (ι.map i) := by
  let h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from X.obj)
  have := isCofibrant_of_cofibration h.i
  have : IsFibrant h.Z := by
    rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
    infer_instance
  exact ⟨BifibrantObject.mk h.Z, homMk h.i, inferInstanceAs (Cofibration h.i),
    inferInstanceAs (WeakEquivalence h.i)⟩

/-- Given `X : CofibrantObject C`, this is a choice of bifibrant resolution of `X`. -/
/-
**HomotopicalAlgebra.CofibrantObject.bifibrantResolutionObj** 是 Mathlib 中的一个定义，位
于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：bifibrantResolutionObj (X : CofibrantObject C) : BifibrantObject C
参数：X : CofibrantObject C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.CofibrantObject.exists_bifibrant`：exists_bifibrant (X
 : CofibrantObject C) : exists (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.
ιCofibrantObject.obj Y), Cofibration (ι.m…

--- 原说明 ---
Given `X : CofibrantObject C`, this is a choice of bifibrant resolution of `X`.
-/
noncomputable def bifibrantResolutionObj (X : CofibrantObject C) :
    BifibrantObject C :=
  (exists_bifibrant X).choose

/-- Given `X : CofibrantObject C`, this is a trivial cofibration
from `X` to a choice of bifibrant resolution. -/
/-
**HomotopicalAlgebra.CofibrantObject.iBifibrantResolutionObj** 是 Mathlib 中的一个定义，
位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：iBifibrantResolutionObj (X : CofibrantObject C) : X ⟶ BifibrantObject.ιCof
ibrantObject.obj (bifibrantResolutionObj X)
参数：X : CofibrantObject C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.CofibrantObject.exists_bifibrant`：exists_bifibrant (X
 : CofibrantObject C) : exists (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.
ιCofibrantObject.obj Y), Cofibration (ι.m…

--- 原说明 ---
Given `X : CofibrantObject C`, this is a trivial cofibration
from `X` to a choice of bifibrant resolution.
-/
noncomputable def iBifibrantResolutionObj (X : CofibrantObject C) :
    X ⟶ BifibrantObject.ιCofibrantObject.obj (bifibrantResolutionObj X) :=
  (exists_bifibrant X).choose_spec.choose
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) :
    Cofibration (iBifibrantResolutionObj X).hom :=
  (exists_bifibrant X).choose_spec.choose_spec.1
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) :
    WeakEquivalence (iBifibrantResolutionObj X).hom :=
  (exists_bifibrant X).choose_spec.choose_spec.2
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) :
    WeakEquivalence (iBifibrantResolutionObj X) := by
  rw [weakEquivalence_iff_of_objectProperty]
  infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) :
    IsFibrant (ι.obj (BifibrantObject.ιCofibrantObject.obj X)) := X.2.2

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.CofibrantObject.exists_bifibrant_map** 是 Mathlib 中的一个引理，位于命
名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : exists (g
 : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂), iBifibrantResolutionO
bj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) = f ≫ iBifibrantResolutionObj X
₂
参数：f : X₁ ⟶ X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
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
· 使用引理 `HomotopicalAlgebra.CofibrantObject.exists_bifibrant`：exists_bifibrant (X
 : CofibrantObject C) : exists (Y : BifibrantObject C) (i : X ⟶ BifibrantObject.
ιCofibrantObject.obj Y), Cofibration (ι.m…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsCofibrantObjBifibrantObjects`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlg
ebra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsFibrantObjBifibrantObjects`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgeb
ra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instCofibrationHomFullSubcategoryCofi
brantObjectsIBifibrantResolutionObj`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory C]   (X : HomotopicalAl
gebra.CofibrantOb…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instWeakEquivalenceHomFullSubcategory
CofibrantObjectsIBifibrantResolutionObj`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory C]   (X : Homotopic
alAlgebra.CofibrantOb…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsFibrantObjιBifibrantObjectιCofi
brantObject`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : 
HomotopicalAlgebra.ModelCategory C]   (X : HomotopicalAlgebra.BifibrantOb…
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用引理 `HomotopicalAlgebra.bifibrantObjects_le_cofibrantObject`：bifibrantObjects
_le_cofibrantObject : bifibrantObjects C <= cofibrantObjects C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
-/
lemma exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    ∃ (g : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂),
      iBifibrantResolutionObj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) =
      f ≫ iBifibrantResolutionObj X₂ := by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (iBifibrantResolutionObj X₁).hom (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨BifibrantObject.homMk sq.lift, by cat_disch⟩

/-- Given a morphism in `CofibrantObject C`, this is a choice of morphism
(well defined only up to homotopy) between the chosen bifibrant resolutions. -/
/-
**HomotopicalAlgebra.CofibrantObject.bifibrantResolutionMap** 是 Mathlib 中的一个定义，位
于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：bifibrantResolutionMap {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : bifibra
ntResolutionObj X₁ ⟶ bifibrantResolutionObj X₂
参数：f : X₁ ⟶ X₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.CofibrantObject.exists_bifibrant_map`：exists_bifibran
t_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : exists (g : bifibrantResolutio
nObj X₁ ⟶ bifibrantResolutionObj X₂), iBifibr…

--- 原说明 ---
Given a morphism in `CofibrantObject C`, this is a choice of morphism
(well defined only up to homotopy) between the chosen bifibrant resolutions.
-/
noncomputable def bifibrantResolutionMap {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.CofibrantObject.bifibrantResolutionMap_fac** 是 Mathlib 中的一个
引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：bifibrantResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : iBi
fibrantResolutionObj X₁ ≫ homMk (bifibrantResolutionMap f).hom = f ≫ iBifibrantR
esolutionObj X₂
参数：f : X₁ ⟶ X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `HomotopicalAlgebra.CofibrantObject.exists_bifibrant_map`：exists_bifibran
t_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : exists (g : bifibrantResolutio
nObj X₁ ⟶ bifibrantResolutionObj X₂), iBifibr…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma bifibrantResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    iBifibrantResolutionObj X₁ ≫ homMk (bifibrantResolutionMap f).hom =
      f ≫ iBifibrantResolutionObj X₂ :=
  (exists_bifibrant_map f).choose_spec

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) [WeakEquivalence f] :
    WeakEquivalence (bifibrantResolutionMap f) := by
  rw [weakEquivalence_iff]
  change weakEquivalences _ (CofibrantObject.homMk (bifibrantResolutionMap f).hom)
  rw [← weakEquivalence_iff, ← weakEquivalence_precomp_iff (iBifibrantResolutionObj X₁),
    bifibrantResolutionMap_fac, weakEquivalence_precomp_iff]
  infer_instance

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.CofibrantObject.bifibrantResolutionMap_fac'** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : to
HoCat.map X₁.iBifibrantResolutionObj ≫ toHoCat.map (homMk (bifibrantResolutionMa
p f).hom) = toHoCat.map f ≫ toHoCat.map X₂.iBifibrantResolutionObj
参数：f : X₁ ⟶ X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsCofibrantObjBifibrantObjects`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlg
ebra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用引理 `HomotopicalAlgebra.bifibrantObjects_le_cofibrantObject`：bifibrantObjects
_le_cofibrantObject : bifibrantObjects C <= cofibrantObjects C
· 使用引理 `HomotopicalAlgebra.CofibrantObject.bifibrantResolutionMap_fac`：bifibrant
ResolutionMap_fac {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) : iBifibrantResoluti
onObj X₁ ≫ homMk (bifibrantResolutionMap f).hom = f…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma bifibrantResolutionMap_fac' {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    toHoCat.map X₁.iBifibrantResolutionObj ≫
    toHoCat.map (homMk (bifibrantResolutionMap f).hom) =
    toHoCat.map f ≫ toHoCat.map X₂.iBifibrantResolutionObj :=
  toHoCat.congr_map (bifibrantResolutionMap_fac f)

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomotopicalAlgebra.CofibrantObject.bifibrantResolutionObj_hom_ext** 是 Mathlib 
中的一个引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：bifibrantResolutionObj_hom_ext {X : CofibrantObject C} {Y : BifibrantObjec
t.HoCat C} {f g : BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) ⟶ Y} (h
 : CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫ BifibrantObject.HoC
at.ιCofibrantObject.map f = CofibrantObject.toHoCat.map (iBifibrantResolutionObj
 X) ≫ BifibrantObject.HoCat.ιCofibrantObject.map g) : f = g
参数：bifibrantResolutionObj X；h : CofibrantObject.toHoCat.map (iBifibrantResolutio
nObj X) ≫ BifibrantObject.HoCat.ιCofibrantObject.map f = CofibrantObject.toHoCat
.map (iBifibrantResolutionObj X) ≫ BifibrantObject.HoCat.ιCofibrantObject.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `HomotopicalAlgebra.BifibrantObject.toHoCat_obj_surjective`：toHoCat_obj_s
urjective : Function.Surjective (toHoCat (C
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instFullHoCatToHoCat`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCate
gory C],   HomotopicalAlgebra.BifibrantObject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.BifibrantObject.toHoCat_map_eq_iff`：toHoCat_map_eq_if
f {X Y : BifibrantObject C} (f g : X ⟶ Y) : toHoCat.map f = toHoCat.map g ↔ homR
el C f g
· 使用引理 `HomotopicalAlgebra.BifibrantObject.homRel_iff_rightHomotopyRel`：homRel_i
ff_rightHomotopyRel {X Y : BifibrantObject C} {f g : X ⟶ Y} : homRel C f g ↔ Rig
htHomotopyRel f.hom g.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelC
ategory C] [IsFibrant Y] (f g : X ⟶ Y) : mk f = mk g ↔ RightHomotopyRel f g
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsFibrantObjBifibrantObjects`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgeb
ra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_cofibration_o
f_weakEquivalence`：precomp_bijective_of_cofibration_of_weakEquivalence [IsFibran
t Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] : Function.Bijective (fun …
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instCofibrationHomFullSubcategoryCofi
brantObjectsIBifibrantResolutionObj`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory C]   (X : HomotopicalAl
gebra.CofibrantOb…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instWeakEquivalenceHomFullSubcategory
CofibrantObjectsIBifibrantResolutionObj`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCategory C]   (X : Homotopic
alAlgebra.CofibrantOb…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsFibrantObjCofibrantObjectsObjCo
fibrantObjectιCofibrantObject`：∀ {C : Type u} [inst : CategoryTheory.Category.{v
, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithCofibrations C]   [inst_2 : Cat
egoryTheory…
· 使用引理 `HomotopicalAlgebra.CofibrantObject.homRel_iff_rightHomotopyRel`：homRel_i
ff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} : homRel C f g ↔ Rig
htHomotopyRel f.hom g.hom
· 使用引理 `HomotopicalAlgebra.CofibrantObject.toHoCat_map_eq_iff`：toHoCat_map_eq_if
f {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ Y) : toHoCat.map f = to
HoCat.map g ↔ homRel C f g
-/
lemma bifibrantResolutionObj_hom_ext
    {X : CofibrantObject C} {Y : BifibrantObject.HoCat C} {f g :
      BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) ⟶ Y}
    (h : CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫
      BifibrantObject.HoCat.ιCofibrantObject.map f =
      CofibrantObject.toHoCat.map (iBifibrantResolutionObj X) ≫
        BifibrantObject.HoCat.ιCofibrantObject.map g) :
    f = g := by
  obtain ⟨Y, rfl⟩ := BifibrantObject.toHoCat_obj_surjective Y
  obtain ⟨f, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective g
  change toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map f) =
    toHoCat.map (X.iBifibrantResolutionObj ≫ BifibrantObject.ιCofibrantObject.map g) at h
  rw [CofibrantObject.toHoCat_map_eq_iff,
    CofibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff] at h
  rw [BifibrantObject.toHoCat_map_eq_iff,
    BifibrantObject.homRel_iff_rightHomotopyRel,
    ← RightHomotopyClass.mk_eq_mk_iff]
  apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence
    _ (iBifibrantResolutionObj X).hom).1
  simpa using! h

set_option backward.isDefEq.respectTransparency false in
/-- The bifibrant resolution functor from the category of cofibrant objects
to the homotopy category of bifibrant objects. -/
@[simps, implicit_reducible]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.bifibrantResolution'** 是 Mathlib 中的一个
定义，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.Functor (Homotopical
Algebra.CofibrantObject C) (HomotopicalAlgebra.BifibrantObject.HoCat C)
参数：HomotopicalAlgebra.CofibrantObject C；HomotopicalAlgebra.BifibrantObject.HoCat
 C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifibrant resolution functor from the category of cofibrant objects
to the homotopy category of bifibrant objects.
-/
noncomputable def HoCat.bifibrantResolution' : CofibrantObject C ⥤ BifibrantObject.HoCat C where
  obj X := BifibrantObject.toHoCat.obj (bifibrantResolutionObj X)
  map f := BifibrantObject.toHoCat.map (bifibrantResolutionMap f)
  map_id X := bifibrantResolutionObj_hom_ext (by simp)
  map_comp {X₁ X₂ X₃} f g := bifibrantResolutionObj_hom_ext (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bifibrant resolution functor from the homotopy category of
cofibrant objects to the homotopy category of bifibrant objects. -/
@[implicit_reducible]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.bifibrantResolution** 是 Mathlib 中的一个定
义，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.Functor (Homotopical
Algebra.CofibrantObject.HoCat C) (HomotopicalAlgebra.BifibrantObject.HoCat C)
参数：HomotopicalAlgebra.CofibrantObject.HoCat C；HomotopicalAlgebra.BifibrantObject
.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifibrant resolution functor from the homotopy category of
cofibrant objects to the homotopy category of bifibrant objects.
-/
noncomputable def HoCat.bifibrantResolution :
    CofibrantObject.HoCat C ⥤ BifibrantObject.HoCat C :=
  CategoryTheory.Quotient.lift _ CofibrantObject.HoCat.bifibrantResolution' (by
    intro X Y f g h
    apply bifibrantResolutionObj_hom_ext
    simpa [← Functor.map_comp, toHoCat_map_eq_iff] using! h.postcomp _)

@[simp]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.bifibrantResolution_obj** 是 Mathlib 中
的一个定理，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C]   (X : HomotopicalAlgebra.CofibrantObject C),   Hom
otopicalAlgebra.CofibrantObject.HoCat.bifibrantResolution.obj (HomotopicalAlgebr
a.CofibrantObject.toHoCat.obj X) =     HomotopicalAlgebra.BifibrantObject.toHoCa
t.obj X.bifibrantResolutionObj
参数：X : HomotopicalAlgebra.CofibrantObject C；HomotopicalAlgebra.CofibrantObject.t
oHoCat.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma HoCat.bifibrantResolution_obj (X : CofibrantObject C) :
    HoCat.bifibrantResolution.obj (CofibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.obj (bifibrantResolutionObj X) := rfl

@[simp]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.bifibrantResolution_map** 是 Mathlib 中
的一个定理，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C]   {X Y : HomotopicalAlgebra.CofibrantObject C} (f :
 X ⟶ Y),   HomotopicalAlgebra.CofibrantObject.HoCat.bifibrantResolution.map (Hom
otopicalAlgebra.CofibrantObject.toHoCat.map f) =     HomotopicalAlgebra.Bifibran
tObject.toHoCat.map (HomotopicalAlgebra.CofibrantObject.bifibrantResolutionMap f
)
参数：f : X ⟶ Y；HomotopicalAlgebra.CofibrantObject.toHoCat.map f；HomotopicalAlgebra
.CofibrantObject.bifibrantResolutionMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma HoCat.bifibrantResolution_map {X Y : CofibrantObject C} (f : X ⟶ Y) :
    HoCat.bifibrantResolution.map (CofibrantObject.toHoCat.map f) =
      BifibrantObject.toHoCat.map (bifibrantResolutionMap f) := rfl

/-- Auxiliary definition for `CofibrantObject.HoCat.adj`. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adjUnit** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.Functor.id (Homotopi
calAlgebra.CofibrantObject.HoCat C) ⟶         HomotopicalAlgebra.CofibrantObject
.HoCat.bifibrantResolution.comp           HomotopicalAlgebra.BifibrantObject.HoC
at.ιCofibrantObject
参数：HomotopicalAlgebra.CofibrantObject.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CofibrantObject.HoCat.adj`.
-/
noncomputable def HoCat.adjUnit :
    𝟭 (HoCat C) ⟶ HoCat.bifibrantResolution ⋙ BifibrantObject.HoCat.ιCofibrantObject :=
  Quotient.natTransLift _
    { app X := toHoCat.map (iBifibrantResolutionObj X)
      naturality _ _ f := (bifibrantResolutionMap_fac' f).symm }
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adjUnit_app** 是 Mathlib 中的一个定理，位于命名空间
 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C]   (X : HomotopicalAlgebra.CofibrantObject C),   Hom
otopicalAlgebra.CofibrantObject.HoCat.adjUnit.app (HomotopicalAlgebra.CofibrantO
bject.toHoCat.obj X) =     HomotopicalAlgebra.CofibrantObject.toHoCat.map X.iBif
ibrantResolutionObj
参数：X : HomotopicalAlgebra.CofibrantObject C；HomotopicalAlgebra.CofibrantObject.t
oHoCat.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma HoCat.adjUnit_app (X : CofibrantObject C) :
    HoCat.adjUnit.app (toHoCat.obj X) =
      toHoCat.map (iBifibrantResolutionObj X) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject.HoCat C) : WeakEquivalence (HoCat.adjUnit.app X) := by
  obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
  rw [HoCat.adjUnit_app, weakEquivalence_toHoCat_map_iff,
    weakEquivalence_iff_of_objectProperty]
  infer_instance

/-- Auxiliary definition for `CofibrantObject.HoCat.adj`. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adjCounit'** 是 Mathlib 中的一个定义，位于命名空间 
`HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.Functor.id (Homotopi
calAlgebra.BifibrantObject.HoCat C) ⟶         HomotopicalAlgebra.BifibrantObject
.HoCat.ιCofibrantObject.comp           HomotopicalAlgebra.CofibrantObject.HoCat.
bifibrantResolution
参数：HomotopicalAlgebra.BifibrantObject.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CofibrantObject.HoCat.adj`.
-/
noncomputable def HoCat.adjCounit' :
    𝟭 (BifibrantObject.HoCat C) ⟶
      BifibrantObject.HoCat.ιCofibrantObject ⋙ HoCat.bifibrantResolution :=
  Quotient.natTransLift _
    { app X :=
        BifibrantObject.toHoCat.map
          (BifibrantObject.homMk (iBifibrantResolutionObj (.mk X.obj)).hom)
      naturality X₁ X₂ f := BifibrantObject.toHoCat.congr_map (by
        have := (ObjectProperty.ι _).congr_map
          (bifibrantResolutionMap_fac (CofibrantObject.homMk f.hom)).symm
        ext : 1
        dsimp
        exact this) }
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adjCounit'_app** 是 Mathlib 中的一个定理，位于命
名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C]   (X : HomotopicalAlgebra.BifibrantObject C),   Hom
otopicalAlgebra.CofibrantObject.HoCat.adjCounit'.app (HomotopicalAlgebra.Bifibra
ntObject.toHoCat.obj X) =     HomotopicalAlgebra.BifibrantObject.toHoCat.map    
   (HomotopicalAlgebra.BifibrantObject.homMk         (HomotopicalAlgebra.Cofibra
ntObject.mk X.obj).iBifibrantResolutionObj.hom)
参数：X : HomotopicalAlgebra.BifibrantObject C；HomotopicalAlgebra.BifibrantObject.t
oHoCat.obj X；HomotopicalAlgebra.BifibrantObject.homMk         (HomotopicalAlgebr
a.CofibrantObject.mk X.obj).iBifibrantResolutionObj.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
-/
lemma HoCat.adjCounit'_app (X : BifibrantObject C) :
    HoCat.adjCounit'.app (BifibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk
        (iBifibrantResolutionObj (.mk X.obj)).hom) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject.HoCat C) : IsIso (HoCat.adjCounit'.app X) := by
  obtain ⟨X, rfl⟩ := BifibrantObject.toHoCat_obj_surjective X
  rw [HoCat.adjCounit'_app]
  have : WeakEquivalence (C := BifibrantObject C)
      (BifibrantObject.homMk ((mk X.obj).iBifibrantResolutionObj).hom) := by
    simp only [BifibrantObject.weakEquivalence_homMk_iff]
    infer_instance
  infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (HoCat.adjCounit' (C := C)) := NatIso.isIso_of_isIso_app _

/-- Auxiliary definition for `CofibrantObject.HoCat.adj`. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adjCounitIso** 是 Mathlib 中的一个定义，位于命名空
间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       HomotopicalAlgebra.BifibrantObject.
HoCat.ιCofibrantObject.comp           HomotopicalAlgebra.CofibrantObject.HoCat.b
ifibrantResolution ≅         CategoryTheory.Functor.id (HomotopicalAlgebra.Bifib
rantObject.HoCat C)
参数：HomotopicalAlgebra.BifibrantObject.HoCat C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsIsoFunctorHoCatAdjCounit'`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebr
a.ModelCategory C],   CategoryTheory.IsIso HomotopicalAl…

--- 原说明 ---
Auxiliary definition for `CofibrantObject.HoCat.adj`.
-/
noncomputable def HoCat.adjCounitIso :
    BifibrantObject.HoCat.ιCofibrantObject ⋙ bifibrantResolution ≅ 𝟭 (BifibrantObject.HoCat C) :=
  (asIso HoCat.adjCounit').symm
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adjCounitIso_inv_app** 是 Mathlib 中的一个
定理，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C]   (X : HomotopicalAlgebra.BifibrantObject C),   Hom
otopicalAlgebra.CofibrantObject.HoCat.adjCounitIso.inv.app (HomotopicalAlgebra.B
ifibrantObject.toHoCat.obj X) =     HomotopicalAlgebra.BifibrantObject.toHoCat.m
ap       (HomotopicalAlgebra.BifibrantObject.homMk         (HomotopicalAlgebra.C
ofibrantObject.mk X.obj).iBifibrantResolutionObj.hom)
参数：X : HomotopicalAlgebra.BifibrantObject C；HomotopicalAlgebra.BifibrantObject.t
oHoCat.obj X；HomotopicalAlgebra.BifibrantObject.homMk         (HomotopicalAlgebr
a.CofibrantObject.mk X.obj).iBifibrantResolutionObj.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
-/
lemma HoCat.adjCounitIso_inv_app (X : BifibrantObject C) :
    HoCat.adjCounitIso.inv.app (BifibrantObject.toHoCat.obj X) =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk
        ((iBifibrantResolutionObj (.mk X.obj))).hom) := rfl

/-- The adjunction between the category `CofibrantObject.HoCat C` and `BifibrantObject.HoCat C`. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `Homoto
picalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       HomotopicalAlgebra.CofibrantObject.
HoCat.bifibrantResolution ⊣         HomotopicalAlgebra.BifibrantObject.HoCat.ιCo
fibrantObject
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the category `CofibrantObject.HoCat C` and `BifibrantObje
ct.HoCat C`.
-/
noncomputable def HoCat.adj :
    HoCat.bifibrantResolution (C := C) ⊣ BifibrantObject.HoCat.ιCofibrantObject where
  unit := HoCat.adjUnit
  counit := HoCat.adjCounitIso.hom
  left_triangle_components X := by
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨X, _, rfl⟩ := CofibrantObject.mk_surjective X
    rw [comp_hom_eq_id]; push inv
    apply bifibrantResolutionObj_hom_ext
    dsimp
    simp only [HoCat.adjCounitIso_inv_app]
    apply bifibrantResolutionMap_fac'
  right_triangle_components X := by
    obtain ⟨X, rfl⟩ := BifibrantObject.toHoCat_obj_surjective X
    rw [comp_hom_eq_id]; push inv
    cat_disch
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (HoCat.adj (C := C)).counit := by
  dsimp [HoCat.adj]
  infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Full :=
  HoCat.adj.fullyFaithfulROfIsIsoCounit.full
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (BifibrantObject.HoCat.ιCofibrantObject (C := C)).Faithful :=
  HoCat.adj.fullyFaithfulROfIsIsoCounit.faithful
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject.HoCat C) : WeakEquivalence (HoCat.adj.unit.app X) := by
  obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
  dsimp [HoCat.adj]
  infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HoCat.bifibrantResolution.IsLocalization (weakEquivalences (HoCat C)) :=
  HoCat.adj.isLocalization_leftAdjoint _ (by
    intro X Y f hf
    obtain ⟨X, rfl⟩ := toHoCat_obj_surjective X
    obtain ⟨Y, rfl⟩ := toHoCat_obj_surjective Y
    obtain ⟨f, rfl⟩ := toHoCat.map_surjective f
    rw [← weakEquivalence_iff, weakEquivalence_toHoCat_map_iff] at hf
    rw [HoCat.bifibrantResolution_map]
    apply Localization.inverts _ (weakEquivalences _)
    rw [← weakEquivalence_iff]
    infer_instance) (fun X ↦ by
    rw [← weakEquivalence_iff]
    dsimp
    infer_instance)

end CofibrantObject

namespace BifibrantObject

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ C`, as a localizer morphism. -/
/-
**HomotopicalAlgebra.BifibrantObject.localizerMorphism** 是 Mathlib 中的一个定义，位于命名空间
 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：localizerMorphism : LocalizerMorphism (weakEquivalences (BifibrantObject C
)) (weakEquivalences C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `BifibrantObject C ⥤ C`, as a localizer morphism.
-/
def localizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C)) (weakEquivalences C) where
  functor := ι
  map := by rfl

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ CofibrantObject C`, as a localizer morphism. -/
@[simps]
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `BifibrantObject C ⥤ CofibrantObject C`, as a localizer morphism.
-/
def ιCofibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (CofibrantObject C)) where
  functor := ιCofibrantObject
  map _ _ _ h := h

variable (C) in
/-- The inclusion `BifibrantObject C ⥤ FibrantObject C`, as a localizer morphism. -/
@[simps]
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `BifibrantObject C ⥤ FibrantObject C`, as a localizer morphism.
-/
def ιFibrantObjectLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (BifibrantObject C))
      (weakEquivalences (FibrantObject C)) where
  functor := ιFibrantObject
  map _ _ _ h := h

open Functor
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ιCofibrantObjectLocalizerMorphism C).IsLocalizedEquivalence :=
  let : CatCommSq (ιCofibrantObjectLocalizerMorphism C).functor toHoCat
      (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight toHoCatCompιCofibrantObject.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso CofibrantObject.HoCat.adj.counit)⟩
  LocalizerMorphism.IsLocalizedEquivalence.mk'
    (ιCofibrantObjectLocalizerMorphism C) BifibrantObject.toHoCat
    (CofibrantObject.toHoCat ⋙ CofibrantObject.HoCat.bifibrantResolution) (𝟭 _)
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category D] (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιCofibrantObject ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((ιCofibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _)
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (localizerMorphism C).IsLocalizedEquivalence :=
  inferInstanceAs ((ιCofibrantObjectLocalizerMorphism C).comp
    (CofibrantObject.localizerMorphism C)).IsLocalizedEquivalence
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (BifibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ιFibrantObjectLocalizerMorphism C).IsLocalizedEquivalence :=
  let L := FibrantObject.ι ⋙ (weakEquivalences C).Q
  have : ((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization
    (weakEquivalences _) :=
    inferInstanceAs ((ι ⋙ (weakEquivalences C).Q).IsLocalization (weakEquivalences _))
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ L
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category D] (L : FibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (ιFibrantObject ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((ιFibrantObjectLocalizerMorphism C).functor ⋙ L).IsLocalization _)

end BifibrantObject

/-
**HomotopicalAlgebra.locallySmall_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopicalAlgebra`。
形式化陈述：locallySmall_of_isLocalization {D : Type*} [Category* D] (L : C ⥤ D) [L.Is
Localization (weakEquivalences C)] [LocallySmall.{w} C] : LocallySmall.{w} D
参数：L : C ⥤ D；weakEquivalences C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_faithful`：locallySmall_of_faithful {C : T
ype u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
 [LocallySmall.{w} D] : Local…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsLocalizationHoCatToHoCatWeakEqu
ivalences`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Ho
motopicalAlgebra.ModelCategory C],   HomotopicalAlgebra.BifibrantObject…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instIsLocalizedEquivalenceWeakEquival
encesLocalizerMorphism`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]
 [inst_1 : HomotopicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.BifibrantO
bjec…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `HomotopicalAlgebra.BifibrantObject.instLocallySmallHoCat`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.ModelCat
egory C]   [CategoryTheory.LocallySmall.{w, v,…
-/
lemma locallySmall_of_isLocalization {D : Type*} [Category* D]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)] [LocallySmall.{w} C] :
    LocallySmall.{w} D :=
  locallySmall_of_faithful ((BifibrantObject.localizerMorphism C).localizedFunctor
    BifibrantObject.toHoCat L).inv

end HomotopicalAlgebra

