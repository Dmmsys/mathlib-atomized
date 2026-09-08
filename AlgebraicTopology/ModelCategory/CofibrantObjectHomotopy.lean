/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# The homotopy category of cofibrant objects

Let `C` be a model category. By using the right homotopy relation,
we introduce the homotopy category `CofibrantObject.HoCat C` of cofibrant objects
in `C`, and we define a cofibrant resolution functor
`CofibrantObject.HoCat.resolution : C ⥤ CofibrantObject.HoCat C`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace CofibrantObject

variable (C) in
/-- The right homotopy relation on the category of cofibrant objects. -/
/-
**HomotopicalAlgebra.CofibrantObject.homRel** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra.CofibrantObject`。
形式化陈述：homRel : HomRel (CofibrantObject C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homotopy relation on the category of cofibrant objects.
-/
def homRel : HomRel (CofibrantObject C) :=
  fun _ _ f g ↦ RightHomotopyRel f.hom g.hom
/-
**HomotopicalAlgebra.CofibrantObject.homRel_iff_rightHomotopyRel** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：homRel_iff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} : homR
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
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma homRel_iff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} :
    homRel C f g ↔ RightHomotopyRel f.hom g.hom := Iff.rfl
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomRel.IsStableUnderPostcomp (homRel C) where
  comp_right _ h := h.postcomp _
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomRel.IsStableUnderPrecomp (homRel C) where
  comp_left _ _ _ h := h.precomp _
/-
**HomotopicalAlgebra.CofibrantObject.homRel_equivalence_of_isFibrant_tgt** 是 Mat
hlib 中的一个引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：homRel_equivalence_of_isFibrant_tgt {X Y : CofibrantObject C} [IsFibrant Y
.obj] : Equivalence (homRel C (X
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
· 使用定理 `Equivalence.comap`：Equivalence.comap (h : Equivalence r) (f : α -> β) : 
Equivalence (r on f)
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.equivalence`：equivalence [ModelCateg
ory C] (X Y : C) [IsFibrant Y] : _root_.Equivalence (RightHomotopyRel (X
-/
lemma homRel_equivalence_of_isFibrant_tgt {X Y : CofibrantObject C} [IsFibrant Y.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (RightHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) ↦ f.hom)

variable (C) in
/-- The homotopy category of cofibrant objects. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopi
calAlgebra.CofibrantObject`。
形式化陈述：HoCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy category of cofibrant objects.
-/
abbrev HoCat := Quotient (CofibrantObject.homRel C)

/-- The quotient functor from the category of cofibrant objects to its
homotopy category. -/
@[implicit_reducible]
/-
**HomotopicalAlgebra.CofibrantObject.toHoCat** 是 Mathlib 中的一个定义，位于命名空间 `Homotopi
calAlgebra.CofibrantObject`。
形式化陈述：toHoCat : CofibrantObject C ⥤ HoCat C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient functor from the category of cofibrant objects to its
homotopy category.
-/
def toHoCat : CofibrantObject C ⥤ HoCat C := Quotient.functor _
/-
**HomotopicalAlgebra.CofibrantObject.toHoCat_obj_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `HomotopicalAlgebra.CofibrantObject`。
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
-/
lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Full (toHoCat (C := C)) := by dsimp [toHoCat]; infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.toHoCat_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopicalAlgebra.CofibrantObject`。
形式化陈述：toHoCat_map_eq {X Y : CofibrantObject C} {f g : X ⟶ Y} (h : homRel C f g) 
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
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
lemma toHoCat_map_eq {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h
/-
**HomotopicalAlgebra.CofibrantObject.toHoCat_map_eq_iff** 是 Mathlib 中的一个引理，位于命名空
间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：toHoCat_map_eq_iff {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ 
Y) : toHoCat.map f = toHoCat.map g ↔ homRel C f g
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
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsStableUnderPrecompHomRel`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalA
lgebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsStableUnderPostcompHomRel`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopical
Algebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `Equivalence.eqvGen_eq`：Equivalence.eqvGen_eq (h : Equivalence r) : EqvGe
n r = r
· 使用引理 `HomotopicalAlgebra.CofibrantObject.homRel_equivalence_of_isFibrant_tgt`：
homRel_equivalence_of_isFibrant_tgt {X Y : CofibrantObject C} [IsFibrant Y.obj] 
: Equivalence (homRel C (X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toHoCat_map_eq_iff {X Y : CofibrantObject C} [IsFibrant Y.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    HomRel.compClosure_eq_self, homRel_equivalence_of_isFibrant_tgt.eqvGen_eq]
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (weakEquivalences (CofibrantObject C)).HasQuotient (homRel C) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    obtain ⟨P, ⟨h⟩⟩ := h
    apply h.weakEquivalence_iff
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryWithWeakEquivalences (CofibrantObject.HoCat C) where
  weakEquivalences := (weakEquivalences _).quotient _
/-
**HomotopicalAlgebra.CofibrantObject.weakEquivalence_toHoCat_map_iff** 是 Mathlib
 中的一个引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：weakEquivalence_toHoCat_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) : We
akEquivalence (toHoCat.map f) ↔ WeakEquivalence f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.quotient_iff`：quotient_iff {X Y : C} (f 
: X ⟶ Y) : W.quotient homRel ((Quotient.functor homRel).map f) ↔ W f
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsStableUnderPrecompHomRel`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalA
lgebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsStableUnderPostcompHomRel`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopical
Algebra.ModelCategory C],   CategoryTheory.HomRel.IsStab…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instHasQuotientWeakEquivalencesHomRel
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homot
opicalAlgebra.ModelCategory C],   (HomotopicalAlgebra.weakEqui…
-/
lemma weakEquivalence_toHoCat_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toHoCat.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in
/-- The functor `CofibrantObject C ⥤ HoCat C`, considered as a localizer morphism. -/
/-
**HomotopicalAlgebra.CofibrantObject.toHoCatLocalizerMorphism** 是 Mathlib 中的一个定义
，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：toHoCatLocalizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantO
bject C)) (weakEquivalences (CofibrantObject.HoCat C)) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `CofibrantObject C ⥤ HoCat C`, considered as a localizer morphism.
-/
def toHoCatLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (CofibrantObject.HoCat C)) where
  functor := toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

variable (C) in
/-
**HomotopicalAlgebra.CofibrantObject.factorsThroughLocalization** 是 Mathlib 中的一个
引理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：factorsThroughLocalization : (homRel C).FactorsThroughLocalization (weakEq
uivalences (CofibrantObject C))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_very_good_pathObject`：exists_
very_good_pathObject [ModelCategory C] {f g : X ⟶ Y} [IsCofibrant X] (h : RightH
omotopyRel f g) : exists (P : PathObject Y), P.IsVery…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsCofibrantObjCofibrantObjects`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlg
ebra.CategoryWithCofibrations C]   [inst_2 : CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.areEqualizedByLocalization_iff`：areEqualizedByLocalizatio
n_iff [L.IsLocalization W] : AreEqualizedByLocalization W f g ↔ L.map f = L.map 
g
· 使用定理 `HomotopicalAlgebra.PathObject.instIsCofibrantPOfIsVeryGood`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {A : C}   [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C] (P : Homotop…
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
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomotopicalAlgebra.PathObject.weakEquivalence_ι`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.CategoryWithWeakE
quivalences C]   {A : C} (self : Homo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₀`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `HomotopicalAlgebra.PrepathObject.ι_p₁`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A : C} (self : HomotopicalAlgebra.PrepathObject A),   C
ategoryTheory.CategoryStruc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₁`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
-/
lemma factorsThroughLocalization :
    (homRel C).FactorsThroughLocalization (weakEquivalences (CofibrantObject C)) := by
  rintro X Y f g h
  obtain ⟨P, _, ⟨h⟩⟩ := h.exists_very_good_pathObject
  let L := (weakEquivalences (CofibrantObject C)).Q
  rw [areEqualizedByLocalization_iff L]
  suffices L.map (homMk P.p₀) = L.map (homMk P.p₁) by
    simp only [show f = homMk h.h ≫ homMk P.p₀ by cat_disch,
      show g = homMk h.h ≫ homMk P.p₁ by cat_disch, Functor.map_comp, this]
  have := Localization.inverts L (weakEquivalences _) (homMk P.ι) (by
    simp only [← weakEquivalence_iff, weakEquivalence_homMk_iff]
    infer_instance)
  simp only [← cancel_epi (L.map (homMk P.ι)), ← L.map_comp, homMk_homMk, P.ι_p₀, P.ι_p₁]
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toHoCatLocalizerMorphism C).IsLocalizedEquivalence := by
  apply (factorsThroughLocalization C).isLocalizedEquivalence
  apply MorphismProperty.eq_inverseImage_quotientFunctor
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : CofibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    (toHoCat ⋙ L).IsLocalization (weakEquivalences _) :=
  inferInstanceAs (((toHoCatLocalizerMorphism C).functor ⋙ L).IsLocalization _)
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.exists_resolution** 是 Mathlib 中的一个定理，
位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] (X : C),   ∃ X',     ∃ (_ : HomotopicalAlgebr
a.IsCofibrant X'),       ∃ p, HomotopicalAlgebra.Fibration p ∧ HomotopicalAlgebr
a.WeakEquivalence p
参数：X : C；_ : HomotopicalAlgebra.IsCofibrant X'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm5b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.cofibrations C).…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.isCofibrant_iff_of_isInitial`：isCofibrant_iff_of_isIn
itial [(cofibrations C).RespectsIso] {A X : C} (i : A ⟶ X) (hA : IsInitial A) : 
IsCofibrant X ↔ Cofibration i
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoOfIsStableUnderRetracts`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Mor
phismProperty C}   [P.IsStableUnderRetracts], P.RespectsIso
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm3c`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopi
calAlgebra.cofibrations C).…
· 使用定理 `HomotopicalAlgebra.instCofibrationICofibrationsTrivialFibrations`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.instFibrationPCofibrationsTrivialFibrations`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.instWeakEquivalencePCofibrationsTrivialFibrations`：∀ 
(C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlge
bra.CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
-/
lemma HoCat.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsCofibrant X') (p : X' ⟶ X), Fibration p ∧ WeakEquivalence p := by
  have h := MorphismProperty.factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to X)
  refine ⟨h.Z, ?_, h.p, inferInstance, inferInstance⟩
  rw [isCofibrant_iff_of_isInitial h.i initialIsInitial]
  infer_instance

/-- Given `X : C`, this is a cofibrant object `X'` equipped with a
trivial fibration `X' ⟶ X` (see `HoCat.pResolutionObj`). -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.resolutionObj** 是 Mathlib 中的一个定义，位于命名
空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → [Homotopi
calAlgebra.ModelCategory C] → C → C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.CofibrantObject.HoCat.exists_resolution`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.
ModelCategory C] (X : C),   ∃ X',     ∃ (_ : Hom…

--- 原说明 ---
Given `X : C`, this is a cofibrant object `X'` equipped with a
trivial fibration `X' ⟶ X` (see `HoCat.pResolutionObj`).
-/
noncomputable def HoCat.resolutionObj (X : C) : C :=
  (exists_resolution X).choose
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : IsCofibrant (HoCat.resolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose

/-- This is a trivial fibration `resolutionObj X ⟶ X` where
`resolutionObj X` is a choice of a cofibrant resolution of `X`. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.pResolutionObj** 是 Mathlib 中的一个定义，位于命
名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       (X : C) → HomotopicalAlgebra.
CofibrantObject.HoCat.resolutionObj X ⟶ X
参数：X : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.CofibrantObject.HoCat.exists_resolution`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.
ModelCategory C] (X : C),   ∃ X',     ∃ (_ : Hom…

--- 原说明 ---
This is a trivial fibration `resolutionObj X ⟶ X` where
`resolutionObj X` is a choice of a cofibrant resolution of `X`.
-/
noncomputable def HoCat.pResolutionObj (X : C) : resolutionObj X ⟶ X :=
  (exists_resolution X).choose_spec.choose_spec.choose
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Fibration (HoCat.pResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : WeakEquivalence (HoCat.pResolutionObj X) :=
  (HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [IsFibrant X] : IsFibrant (HoCat.resolutionObj X) :=
  isFibrant_of_fibration (HoCat.pResolutionObj X)
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.exists_resolution_map** 是 Mathlib 中的一
个定理，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   ∃ g,     CategoryT
heory.CategoryStruct.comp g (HomotopicalAlgebra.CofibrantObject.HoCat.pResolutio
nObj Y) =       CategoryTheory.CategoryStruct.comp (HomotopicalAlgebra.Cofibrant
Object.HoCat.pResolutionObj X) f
参数：f : X ⟶ Y；HomotopicalAlgebra.CofibrantObject.HoCat.pResolutionObj Y；Homotopic
alAlgebra.CofibrantObject.HoCat.pResolutionObj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsCofibrantResolutionObj`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlg
ebra.ModelCategory C] (X : C),   HomotopicalAlgebra.I…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instFibrationPResolutionObj`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] (X : C),   HomotopicalAlgebra.F…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instWeakEquivalencePResolutionObj`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopic
alAlgebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
-/
lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      g ≫ pResolutionObj Y = pResolutionObj X ≫ f := by
  have sq : CommSq (initial.to _) (initial.to _) (pResolutionObj Y)
    (pResolutionObj X ≫ f) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- A lifting of a morphism `f : X ⟶ Y` on cofibrant resolutions.
(This is functorial only up to homotopy, see `HoCat.resolution`.) -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap** 是 Mathlib 中的一个定义，位于命名
空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {X Y : C} →         (X ⟶ Y) →
           (HomotopicalAlgebra.CofibrantObject.HoCat.resolutionObj X ⟶          
   HomotopicalAlgebra.CofibrantObject.HoCat.resolutionObj Y)
参数：X ⟶ Y；HomotopicalAlgebra.CofibrantObject.HoCat.resolutionObj X ⟶             
HomotopicalAlgebra.CofibrantObject.HoCat.resolutionObj Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.CofibrantObject.HoCat.exists_resolution_map`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   ∃ g,…

--- 原说明 ---
A lifting of a morphism `f : X ⟶ Y` on cofibrant resolutions.
(This is functorial only up to homotopy, see `HoCat.resolution`.)
-/
noncomputable def HoCat.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose

@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap_fac** 是 Mathlib 中的一个定理，
位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   CategoryTheory.Cat
egoryStruct.comp (HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap f)     
  (HomotopicalAlgebra.CofibrantObject.HoCat.pResolutionObj Y) =     CategoryTheo
ry.CategoryStruct.comp (HomotopicalAlgebra.CofibrantObject.HoCat.pResolutionObj 
X) f
参数：f : X ⟶ Y；HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap f；Homotopica
lAlgebra.CofibrantObject.HoCat.pResolutionObj Y；HomotopicalAlgebra.CofibrantObje
ct.HoCat.pResolutionObj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `HomotopicalAlgebra.CofibrantObject.HoCat.exists_resolution_map`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   ∃ g,…
-/
lemma HoCat.resolutionMap_fac {X Y : C} (f : X ⟶ Y) :
    resolutionMap f ≫ pResolutionObj Y =
      pResolutionObj X ≫ f :=
  (exists_resolution_map f).choose_spec

@[simp]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff** 是
 Mathlib 中的一个定理，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y),   HomotopicalAlgebra
.WeakEquivalence (HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap f) ↔   
  HomotopicalAlgebra.WeakEquivalence f
参数：f : X ⟶ Y；HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.weakEquivalence_postcomp_iff`：weakEquivalence_postcom
p_iff [WeakEquivalence g] : WeakEquivalence (f ≫ g) ↔ WeakEquivalence f
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm2`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   (Homotopic
alAlgebra.weakEquivalences…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instWeakEquivalencePResolutionObj`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopic
alAlgebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.HoCat.resolutionMap_fac`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.
ModelCategory C] {X Y : C}   (f : X ⟶ Y),   Cate…
· 使用引理 `HomotopicalAlgebra.weakEquivalence_precomp_iff`：weakEquivalence_precomp_
iff [WeakEquivalence f] : WeakEquivalence (f ≫ g) ↔ WeakEquivalence g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma HoCat.weakEquivalence_resolutionMap_iff {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence (resolutionMap f) ↔ WeakEquivalence f := by
  rw [← weakEquivalence_postcomp_iff _ (pResolutionObj Y),
    HoCat.resolutionMap_fac, weakEquivalence_precomp_iff]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.resolutionObj_hom_ext** 是 Mathlib 中的一
个定理，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : H
omotopicalAlgebra.ModelCategory C] {X : C}   [inst_2 : HomotopicalAlgebra.IsCofi
brant X] {Y : C}   {f g : X ⟶ HomotopicalAlgebra.CofibrantObject.HoCat.resolutio
nObj Y},   HomotopicalAlgebra.LeftHomotopyRel       (CategoryTheory.CategoryStru
ct.comp f (HomotopicalAlgebra.CofibrantObject.HoCat.pResolutionObj Y))       (Ca
tegoryTheory.CategoryStruct.comp g (HomotopicalAlgebra.CofibrantObject.HoCat.pRe
solutionObj Y)) →     HomotopicalAlgebra.CofibrantObject.toHoCat.map (Homotopica
lAlgebra.CofibrantObject.homMk f) =       HomotopicalAlgebra.CofibrantObject.toH
oCat.map (HomotopicalAlgebra.CofibrantObject.homMk g)
参数：CategoryTheory.CategoryStruct.comp f (HomotopicalAlgebra.CofibrantObject.HoCa
t.pResolutionObj Y)；CategoryTheory.CategoryStruct.comp g (HomotopicalAlgebra.Cof
ibrantObject.HoCat.pResolutionObj Y)；HomotopicalAlgebra.CofibrantObject.homMk f；
HomotopicalAlgebra.CofibrantObject.homMk g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `HomotopicalAlgebra.CofibrantObject.toHoCat_map_eq`：toHoCat_map_eq {X Y :
 CofibrantObject C} {f g : X ⟶ Y} (h : homRel C f g) : toHoCat.map f = toHoCat.m
ap g
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsCofibrantResolutionObj`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlg
ebra.ModelCategory C] (X : C),   HomotopicalAlgebra.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.CofibrantObject.homRel_iff_rightHomotopyRel`：homRel_i
ff_rightHomotopyRel {X Y : CofibrantObject C} {f g : X ⟶ Y} : homRel C f g ↔ Rig
htHomotopyRel f.hom g.hom
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.rightHomotopyRel`：rightHomotopyRel (h
 : LeftHomotopyRel f g) : RightHomotopyRel f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.LeftHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelCa
tegory C] [IsCofibrant X] (f g : X ⟶ Y) : mk f = mk g ↔ LeftHomotopyRel f g
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用引理 `HomotopicalAlgebra.LeftHomotopyClass.postcomp_bijective_of_fibration_of_
weakEquivalence`：postcomp_bijective_of_fibration_of_weakEquivalence [IsCofibrant
 X] (g : Y ⟶ Z) [Fibration g] [WeakEquivalence g] : Function.Bijective (fun (…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instFibrationPResolutionObj`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlge
bra.ModelCategory C] (X : C),   HomotopicalAlgebra.F…
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instWeakEquivalencePResolutionObj`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopic
alAlgebra.ModelCategory C] (X : C),   HomotopicalAlgebra.W…
-/
lemma HoCat.resolutionObj_hom_ext {X : C} [IsCofibrant X] {Y : C} {f g : X ⟶ resolutionObj Y}
    (h : LeftHomotopyRel (f ≫ pResolutionObj Y) (g ≫ pResolutionObj Y)) :
    toHoCat.map (homMk f) = toHoCat.map (homMk g) := by
  apply toHoCat_map_eq
  rw [homRel_iff_rightHomotopyRel]
  apply LeftHomotopyRel.rightHomotopyRel
  rw [← LeftHomotopyClass.mk_eq_mk_iff] at h ⊢
  exact (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence
    (X := X) (g := pResolutionObj Y)).injective h

/-- A cofibrant resolution functor from a model category to the homotopy category
of cofibrant objects. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.resolution** 是 Mathlib 中的一个定义，位于命名空间 
`HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.Functor C (Hom
otopicalAlgebra.CofibrantObject.HoCat C)
参数：HomotopicalAlgebra.CofibrantObject.HoCat C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.CofibrantObject.instIsCofibrantResolutionObj`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlg
ebra.ModelCategory C] (X : C),   HomotopicalAlgebra.I…

--- 原说明 ---
A cofibrant resolution functor from a model category to the homotopy category
of cofibrant objects.
-/
noncomputable def HoCat.resolution : C ⥤ CofibrantObject.HoCat C where
  obj X := toHoCat.obj (mk (resolutionObj X))
  map f := toHoCat.map (homMk (resolutionMap f))
  map_id X := by
    rw [← toHoCat.map_id]
    exact resolutionObj_hom_ext (by simpa using .refl _)
  map_comp {X₁ X₂ X₃} f g := by
    rw [← toHoCat.map_comp]
    exact resolutionObj_hom_ext (by simpa using .refl _)

variable (C) in
/-- The cofibrant resolution functor `HoCat.resolution`, as a localizer morphism. -/
@[simps]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.localizerMorphismResolution** 是 Mathl
ib 中的一个定义，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       CategoryTheory.LocalizerMorph
ism (HomotopicalAlgebra.weakEquivalences C)         (HomotopicalAlgebra.weakEqui
valences (HomotopicalAlgebra.CofibrantObject.HoCat C))
参数：HomotopicalAlgebra.CofibrantObject.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofibrant resolution functor `HoCat.resolution`, as a localizer morphism.
-/
noncomputable def HoCat.localizerMorphismResolution :
    LocalizerMorphism (weakEquivalences C)
      (weakEquivalences (CofibrantObject.HoCat C)) where
  functor := HoCat.resolution
  map _ _ _ h := by
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff, HoCat.resolution,
      weakEquivalence_toHoCat_map_iff, weakEquivalence_resolutionMap_iff,
      weakEquivalence_homMk_iff] using h

/-- The map `HoCat.pResolutionObj`, when applied to already cofibrant objects, gives
a natural transformation `ι ⋙ HoCat.resolution ⟶ toHoCat`. -/
@[simps]
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.** 是 Mathlib 中的一个定义，位于命名空间 `Homotopic
alAlgebra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `HoCat.pResolutionObj`, when applied to already cofibrant objects, gives
a natural transformation `ι ⋙ HoCat.resolution ⟶ toHoCat`.
-/
noncomputable def HoCat.ιCompResolutionNatTrans :
    ι ⋙ HoCat.resolution (C := C) ⟶ toHoCat where
  app X := toHoCat.map { hom := (HoCat.pResolutionObj (ι.obj X)) }
  naturality _ _ f := toHoCat.congr_map (by
    ext : 1
    exact HoCat.resolutionMap_fac f.hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) :
    WeakEquivalence (HoCat.ιCompResolutionNatTrans.app X) := by
  dsimp
  rw [weakEquivalence_toHoCat_map_iff, weakEquivalence_iff_of_objectProperty]
  infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : CofibrantObject.HoCat C ⥤ D)
    [L.IsLocalization (weakEquivalences _)] :
    IsIso (Functor.whiskerRight HoCat.ιCompResolutionNatTrans L) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply Localization.inverts L (weakEquivalences _)
  rw [← weakEquivalence_iff]
  infer_instance

section

variable {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- The induced functor `CofibrantObject.HoCat C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.toLocalization** 是 Mathlib 中的一个定义，位于命
名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {D : Type u_2} →         [ins
t_2 : CategoryTheory.Category.{v_2, u_2} D] →           (L : CategoryTheory.Func
tor C D) →             [L.IsLocalization (HomotopicalAlgebra.weakEquivalences C)
] →               CategoryTheory.Functor (HomotopicalAlgebra.CofibrantObject.HoC
at C) D
参数：L : CategoryTheory.Functor C D；HomotopicalAlgebra.weakEquivalences C；Homotopi
calAlgebra.CofibrantObject.HoCat C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced functor `CofibrantObject.HoCat C ⥤ D`, when `D` is a localization
of `C` with respect to weak equivalences.
-/
def HoCat.toLocalization : HoCat C ⥤ D :=
  CategoryTheory.Quotient.lift _ (ι ⋙ L)
    (fun _ _ _ _ h ↦ (factorsThroughLocalization C h).map_eq_of_isInvertedBy _
      (fun _ _ _ ↦ Localization.inverts L (weakEquivalences _) _))

/-- The isomorphism `toHoCat ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of cofibrant objects factors through the homotopy category
of cofibrant objects. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.toHoCatCompToLocalizationIso** 是 Math
lib 中的一个定义，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {D : Type u_2} →         [ins
t_2 : CategoryTheory.Category.{v_2, u_2} D] →           (L : CategoryTheory.Func
tor C D) →             [inst_3 : L.IsLocalization (HomotopicalAlgebra.weakEquiva
lences C)] →               HomotopicalAlgebra.CofibrantObject.toHoCat.comp      
             (HomotopicalAlgebra.CofibrantObject.HoCat.toLocalization L) ≅      
           HomotopicalAlgebra.CofibrantObject.ι.comp L
参数：L : CategoryTheory.Functor C D；HomotopicalAlgebra.weakEquivalences C；Homotopi
calAlgebra.CofibrantObject.HoCat.toLocalization L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `toHoCat ⋙ toLocalization L ≅ ι ⋙ L` which expresses that
if `L : C ⥤ D` is a localization functor, then its restriction on the
full subcategory of cofibrant objects factors through the homotopy category
of cofibrant objects.
-/
def HoCat.toHoCatCompToLocalizationIso : toHoCat ⋙ toLocalization L ≅ ι ⋙ L := Iso.refl _

@[deprecated (since := "2026-01-31")]
alias HoCat.toπCompToLocalizationIso := HoCat.toHoCatCompToLocalizationIso

/-- The natural isomorphism `HoCat.resolution ⋙ HoCat.toLocalization L ⟶ L` when
`L : C ⥤ D` is a localization functor. -/
/-
**HomotopicalAlgebra.CofibrantObject.HoCat.resolutionCompToLocalizationNatTrans*
* 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebra.CofibrantObject.HoCat`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : HomotopicalAlgebra.ModelCategory C] →       {D : Type u_2} →         [ins
t_2 : CategoryTheory.Category.{v_2, u_2} D] →           (L : CategoryTheory.Func
tor C D) →             [inst_3 : L.IsLocalization (HomotopicalAlgebra.weakEquiva
lences C)] →               HomotopicalAlgebra.CofibrantObject.HoCat.resolution.c
omp                   (HomotopicalAlgebra.CofibrantObject.HoCat.toLocalization L
) ⟶                 L
参数：L : CategoryTheory.Functor C D；HomotopicalAlgebra.weakEquivalences C；Homotopi
calAlgebra.CofibrantObject.HoCat.toLocalization L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `HoCat.resolution ⋙ HoCat.toLocalization L ⟶ L` when
`L : C ⥤ D` is a localization functor.
-/
noncomputable def HoCat.resolutionCompToLocalizationNatTrans :
    HoCat.resolution ⋙ HoCat.toLocalization L ⟶ L where
  app X := L.map (pResolutionObj X)
  naturality _ _ f := by
    simpa only [Functor.map_comp] using! L.congr_map (HoCat.resolutionMap_fac f)

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
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
/-- The inclusion `CofibrantObject C ⥤ C`, as a localizer morphism. -/
@[simps]
/-
**HomotopicalAlgebra.CofibrantObject.localizerMorphism** 是 Mathlib 中的一个定义，位于命名空间
 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：localizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantObject C
)) (weakEquivalences C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `CofibrantObject C ⥤ C`, as a localizer morphism.
-/
def localizerMorphism : LocalizerMorphism (weakEquivalences (CofibrantObject C))
    (weakEquivalences C) where
  functor := ι
  map := by rfl

open Functor in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (localizerMorphism C).IsLocalizedEquivalence := by
  let Hcof := (weakEquivalences (HoCat C)).Localization
  let Lcofπ : HoCat C ⥤ Hcof := (weakEquivalences (CofibrantObject.HoCat C)).Q
  let Lcof : CofibrantObject C ⥤ Hcof := toHoCat ⋙ Lcofπ
  let H := (weakEquivalences C).Localization
  let L : C ⥤ H := (weakEquivalences C).Q
  let F := (localizerMorphism C).localizedFunctor Lcof L
  let eF : ι ⋙ L ≅ Lcof ⋙ F := CatCommSq.iso (localizerMorphism C).functor Lcof L F
  let eF' : HoCat.toLocalization L ≅ Lcofπ ⋙ F :=
    CategoryTheory.Quotient.natIsoLift _
      (HoCat.toHoCatCompToLocalizationIso L ≪≫ eF ≪≫ associator _ _ _)
  let G : H ⥤ Hcof := (HoCat.localizerMorphismResolution C).localizedFunctor L Lcofπ
  let eG : HoCat.resolution ⋙ Lcofπ ≅ L ⋙ G :=
    CatCommSq.iso (HoCat.localizerMorphismResolution C).functor L Lcofπ G
  have : Localization.Lifting L (weakEquivalences C)
      (HoCat.resolution ⋙ HoCat.toLocalization L) (G ⋙ F) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eG.symm _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eF'.symm⟩
  have : Localization.Lifting Lcof (weakEquivalences (CofibrantObject C))
        (ι ⋙ HoCat.resolution ⋙ Lcofπ) (F ⋙ G) :=
    ⟨(associator _ _ _).symm ≪≫ isoWhiskerRight eF.symm G ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ eG.symm⟩
  let E : Hcof ≌ H := CategoryTheory.Equivalence.mk F G
    (Localization.liftNatIso Lcof (weakEquivalences _) Lcof (ι ⋙ HoCat.resolution ⋙ Lcofπ) _ _
      ((asIso (whiskerRight HoCat.ιCompResolutionNatTrans Lcofπ)).symm ≪≫
          associator _ _ _))
    (Localization.liftNatIso L (weakEquivalences _)
      (HoCat.resolution ⋙ HoCat.toLocalization L) L _ _
      (asIso (HoCat.resolutionCompToLocalizationNatTrans L)))
  have : F.IsEquivalence := E.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' (localizerMorphism C) Lcof L F

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) :
    IsCofibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (ι ⋙ L).IsLocalization (weakEquivalences (CofibrantObject C)) :=
  inferInstanceAs (((localizerMorphism C).functor ⋙ L).IsLocalization _)

end CofibrantObject

end HomotopicalAlgebra

