/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy

/-!
# Homotopies in model categories

In this file, we relate left and right homotopies between
morphisms `X ⟶ Y` in model categories. In particular, if `X` is cofibrant
and `Y` is fibrant, these notions coincide (for arbitrary choices of good
cylinders or good path objects).

Using the factorization lemma by K. S. Brown, we deduce versions of the Whitehead
theorem (`LeftHomotopyClass.whitehead` and `RightHomotopyClass.whitehead`)
which assert that when both `X` and `Y` are fibrant and cofibrant,
then any weak equivalence `X ⟶ Y` is a homotopy equivalence.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y Z : C}

namespace LeftHomotopyRel

variable {f g : X ⟶ Y} [IsCofibrant X]

set_option backward.isDefEq.respectTransparency false in
/-- When two morphisms `X ⟶ Y` with `X` cofibrant are related by a left homotopy,
this is a choice of a right homotopy relative to any good path object for `Y`. -/
/-
**HomotopicalAlgebra.LeftHomotopyRel.rightHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.LeftHomotopyRel`。
形式化陈述：rightHomotopy (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.IsGood] : Q.
RightHomotopy f g
参数：h : LeftHomotopyRel f g；Q : PathObject Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.exists_good_cylinder`：exists_good_cyl
inder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : exists (P : Cy
linder X), P.IsGood ∧ Nonempty (P.LeftHomotop…

--- 原说明 ---
When two morphisms `X ⟶ Y` with `X` cofibrant are related by a left homotopy,
this is a choice of a right homotopy relative to any good path object for `Y`.
-/
noncomputable def rightHomotopy (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.IsGood] :
    Q.RightHomotopy f g :=
  let P := h.exists_good_cylinder.choose
  have h := h.exists_good_cylinder.choose_spec.2.some
  have h' := h.exists_good_cylinder.choose_spec.1
  have sq : CommSq (f ≫ Q.ι) P.i₀ Q.p (prod.lift (P.π ≫ f) h.h) := { }
  { h := P.i₁ ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      rw [Category.assoc, Q.p_fst, prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      rw [Category.assoc, Q.p_snd, prod.lift_snd] at this
      simp [this] }
/-
**HomotopicalAlgebra.LeftHomotopyRel.rightHomotopyRel** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.LeftHomotopyRel`。
形式化陈述：rightHomotopyRel (h : LeftHomotopyRel f g) : RightHomotopyRel f g
参数：h : LeftHomotopyRel f g。
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
· 使用引理 `HomotopicalAlgebra.PathObject.exists_very_good`：exists_very_good : exist
s (P : PathObject A), P.IsVeryGood
· 使用定理 `HomotopicalAlgebra.PathObject.IsVeryGood.toIsGood`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Categ
oryWithWeakEquivalences C} {P : Homotop…
-/
lemma rightHomotopyRel (h : LeftHomotopyRel f g) : RightHomotopyRel f g := by
  obtain ⟨P, _⟩ := PathObject.exists_very_good Y
  exact ⟨_, ⟨h.rightHomotopy P⟩⟩

end LeftHomotopyRel

namespace RightHomotopyRel

variable {f g : X ⟶ Y} [IsFibrant Y]

set_option backward.isDefEq.respectTransparency false in
/-- When two morphisms `X ⟶ Y` with `Y` fibrant are related by a right homotopy,
this is a choice of a left homotopy relative to any good cylinder object for `X`. -/
/-
**HomotopicalAlgebra.RightHomotopyRel.leftHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Ho
motopicalAlgebra.RightHomotopyRel`。
形式化陈述：leftHomotopy (h : RightHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] : Q.Le
ftHomotopy f g
参数：h : RightHomotopyRel f g；Q : Cylinder X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_good_pathObject`：exists_good_
pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) : exists (
P : PathObject Y), P.IsGood ∧ Nonempty (P.RightH…

--- 原说明 ---
When two morphisms `X ⟶ Y` with `Y` fibrant are related by a right homotopy,
this is a choice of a left homotopy relative to any good cylinder object for `X`
.
-/
noncomputable def leftHomotopy (h : RightHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] :
    Q.LeftHomotopy f g :=
  let P := h.exists_good_pathObject.choose
  have h := h.exists_good_pathObject.choose_spec.2.some
  have h' := h.exists_good_pathObject.choose_spec.1
  have sq : CommSq (coprod.desc (f ≫ P.ι) h.h) Q.i P.p₀ (Q.π ≫ f) := { }
  { h := sq.lift ≫ P.p₁
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      rw [Q.inl_i_assoc, coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      rw [Q.inr_i_assoc, coprod.inr_desc] at this
      simp [reassoc_of% this, P] }
/-
**HomotopicalAlgebra.RightHomotopyRel.leftHomotopyRel** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.RightHomotopyRel`。
形式化陈述：leftHomotopyRel (h : RightHomotopyRel f g) : LeftHomotopyRel f g
参数：h : RightHomotopyRel f g。
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
· 使用引理 `HomotopicalAlgebra.Cylinder.exists_very_good`：exists_very_good : exists 
(P : Cylinder A), P.IsVeryGood
· 使用定理 `HomotopicalAlgebra.Cylinder.IsVeryGood.toIsGood`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Categor
yWithWeakEquivalences C} {P : Homotop…
-/
lemma leftHomotopyRel (h : RightHomotopyRel f g) : LeftHomotopyRel f g := by
  obtain ⟨P, _⟩ := Cylinder.exists_very_good X
  exact ⟨P, ⟨h.leftHomotopy P⟩⟩

end RightHomotopyRel

section

variable {f g : X ⟶ Y} [IsCofibrant X] [IsFibrant Y]

/-
**HomotopicalAlgebra.leftHomotopyRel_iff_rightHomotopyRel** 是 Mathlib 中的一个引理，位于命
名空间 `HomotopicalAlgebra`。
形式化陈述：leftHomotopyRel_iff_rightHomotopyRel : LeftHomotopyRel f g ↔ RightHomotopy
Rel f g
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
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.rightHomotopyRel`：rightHomotopyRel (h
 : LeftHomotopyRel f g) : RightHomotopyRel f g
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.leftHomotopyRel`：leftHomotopyRel (h 
: RightHomotopyRel f g) : LeftHomotopyRel f g
-/
lemma leftHomotopyRel_iff_rightHomotopyRel :
    LeftHomotopyRel f g ↔ RightHomotopyRel f g :=
  ⟨fun h ↦ h.rightHomotopyRel, fun h ↦ h.leftHomotopyRel⟩

/-- When two morphisms `X ⟶ Y` with `X` cofibrant and `Y` fibrant are related
by a left homotopy, this is a choice of a left homotopy relative
to any good cylinder object for `X`. -/
/-
**HomotopicalAlgebra.LeftHomotopyRel.leftHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Hom
otopicalAlgebra.LeftHomotopyRel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       {X Y : C} →         {f g : X ⟶ Y} →
           [HomotopicalAlgebra.IsCofibrant X] →             [HomotopicalAlgebra.
IsFibrant Y] →               HomotopicalAlgebra.LeftHomotopyRel f g →           
      (Q : HomotopicalAlgebra.Cylinder X) → [Q.IsGood] → Q.LeftHomotopy f g
参数：Q : HomotopicalAlgebra.Cylinder X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When two morphisms `X ⟶ Y` with `X` cofibrant and `Y` fibrant are related
by a left homotopy, this is a choice of a left homotopy relative
to any good cylinder object for `X`.
-/
noncomputable def LeftHomotopyRel.leftHomotopy
    (h : LeftHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] :
    Q.LeftHomotopy f g :=
  RightHomotopyRel.leftHomotopy (by rwa [← leftHomotopyRel_iff_rightHomotopyRel]) _

/-- When two morphisms `X ⟶ Y` with `X` cofibrant and `Y` fibrant are related
by a right homotopy, this is a choice of a right homotopy relative
to any good path object for `Y`. -/
/-
**HomotopicalAlgebra.RightHomotopyRel.rightHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `H
omotopicalAlgebra.RightHomotopyRel`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 HomotopicalAlgebra.ModelCategory C] →       {X Y : C} →         {f g : X ⟶ Y} →
           [HomotopicalAlgebra.IsCofibrant X] →             [HomotopicalAlgebra.
IsFibrant Y] →               HomotopicalAlgebra.RightHomotopyRel f g →          
       (P : HomotopicalAlgebra.PathObject Y) → [P.IsGood] → P.RightHomotopy f g
参数：P : HomotopicalAlgebra.PathObject Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When two morphisms `X ⟶ Y` with `X` cofibrant and `Y` fibrant are related
by a right homotopy, this is a choice of a right homotopy relative
to any good path object for `Y`.
-/
noncomputable def RightHomotopyRel.rightHomotopy
    (h : RightHomotopyRel f g) (P : PathObject Y) [P.IsGood] :
    P.RightHomotopy f g :=
  LeftHomotopyRel.rightHomotopy (by rwa [leftHomotopyRel_iff_rightHomotopyRel]) _

end

namespace LeftHomotopyClass

variable (X)

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEq
uivalence** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra.LeftHomotopyClass`。
形式化陈述：postcomp_bijective_of_fibration_of_weakEquivalence [IsCofibrant X] (g : Y 
⟶ Z) [Fibration g] [WeakEquivalence g] : Function.Bijective (fun (f : LeftHomoto
pyClass X Y) => f.postcomp g)
参数：g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteColim…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.LeftHomotopyClass.mk_surjective`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C],   Functio…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.exists_good_cylinder`：exists_good_cyl
inder [ModelCategory C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) : exists (P : Cy
linder X), P.IsGood ∧ Nonempty (P.LeftHomotop…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `HomotopicalAlgebra.Precylinder.inl_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopicalAlgebra.Precylinder.inr_i_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {A : C} (P : HomotopicalAlgebra.Precylinder A)   [i
nst_1 : CategoryTheory.Limits.Ha…
· 使用定理 `HomotopicalAlgebra.Precylinder.LeftHomotopy.h₁`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C} {P : HomotopicalAlgebra.Precylinder X} 
{Y : C}   {f g : X ⟶ Y} (self : P.Le…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelCa
tegory C] [IsCofibrant X] (f g : X ⟶ Y) : mk f = mk g ↔ LeftHomotopyRel f g
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4b`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.Cylinder.IsGood.cofibration_i`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Catego
ryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
-/
lemma postcomp_bijective_of_fibration_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [Fibration g] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp g) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [postcomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
    have sq : CommSq (coprod.desc f₀ f₁) P.i g h.h := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := coprod.inl ≫= sq.fac_left
          rwa [P.inl_i_assoc, coprod.inl_desc] at this
        h₁ := by
          have := coprod.inr ≫= sq.fac_left
          rwa [P.inr_i_assoc, coprod.inr_desc] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq (initial.to Y) (initial.to X) g φ := { }
    exact ⟨mk sq.lift, by simp⟩
/-
**HomotopicalAlgebra.LeftHomotopyClass.postcomp_bijective_of_weakEquivalence** 是
 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra.LeftHomotopyClass`。
形式化陈述：postcomp_bijective_of_weakEquivalence [IsCofibrant X] (g : Y ⟶ Z) [IsFibra
nt Y] [IsFibrant Z] [WeakEquivalence g] : Function.Bijective (fun (f : LeftHomot
opyClass X Y) => f.postcomp g)
参数：g : Y ⟶ Z。
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
· 使用定理 `HomotopicalAlgebra.FibrantBrownFactorization.instNonemptyOfIsFibrant`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopic
alAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y) [Homoto…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyClass.postcomp_bijective_of_fibration_of_
weakEquivalence`：postcomp_bijective_of_fibration_of_weakEquivalence [IsCofibrant
 X] (g : Y ⟶ Z) [Fibration g] [WeakEquivalence g] : Function.Bijective (fun (…
· 使用定理 `HomotopicalAlgebra.FibrantBrownFactorization.fibration_r`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.Mo
delCategory C] {X Y : C}   {f : X ⟶ Y} (self :…
· 使用定理 `HomotopicalAlgebra.FibrantBrownFactorization.instWeakEquivalenceR`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalA
lgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y) (h : Ho…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomotopicalAlgebra.LeftHomotopyClass.mk_surjective`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C],   Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomotopicalAlgebra.FibrantBrownFactorization.i_r`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.ModelCateg
ory C] {X Y : C}   {f : X ⟶ Y} (self :…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `HomotopicalAlgebra.instFibrationPTrivialCofibrationsFibrations`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.FibrantBrownFactorization.instWeakEquivalencePTrivial
CofibrationsFibrations`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u
_1} C] [inst_1 : HomotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y) (h 
: Ho…
-/
lemma postcomp_bijective_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [IsFibrant Y] [IsFibrant Z] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp g) := by
  let h : FibrantBrownFactorization g := Classical.arbitrary _
  have hi : Function.Bijective (fun (f : LeftHomotopyClass X Y) ↦ f.postcomp h.i) := by
    rw [← Function.Bijective.of_comp_iff'
      (postcomp_bijective_of_fibration_of_weakEquivalence X h.r)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (postcomp_bijective_of_fibration_of_weakEquivalence X h.p).comp hi using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

end LeftHomotopyClass

namespace RightHomotopyClass

variable (Z)

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_cofibration_of_weak
Equivalence** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra.RightHomotopyClass`。
形式化陈述：precomp_bijective_of_cofibration_of_weakEquivalence [IsFibrant Z] (f : X ⟶
 Y) [Cofibration f] [WeakEquivalence f] : Function.Bijective (fun (g : RightHomo
topyClass Y Z) => g.precomp f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm1a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C],   CategoryT
heory.Limits.HasFiniteLimit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HomotopicalAlgebra.RightHomotopyClass.mk_surjective`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.C
ategoryWithWeakEquivalences C],   Functio…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `HomotopicalAlgebra.RightHomotopyRel.exists_good_pathObject`：exists_good_
pathObject [ModelCategory C] {f g : X ⟶ Y} (h : RightHomotopyRel f g) : exists (
P : PathObject Y), P.IsGood ∧ Nonempty (P.RightH…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_fst`：p_fst : P.p ≫ prod.fst = P.p₀
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₀`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomotopicalAlgebra.PrepathObject.p_snd`：p_snd : P.p ≫ prod.snd = P.p₁
· 使用定理 `HomotopicalAlgebra.PrepathObject.RightHomotopy.h₁`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {Y : C} {P : HomotopicalAlgebra.PrepathObjec
t Y} {X : C}   {f g : X ⟶ Y} (self : P.…
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelC
ategory C] [IsFibrant Y] (f g : X ⟶ Y) : mk f = mk g ↔ RightHomotopyRel f g
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `HomotopicalAlgebra.ModelCategory.cm4a`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} [self : HomotopicalAlgebra.ModelCategory C] {A B X Y : C
}   (i : A ⟶ B) (p : X ⟶ Y)…
· 使用定理 `HomotopicalAlgebra.PathObject.IsGood.fibration_p`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} {A : C}   {inst_1 : HomotopicalAlgebra.Catego
ryWithWeakEquivalences C} {P : Homotop…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
-/
lemma precomp_bijective_of_cofibration_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp f) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [precomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
    have sq : CommSq h.h f P.p (prod.lift f₀ f₁) := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := sq.fac_right =≫ prod.fst
          rwa [Category.assoc, P.p_fst, prod.lift_fst] at this
        h₁ := by
          have := sq.fac_right =≫ prod.snd
          rwa [Category.assoc, P.p_snd, prod.lift_snd] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq φ f (terminal.from _) (terminal.from _) := { }
    exact ⟨mk sq.lift, by simp⟩
/-
**HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_weakEquivalence** 是
 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebra.RightHomotopyClass`。
形式化陈述：precomp_bijective_of_weakEquivalence [IsFibrant Z] (f : X ⟶ Y) [IsCofibran
t X] [IsCofibrant Y] [WeakEquivalence f] : Function.Bijective (fun (g : RightHom
otopyClass Y Z) => g.precomp f)
参数：f : X ⟶ Y。
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
· 使用定理 `HomotopicalAlgebra.CofibrantBrownFactorization.instNonemptyOfIsCofibrant
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homot
opicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y) [Homoto…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_cofibration_o
f_weakEquivalence`：precomp_bijective_of_cofibration_of_weakEquivalence [IsFibran
t Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] : Function.Bijective (fun …
· 使用定理 `HomotopicalAlgebra.CofibrantBrownFactorization.cofibration_s`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebr
a.ModelCategory C] {X Y : C}   {f : X ⟶ Y} (self :…
· 使用定理 `HomotopicalAlgebra.CofibrantBrownFactorization.instWeakEquivalenceS`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Homotopica
lAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y) (h : Ho…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomotopicalAlgebra.RightHomotopyClass.mk_surjective`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.C
ategoryWithWeakEquivalences C],   Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomotopicalAlgebra.CofibrantBrownFactorization.s_p_assoc`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : HomotopicalAlgebra.Mo
delCategory C] {X Y : C}   {f : X ⟶ Y} (self :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.M
orphismProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `HomotopicalAlgebra.instCofibrationICofibrationsTrivialFibrations`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : HomotopicalAlgebra.
CategoryWithWeakEquivalences C]   [inst_2 : Homotopica…
· 使用定理 `HomotopicalAlgebra.CofibrantBrownFactorization.instWeakEquivalenceICofib
rationsTrivialFibrations`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} C] [inst_1 : HomotopicalAlgebra.ModelCategory C] {X Y : C}   (f : X ⟶ Y) (
h : Ho…
-/
lemma precomp_bijective_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp f) := by
  let h : CofibrantBrownFactorization f := Classical.arbitrary _
  have hj : Function.Bijective (fun (g : RightHomotopyClass Y Z) ↦ g.precomp h.p) := by
    rw [← Function.Bijective.of_comp_iff'
      (precomp_bijective_of_cofibration_of_weakEquivalence Z h.s)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (precomp_bijective_of_cofibration_of_weakEquivalence Z h.i).comp hj using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp
/-
**HomotopicalAlgebra.RightHomotopyClass.whitehead** 是 Mathlib 中的一个引理，位于命名空间 `Hom
otopicalAlgebra.RightHomotopyClass`。
形式化陈述：whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y] (f :
 X ⟶ Y) [WeakEquivalence f] : exists (g : Y ⟶ X), RightHomotopyRel (f ≫ g) (𝟙 X)
 ∧ RightHomotopyRel (g ≫ f) (𝟙 Y)
参数：f : X ⟶ Y。
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
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_weakEquivalen
ce`：precomp_bijective_of_weakEquivalence [IsFibrant Z] (f : X ⟶ Y) [IsCofibrant 
X] [IsCofibrant Y] [WeakEquivalence f] : Function.Bijective (fun…
· 使用定理 `HomotopicalAlgebra.RightHomotopyClass.mk_surjective`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : HomotopicalAlgebra.C
ategoryWithWeakEquivalences C],   Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.mk_eq_mk_iff`：mk_eq_mk_iff [ModelC
ategory C] [IsFibrant Y] (f g : X ⟶ Y) : mk f = mk g ↔ RightHomotopyRel f g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomotopicalAlgebra.leftHomotopyRel_iff_rightHomotopyRel`：leftHomotopyRel
_iff_rightHomotopyRel : LeftHomotopyRel f g ↔ RightHomotopyRel f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `HomotopicalAlgebra.LeftHomotopyRel.postcomp`：postcomp [CategoryWithWeakE
quivalences C] {f g : X ⟶ Y} (h : LeftHomotopyRel f g) {Z : C} (p : Y ⟶ Z) : Lef
tHomotopyRel (f ≫ p) (g ≫ p)
-/
lemma whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] :
    ∃ (g : Y ⟶ X), RightHomotopyRel (f ≫ g) (𝟙 X) ∧ RightHomotopyRel (g ≫ f) (𝟙 Y) := by
  obtain ⟨g, hg⟩ := (precomp_bijective_of_weakEquivalence X f).2 (.mk (𝟙 X))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  dsimp at hg
  refine ⟨g, by rwa [← mk_eq_mk_iff], ?_⟩
  rw [← mk_eq_mk_iff]
  apply (precomp_bijective_of_weakEquivalence Y f).1
  simp only [precomp_mk, Category.comp_id]
  rw [mk_eq_mk_iff, ← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
  simpa using hg.postcomp f

end RightHomotopyClass

/-
**HomotopicalAlgebra.LeftHomotopyClass.whitehead** 是 Mathlib 中的一个定理，位于命名空间 `Homo
topicalAlgebra.LeftHomotopyClass`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Homotop
icalAlgebra.ModelCategory C] {X Y : C}   [HomotopicalAlgebra.IsCofibrant X] [Hom
otopicalAlgebra.IsCofibrant Y] [HomotopicalAlgebra.IsFibrant X]   [HomotopicalAl
gebra.IsFibrant Y] (f : X ⟶ Y) [HomotopicalAlgebra.WeakEquivalence f],   ∃ g,   
  HomotopicalAlgebra.LeftHomotopyRel (CategoryTheory.CategoryStruct.comp f g) (C
ategoryTheory.CategoryStruct.id X) ∧       HomotopicalAlgebra.LeftHomotopyRel (C
ategoryTheory.CategoryStruct.comp g f) (CategoryTheory.CategoryStruct.id Y)
参数：f : X ⟶ Y；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.CategoryStruc
t.id X；CategoryTheory.CategoryStruct.comp g f；CategoryTheory.CategoryStruct.id Y
。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomotopicalAlgebra.RightHomotopyClass.whitehead`：whitehead [IsCofibrant 
X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
 exists (g : Y ⟶ X), RightHomotopyRel…
-/
lemma LeftHomotopyClass.whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] :
    ∃ (g : Y ⟶ X), LeftHomotopyRel (f ≫ g) (𝟙 X) ∧ LeftHomotopyRel (g ≫ f) (𝟙 Y) := by
  simp only [leftHomotopyRel_iff_rightHomotopyRel]
  apply RightHomotopyClass.whitehead

section

variable [IsCofibrant X] [IsFibrant Y]

/-- Left homotopy classes of maps `X ⟶ Y` identify to right homotopy classes
when `X` is cofibrant and `Y` is fibrant. -/
/-
**HomotopicalAlgebra.leftHomotopyClassEquivRightHomotopyClass** 是 Mathlib 中的一个定义
，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：leftHomotopyClassEquivRightHomotopyClass : LeftHomotopyClass X Y ≃ RightHo
motopyClass X Y where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopy classes of maps `X ⟶ Y` identify to right homotopy classes
when `X` is cofibrant and `Y` is fibrant.
-/
def leftHomotopyClassEquivRightHomotopyClass :
    LeftHomotopyClass X Y ≃ RightHomotopyClass X Y where
  toFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
/-
**HomotopicalAlgebra.leftHomotopyClassEquivRightHomotopyClass_mk** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：leftHomotopyClassEquivRightHomotopyClass_mk (f : X ⟶ Y) : leftHomotopyClas
sEquivRightHomotopyClass (.mk f) = .mk f
参数：f : X ⟶ Y。
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
-/
lemma leftHomotopyClassEquivRightHomotopyClass_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass (.mk f) = .mk f := rfl

@[simp]
/-
**HomotopicalAlgebra.leftHomotopyClassEquivRightHomotopyClass_symm_mk** 是 Mathli
b 中的一个引理，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：leftHomotopyClassEquivRightHomotopyClass_symm_mk (f : X ⟶ Y) : leftHomotop
yClassEquivRightHomotopyClass.symm (.mk f) = .mk f
参数：f : X ⟶ Y。
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
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma leftHomotopyClassEquivRightHomotopyClass_symm_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass.symm (.mk f) = .mk f := rfl

end

end HomotopicalAlgebra

