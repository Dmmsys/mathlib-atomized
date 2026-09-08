/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.LinearAlgebra.Coevaluation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The category of finitely generated modules over a ring

This introduces `FGModuleCat R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `ModuleCat R`.

When `K` is a field,
`FGModuleCat K` is the category of finite-dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `FGModuleCat R` is abelian when `R` is (left)-Noetherian.

-/

@[expose] public section


noncomputable section

open CategoryTheory Module

universe v w u

section Ring

variable (R : Type u) [Ring R]

/-- Finitely generated modules, as a property of objects of `ModuleCat R`. -/
/-
**ModuleCat.isFG** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModuleCat.isFG : ObjectProperty (ModuleCat.{v} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finitely generated modules, as a property of objects of `ModuleCat R`.
-/
def ModuleCat.isFG : ObjectProperty (ModuleCat.{v} R) :=
  fun V ↦ Module.Finite R V

variable {R} in
/-
**ModuleCat.isFG_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.isFG_iff (V : ModuleCat.{v} R) : isFG R V ↔ Module.Finite R V
参数：V : ModuleCat.{v} R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ModuleCat.isFG_iff (V : ModuleCat.{v} R) :
    isFG R V ↔ Module.Finite R V := Iff.rfl

/-- The category of finitely generated modules. -/
/-
**FGModuleCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FGModuleCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finitely generated modules.
-/
abbrev FGModuleCat := (ModuleCat.isFG.{v} R).FullSubcategory

variable {R}

/-- A synonym for `M.obj.carrier`, which we can mark with `@[coe]`. -/
@[reducible]
/-
**FGModuleCat.carrier** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FGModuleCat.carrier (M : FGModuleCat.{v} R) : Type v
参数：M : FGModuleCat.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A synonym for `M.obj.carrier`, which we can mark with `@[coe]`.
-/
def FGModuleCat.carrier (M : FGModuleCat.{v} R) : Type v := M.obj.carrier
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (FGModuleCat.{v} R) (Type v) :=
  ⟨FGModuleCat.carrier⟩

attribute [coe] FGModuleCat.carrier
/-
**FGModuleCat.obj_carrier** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] (M : FGModuleCat R), ↑M.obj = ↑M
参数：M : FGModuleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma FGModuleCat.obj_carrier (M : FGModuleCat.{v} R) : M.obj.carrier = M.carrier := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : FGModuleCat.{v} R) : Module.Finite R M :=
  M.property

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

/-
**FGModuleCat.hom_hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ (R : Type u) [inst : Ring R] {A B C : FGModuleCat R} (f : A ⟶ B) (g : B 
⟶ C),   ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp f g).hom = ModuleC
at.Hom.hom g.hom ∘ₗ ModuleCat.Hom.hom f.hom
参数：R : Type u；f : A ⟶ B；g : B ⟶ C；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_hom_comp {A B C : FGModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl
/-
**FGModuleCat.hom_hom_id** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (A : FGModuleCat R),   ModuleCat.Hom.hom (C
ategoryTheory.CategoryStruct.id A).hom = LinearMap.id
参数：R : Type u；A : FGModuleCat R；CategoryTheory.CategoryStruct.id A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_hom_id (A : FGModuleCat.{v} R) : (𝟙 A : A ⟶ A).hom.hom = LinearMap.id := rfl
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FGModuleCat.{v} R) :=
  ⟨⟨ModuleCat.of R PUnit, by unfold ModuleCat.isFG; infer_instance⟩⟩

/-- Lift an unbundled finitely generated module to `FGModuleCat R`. -/
/-
**FGModuleCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `FGModuleCat`。
形式化陈述：of (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModu
leCat R
参数：V : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an unbundled finitely generated module to `FGModuleCat R`.
-/
abbrev of (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
  ⟨ModuleCat.of R V, inferInstanceAs <| Module.Finite R V⟩

@[simp]
/-
**FGModuleCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `FGModuleCat`。
形式化陈述：of_carrier (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] 
: of R V = V
参数：V : Type v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] :
    of R V = V := rfl

variable {R} in
/-- Lift a linear map between finitely generated modules to `FGModuleCat R`. -/
/-
**FGModuleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `FGModuleCat`。
形式化陈述：ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V] [Ad
dCommGroup W] [Module R W] [Module.Finite R W] (f : V ->ₗ[R] W) : of R V ⟶ of R 
W
参数：f : V ->ₗ[R] W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a linear map between finitely generated modules to `FGModuleCat R`.
-/
abbrev ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : V →ₗ[R] W) : of R V ⟶ of R W :=
  ConcreteCategory.ofHom f

variable {R} in
/-
**FGModuleCat.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {V W : FGModuleCat R} {f g : V ⟶ W},   Modu
leCat.Hom.hom f.hom = ModuleCat.Hom.hom g.hom → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
-/
@[ext] lemma hom_ext {V W : FGModuleCat.{v} R} {f g : V ⟶ W} (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : FGModuleCat.{v} R) : Module.Finite R V :=
  V.property
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

variable {R} in
/-- Converts an isomorphism in the category `FGModuleCat R` to
a `LinearEquiv` between the underlying modules. -/
/-
**FGModuleCat.isoToLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：isoToLinearEquiv {V W : FGModuleCat.{v} R} (i : V ≅ W) : V ≃ₗ[R] W
参数：i : V ≅ W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts an isomorphism in the category `FGModuleCat R` to
a `LinearEquiv` between the underlying modules.
-/
def isoToLinearEquiv {V W : FGModuleCat.{v} R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

variable {R} in
/-- Converts a `LinearEquiv` to an isomorphism in the category `FGModuleCat R`. -/
@[simps]
/-
**FGModuleCat._root_.LinearEquiv.toFGModuleCatIso** 是 Mathlib 中的一个定义，位于命名空间 `FGM
oduleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `LinearEquiv` to an isomorphism in the category `FGModuleCat R`.
-/
def _root_.LinearEquiv.toFGModuleCatIso
    {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

/-- Universe lifting as a functor on `FGModuleCat`. -/
/-
**FGModuleCat.ulift** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：ulift : FGModuleCat.{v} R ⥤ FGModuleCat.{max v w} R where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universe lifting as a functor on `FGModuleCat`.
-/
def ulift : FGModuleCat.{v} R ⥤ FGModuleCat.{max v w} R where
  obj M := .of R <| ULift M
  map f := ofHom <| ULift.moduleEquiv.symm.toLinearMap ∘ₗ f.hom.hom ∘ₗ ULift.moduleEquiv.toLinearMap

/-- Universe lifting is fully faithful. -/
/-
**FGModuleCat.fullyFaithfulULift** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：fullyFaithfulULift : (ulift R).FullyFaithful where preimage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universe lifting is fully faithful.
-/
def fullyFaithfulULift : (ulift R).FullyFaithful where
  preimage f := ofHom <| ULift.moduleEquiv.toLinearMap ∘ₗ f.hom.hom ∘ₗ
    ULift.moduleEquiv.symm.toLinearMap
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ulift R).Faithful :=
  (fullyFaithfulULift R).faithful
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ulift R).Full :=
  (fullyFaithfulULift R).full

end Ring

section CommRing

variable (R : Type u) [CommRing R]

/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ModuleCat.isFG R).IsMonoidal where
  prop_unit := Module.Finite.self R
  prop_tensor X Y (_ : Module.Finite _ _) (_ : Module.Finite _ _) :=
    Module.Finite.tensorProduct R X Y

open MonoidalCategory
/-
**FGModuleCat.tensorUnit_obj** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ (R : Type u) [inst : CommRing R],   (CategoryTheory.MonoidalCategoryStru
ct.tensorUnit (FGModuleCat R)).obj =     CategoryTheory.MonoidalCategoryStruct.t
ensorUnit (ModuleCat R)
参数：R : Type u；CategoryTheory.MonoidalCategoryStruct.tensorUnit (FGModuleCat R)；M
oduleCat R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
-/
@[simp] lemma tensorUnit_obj : (𝟙_ (FGModuleCat R)).obj = 𝟙_ (ModuleCat R) := rfl
/-
**FGModuleCat.tensorObj_obj** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] (M N : FGModuleCat R),   (CategoryTheor
y.MonoidalCategoryStruct.tensorObj M N).obj =     CategoryTheory.MonoidalCategor
yStruct.tensorObj M.obj N.obj
参数：R : Type u；M N : FGModuleCat R；CategoryTheory.MonoidalCategoryStruct.tensorOb
j M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
-/
@[simp] lemma tensorObj_obj (M N : FGModuleCat.{u} R) : (M ⊗ N).obj = (M.obj ⊗ N.obj) := rfl
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive where
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Linear R where
/-
**FGModuleCat.Iso.conj_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat.Iso`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] {V W : FGModuleCat R} (i : V ≅ W) (f : 
CategoryTheory.End V),   i.conj f = FGModuleCat.ofHom ((FGModuleCat.isoToLinearE
quiv i).conj (ModuleCat.Hom.hom f.hom))
参数：R : Type u；i : V ≅ W；f : CategoryTheory.End V；(FGModuleCat.isoToLinearEquiv i
).conj (ModuleCat.Hom.hom f.hom)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.conj_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = FGModuleCat.ofHom (LinearEquiv.conj (isoToLinearEquiv i) f.hom.hom) :=
  rfl
/-
**FGModuleCat.Iso.conj_hom_eq_conj** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat.Iso`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] {V W : FGModuleCat R} (i : V ≅ W) (f : 
CategoryTheory.End V),   ModuleCat.Hom.hom (i.conj f).hom = (FGModuleCat.isoToLi
nearEquiv i).conj (ModuleCat.Hom.hom f.hom)
参数：R : Type u；i : V ≅ W；f : CategoryTheory.End V；i.conj f；FGModuleCat.isoToLinea
rEquiv i；ModuleCat.Hom.hom f.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.conj_hom_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    (Iso.conj i f).hom.hom = (LinearEquiv.conj (isoToLinearEquiv i) f.hom.hom) :=
  rfl

end CommRing

section Field

variable (K : Type u) [Field K]

/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V W : FGModuleCat.{v} K) : Module.Finite K (V.obj ⟶ W.obj) :=
  ((inferInstance : Module.Finite K (V →ₗ[K] W))).equiv ModuleCat.homLinearEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V W : FGModuleCat.{v} K) : Module.Finite K (V ⟶ W) :=
  ((inferInstance : Module.Finite K (V.obj ⟶ W.obj))).equiv
    InducedCategory.homLinearEquiv.symm
/-
**FGModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ModuleCat.isFG K).IsMonoidalClosed where
  prop_ihom {X Y} (_ : Module.Finite _ _) (_ : Module.Finite _ _) :=
    ((inferInstance : Module.Finite K (X →ₗ[K] Y))).equiv ModuleCat.homLinearEquiv.symm

variable (V W : FGModuleCat K)

@[simp]
/-
**FGModuleCat.ihom_obj** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：ihom_obj : (ihom V).obj W = FGModuleCat.of K (V.obj ⟶ W.obj)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用定理 `FGModuleCat.instIsMonoidalClosedModuleCatIsFG`：∀ (K : Type u) [inst : Fi
eld K], (ModuleCat.isFG K).IsMonoidalClosed
-/
theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V.obj ⟶ W.obj) :=
  rfl

/-- The dual module is the dual in the rigid monoidal category `FGModuleCat K`. -/
/-
**FGModuleCat.FGModuleCatDual** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：FGModuleCatDual : FGModuleCat K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual module is the dual in the rigid monoidal category `FGModuleCat K`.
-/
def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩
/-
**FGModuleCat.FGModuleCatDual_obj** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ (K : Type u) [inst : Field K] (V : FGModuleCat K),   (FGModuleCat.FGModu
leCatDual K V).obj = ModuleCat.of K (Module.Dual K ↑V)
参数：K : Type u；V : FGModuleCat K；FGModuleCat.FGModuleCatDual K V；Module.Dual K ↑V
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma FGModuleCatDual_obj : (FGModuleCatDual K V).obj = ModuleCat.of K (Module.Dual K V) :=
  rfl
/-
**FGModuleCat.FGModuleCatDual_coe** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
形式化陈述：∀ (K : Type u) [inst : Field K] (V : FGModuleCat K), ↑(FGModuleCat.FGModul
eCatDual K V) = Module.Dual K ↑V
参数：K : Type u；V : FGModuleCat K；FGModuleCat.FGModuleCatDual K V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma FGModuleCatDual_coe : (FGModuleCatDual K V : Type u) = Module.Dual K V := rfl

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `LinearAlgebra.coevaluation`. -/
/-
**FGModuleCat.FGModuleCatCoevaluation** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V otimes FGModuleCatDual K 
V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coevaluation map is defined in `LinearAlgebra.coevaluation`.
-/
def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V ⊗ FGModuleCatDual K V :=
  ConcreteCategory.ofHom <| coevaluation K V
/-
**FGModuleCat.FGModuleCatCoevaluation_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `FGMod
uleCat`。
形式化陈述：FGModuleCatCoevaluation_apply_one : (FGModuleCatCoevaluation K V).hom (1 :
 K) = ∑ i : Basis.ofVectorSpaceIndex K V, (Basis.ofVectorSpace K V) i otimesₜ[K]
 (Basis.ofVectorSpace K V).coord i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `coevaluation_apply_one`：coevaluation_apply_one : (coevaluation K V) (1 :
 K) = let bV
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
-/
theorem FGModuleCatCoevaluation_apply_one :
    (FGModuleCatCoevaluation K V).hom (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V,
        (Basis.ofVectorSpace K V) i ⊗ₜ[K] (Basis.ofVectorSpace K V).coord i :=
  coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
/-
**FGModuleCat.FGModuleCatEvaluation** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：FGModuleCatEvaluation : FGModuleCatDual K V otimes V ⟶ 𝟙_ (FGModuleCat K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation morphism is given by the contraction map.
-/
def FGModuleCatEvaluation : FGModuleCatDual K V ⊗ V ⟶ 𝟙_ (FGModuleCat K) :=
  ConcreteCategory.ofHom <| contractLeft K V
/-
**FGModuleCat.FGModuleCatEvaluation_apply** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat
`。
形式化陈述：FGModuleCatEvaluation_apply (f : FGModuleCatDual K V) (x : V) : (FGModuleC
atEvaluation K V).hom (f otimesₜ x) = f.toFun x
参数：f : FGModuleCatDual K V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contractLeft_apply`：contractLeft_apply (f : Module.Dual R M) (m : M) : c
ontractLeft R M (f otimesₜ m) = f m
-/
theorem FGModuleCatEvaluation_apply (f : FGModuleCatDual K V) (x : V) :
    (FGModuleCatEvaluation K V).hom (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

set_option backward.isDefEq.respectTransparency false in
/-- `@[simp]`-normal form of `FGModuleCatEvaluation_apply`, where the carriers have been unfolded.
-/
@[simp]
/-
**FGModuleCat.FGModuleCatEvaluation_apply'** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCa
t`。
形式化陈述：FGModuleCatEvaluation_apply' (f : FGModuleCatDual K V) (x : V) : DFunLike.
coe (F
参数：f : FGModuleCatDual K V；x : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contractLeft_apply`：contractLeft_apply (f : Module.Dual R M) (m : M) : c
ontractLeft R M (f otimesₜ m) = f m

--- 原说明 ---
`@[simp]`-normal form of `FGModuleCatEvaluation_apply`, where the carriers have 
been unfolded.
-/
theorem FGModuleCatEvaluation_apply' (f : FGModuleCatDual K V) (x : V) :
    DFunLike.coe
      (F := ((ModuleCat.of K (Module.Dual K V) ⊗ V.obj).carrier →ₗ[K] (𝟙_ (ModuleCat K))))
      (FGModuleCatEvaluation K V).hom.hom (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

set_option backward.privateInPublic true in
/-
**FGModuleCat.coevaluation_evaluation** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coevaluation_evaluation :
    letI V' : FGModuleCat K := FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (λ_ V').inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation K V

set_option backward.privateInPublic true in
/-
**FGModuleCat.evaluation_coevaluation** 是 Mathlib 中的一个定理，位于命名空间 `FGModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem evaluation_coevaluation :
    FGModuleCatCoevaluation K V ▷ V ≫
        (α_ V (FGModuleCatDual K V) V).hom ≫ V ◁ FGModuleCatEvaluation K V =
      (λ_ V).hom ≫ (ρ_ V).inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation' K V

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**FGModuleCat.exactPairing** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
形式化陈述：exactPairing : ExactPairing V (FGModuleCatDual K V) where coevaluation'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Category.FGModuleCat.Basic.0.FGModuleCat.coeval
uation_evaluation`：∀ (K : Type u) [inst : Field K] (V : FGModuleCat K),   Catego
ryTheory.CategoryStruct.comp       (CategoryTheory.MonoidalCategoryStruct.whisk…
· 使用定理 `_private.Mathlib.Algebra.Category.FGModuleCat.Basic.0.FGModuleCat.evalua
tion_coevaluation`：∀ (K : Type u) [inst : Field K] (V : FGModuleCat K),   Catego
ryTheory.CategoryStruct.comp       (CategoryTheory.MonoidalCategoryStruct.whisk…
-/
instance exactPairing : ExactPairing V (FGModuleCatDual K V) where
  coevaluation' := FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V
/-
**FGModuleCat.rightDual** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleCat`。
形式化陈述：rightDual : HasRightDual V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩
/-
**FGModuleCat.rightRigidCategory** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleCat`。
形式化陈述：(K : Type u) → [inst : Field K] → CategoryTheory.RightRigidCategory (FGMod
uleCat K)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where

end Field

end FGModuleCat

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp]
/-
**LinearMap.comp_id_fgModuleCat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.comp_id_fgModuleCat {R} [Ring R] {G : FGModuleCat.{v} R} {H : Ty
pe v} [AddCommGroup H] [Module R H] (f : G ->ₗ[R] H) : f.comp (ModuleCat.Hom.hom
 (InducedCategory.Hom.hom (𝟙 G))) = f
参数：f : G ->ₗ[R] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.hom_ext_iff`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R
} {f g : M ⟶ N}, f = g ↔ ModuleCat.Hom.hom f = ModuleCat.Hom.hom g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/
theorem LinearMap.comp_id_fgModuleCat
    {R} [Ring R] {G : FGModuleCat.{v} R} {H : Type v} [AddCommGroup H] [Module R H]
    (f : G →ₗ[R] H) : f.comp (ModuleCat.Hom.hom (InducedCategory.Hom.hom (𝟙 G))) = f :=
  ModuleCat.hom_ext_iff.mp <| Category.id_comp (ModuleCat.ofHom f)

@[simp]
/-
**LinearMap.id_fgModuleCat_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.id_fgModuleCat_comp {R} [Ring R] {G : Type v} [AddCommGroup G] [
Module R G] {H : FGModuleCat.{v} R} (f : G ->ₗ[R] H) : LinearMap.comp (ModuleCat
.Hom.hom (InducedCategory.Hom.hom (𝟙 H))) f = f
参数：f : G ->ₗ[R] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.hom_ext_iff`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R
} {f g : M ⟶ N}, f = g ↔ ModuleCat.Hom.hom f = ModuleCat.Hom.hom g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem LinearMap.id_fgModuleCat_comp
    {R} [Ring R] {G : Type v} [AddCommGroup G] [Module R G] {H : FGModuleCat.{v} R}
    (f : G →ₗ[R] H) : LinearMap.comp (ModuleCat.Hom.hom (InducedCategory.Hom.hom (𝟙 H))) f = f :=
  ModuleCat.hom_ext_iff.mp <| Category.comp_id (ModuleCat.ofHom f)
