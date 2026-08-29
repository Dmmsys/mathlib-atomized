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

/--
Definition of `ModuleCat.isFG` / `ModuleCat.isFG` 的定义

English:
definition ModuleCat.isFG
  signature: : ObjectProperty (ModuleCat.{v} R)
  body: fun V => Module.Finite R V

中文:
定义 模范畴.isFG
  签名: : ObjectProperty (模范畴.{v} R)
  定义体: fun V => Module.Finite R V

Depends on / 依赖: Finite, Module, Module.Finite
-/
def ModuleCat.isFG : ObjectProperty (ModuleCat.{v} R) :=
  fun V => Module.Finite R V

variable {R} in
/--
lemma `ModuleCat.isFG_iff` / 引理 `ModuleCat.isFG_iff`

English:
lemma ModuleCat.isFG_iff
  given: (V : ModuleCat.{v} R)
  proof: Iff.rfl

中文:
引理 模范畴.isFG_iff
  条件: (V : 模范畴.{v} R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ModuleCat.isFG_iff (V : ModuleCat.{v} R) :
    isFG R V ↔ Module.Finite R V := Iff.rfl

/--
Definition of `FGModuleCat` / `FGModuleCat` 的定义

English:
abbreviation FGModuleCat
  body: (ModuleCat.isFG.{v} R).FullSubcategory

中文:
缩写 FGModuleCat
  定义体: (ModuleCat.isFG.{v} R).FullSubcategory

Depends on / 依赖: FullSubcategory, ModuleCat, ModuleCat.isFG
-/
abbrev FGModuleCat := (ModuleCat.isFG.{v} R).FullSubcategory

variable {R}

/-- A synonym for `M.obj.carrier`, which we can mark with `@[coe]`. -/
@[reducible]
/--
Definition of `FGModuleCat.carrier` / `FGModuleCat.carrier` 的定义

English:
definition FGModuleCat.carrier
  signature: (M : FGModuleCat.{v} R)
  body: M.obj.carrier

中文:
定义 FGModuleCat.carrier
  签名: (M : FGModuleCat.{v} R)
  定义体: M.obj.carrier

Depends on / 依赖: M.obj.carrier, carrier
-/
def FGModuleCat.carrier (M : FGModuleCat.{v} R) : Type v := M.obj.carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (FGModuleCat.{v} R) (Type v)
  body: ⟨FGModuleCat.carrier⟩

中文:
实例 :
  签名: CoeSort (FGModuleCat.{v} R) (类型v)
  定义体: ⟨FGModuleCat.carrier⟩

Depends on / 依赖: FGModuleCat, FGModuleCat.carrier, carrier
-/
instance : CoeSort (FGModuleCat.{v} R) (Type v) :=
  ⟨FGModuleCat.carrier⟩

attribute [coe] FGModuleCat.carrier

/--
lemma `FGModuleCat.obj_carrier` / 引理 `FGModuleCat.obj_carrier`

English:
lemma FGModuleCat.obj_carrier
  given: (M : FGModuleCat.{v} R)
  statement: M.obj.carrier = M.carrier
  proof: rfl

中文:
引理 FGModuleCat.obj_carrier
  条件: (M : FGModuleCat.{v} R)
  结论: M.obj.carrier = M.carrier
  证明: rfl
-/
@[simp] lemma FGModuleCat.obj_carrier (M : FGModuleCat.{v} R) : M.obj.carrier = M.carrier := rfl

instance (M : FGModuleCat.{v} R) : Module.Finite R M :=
  M.property

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

/--
lemma `hom_hom_comp` / 引理 `hom_hom_comp`

English:
lemma hom_hom_comp
  given: {A B C : FGModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C)
  proof: rfl

中文:
引理 hom_hom_comp
  条件: {A B C : FGModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C)
  证明: rfl
-/
@[simp] lemma hom_hom_comp {A B C : FGModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl

/--
lemma `hom_hom_id` / 引理 `hom_hom_id`

English:
lemma hom_hom_id
  given: (A : FGModuleCat.{v} R)
  statement: (𝟙 A : A ⟶ A).hom.hom = LinearMap.id
  proof: rfl

中文:
引理 hom_hom_id
  条件: (A : FGModuleCat.{v} R)
  结论: (𝟙 A : A ⟶ A).hom.hom = 线性映射.id
  证明: rfl
-/
@[simp] lemma hom_hom_id (A : FGModuleCat.{v} R) : (𝟙 A : A ⟶ A).hom.hom = LinearMap.id := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FGModuleCat.{v} R)
  body: ⟨⟨ModuleCat.of R PUnit, by unfold ModuleCat.isFG; infer_instance⟩⟩

中文:
实例 :
  签名: 可居 (FGModuleCat.{v} R)
  定义体: ⟨⟨ModuleCat.of R PUnit, by unfold ModuleCat.isFG; infer_instance⟩⟩

Depends on / 依赖: ModuleCat, ModuleCat.isFG, ModuleCat.of, infer_instance
-/
instance : Inhabited (FGModuleCat.{v} R) :=
  ⟨⟨ModuleCat.of R PUnit, by unfold ModuleCat.isFG; infer_instance⟩⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
  body: ⟨ModuleCat.of R V, inferInstanceAs Module.Finite R V⟩

@[simp]

中文:
缩写 of
  签名: (V : 类型v) [加法交换群 V] [模 R V] [模.有限 R V]
  定义体: ⟨ModuleCat.of R V, inferInstanceAs Module.Finite R V⟩

@[simp]

Depends on / 依赖: Finite, Module, Module.Finite, ModuleCat, ModuleCat.of
-/
abbrev of (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
⟨ModuleCat.of R V, inferInstanceAs Module.Finite R V⟩

@[simp]
/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
  proof: rfl

中文:
引理 of_carrier
  条件: (V : 类型v) [加法交换群 V] [模 R V] [模.有限 R V]
  证明: rfl
-/
lemma of_carrier (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V] :
    of R V = V := rfl

variable {R} in
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: {V W : 类型v} [加法交换群 V] [模 R V] [模.有限 R V]
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : V ->ₗ[R] W) : of R V ⟶ of R W :=
  ConcreteCategory.ofHom f

variable {R} in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {V W : FGModuleCat.{v} R} {f g : V ⟶ W} (h : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

中文:
引理 hom_ext
  条件: {V W : FGModuleCat.{v} R} {f g : V ⟶ W} (h : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)
-/
@[ext] lemma hom_ext {V W : FGModuleCat.{v} R} {f g : V ⟶ W} (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

instance (V : FGModuleCat.{v} R) : Module.Finite R V :=
  V.property

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).Full
  body: ⟨ofHom f.hom, rfl⟩

中文:
实例 :
  签名: (forget₂ (FGModuleCat.{v} R) (模范畴.{v} R)).满
  定义体: ⟨ofHom f.hom, rfl⟩

Depends on / 依赖: f.hom
-/
instance : (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

variable {R} in
/--
Definition of `isoToLinearEquiv` / `isoToLinearEquiv` 的定义

English:
definition isoToLinearEquiv
  signature: {V W : FGModuleCat.{v} R} (i : V ≅ W)
  body: ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

中文:
定义 isoToLinearEquiv
  签名: {V W : FGModuleCat.{v} R} (i : V ≅ W)
  定义体: ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

Depends on / 依赖: FGModuleCat, ModuleCat, mapIso, toLinearEquiv
-/
def isoToLinearEquiv {V W : FGModuleCat.{v} R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

variable {R} in
/-- Converts a `LinearEquiv` to an isomorphism in the category `FGModuleCat R`. -/
@[simps]
/--
Definition of `_root_.LinearEquiv.toFGModuleCatIso` / `_root_.LinearEquiv.toFGModuleCatIso` 的定义

English:
definition _root_.LinearEquiv.toFGModuleCatIso
  body: ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

中文:
定义 _root_.线性等价.toFGModuleCatIso
  定义体: ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, e.toLinearMap, toLinearMap
-/
def _root_.LinearEquiv.toFGModuleCatIso
    {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: : FGModuleCat.{v} R ⥤ FGModuleCat.{max v w} R where
  body: .of R ULift M
map f := ofHom ULift.moduleEquiv.symm.toLinearMap ∘ₗ f.hom.hom ∘ₗ ULift.moduleEquiv.toLinearMap

中文:
定义 ulift
  签名: : FGModuleCat.{v} R ⥤ FGModuleCat.{最大值 v w} R where
  定义体: .of R ULift M
map f := ofHom ULift.moduleEquiv.symm.toLinearMap ∘ₗ f.hom.hom ∘ₗ ULift.moduleEquiv.toLinearMap
-/
def ulift : FGModuleCat.{v} R ⥤ FGModuleCat.{max v w} R where
obj M := .of R ULift M
map f := ofHom ULift.moduleEquiv.symm.toLinearMap ∘ₗ f.hom.hom ∘ₗ ULift.moduleEquiv.toLinearMap

/--
Definition of `fullyFaithfulULift` / `fullyFaithfulULift` 的定义

English:
definition fullyFaithfulULift
  signature: : (ulift R).FullyFaithful where
  body: ofHom ULift.moduleEquiv.toLinearMap ∘ₗ f.hom.hom ∘ₗ
    ULift.moduleEquiv.symm.toLinearMap

中文:
定义 fullyFaithfulULift
  签名: : (ulift R).满忠实 where
  定义体: ofHom ULift.moduleEquiv.toLinearMap ∘ₗ f.hom.hom ∘ₗ
    ULift.moduleEquiv.symm.toLinearMap

Depends on / 依赖: ULift.moduleEquiv.toLinearMap, f.hom.hom, moduleEquiv, toLinearMap
-/
def fullyFaithfulULift : (ulift R).FullyFaithful where
preimage f := ofHom ULift.moduleEquiv.toLinearMap ∘ₗ f.hom.hom ∘ₗ
    ULift.moduleEquiv.symm.toLinearMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ulift R).Faithful
  body: (fullyFaithfulULift R).faithful

中文:
实例 :
  签名: (ulift R).忠实
  定义体: (fullyFaithfulULift R).faithful

Depends on / 依赖: faithful, fullyFaithfulULift
-/
instance : (ulift R).Faithful :=
  (fullyFaithfulULift R).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ulift R).Full
  body: (fullyFaithfulULift R).full

中文:
实例 :
  签名: (ulift R).满
  定义体: (fullyFaithfulULift R).full

Depends on / 依赖: fullyFaithfulULift
-/
instance : (ulift R).Full :=
  (fullyFaithfulULift R).full

end Ring

section CommRing

variable (R : Type u) [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ModuleCat.isFG R).IsMonoidal
  body: Module.Finite.self R
  prop_tensor X Y (_ : Module.Finite _ _) (_ : Module.Finite _ _) :=
    Module.Finite.tensorProduct R X Y

中文:
实例 :
  签名: (模范畴.isFG R).是幺半群
  定义体: Module.Finite.self R
  prop_tensor X Y (_ : Module.Finite _ _) (_ : Module.Finite _ _) :=
    Module.Finite.tensorProduct R X Y

Depends on / 依赖: Finite, Module, Module.Finite.self
-/
instance : (ModuleCat.isFG R).IsMonoidal where
  prop_unit := Module.Finite.self R
  prop_tensor X Y (_ : Module.Finite _ _) (_ : Module.Finite _ _) :=
    Module.Finite.tensorProduct R X Y

open MonoidalCategory

/--
lemma `tensorUnit_obj` / 引理 `tensorUnit_obj`

English:
lemma tensorUnit_obj
  statement: (𝟙_ (FGModuleCat R)).obj = 𝟙_ (ModuleCat R)
  proof: rfl

中文:
引理 tensorUnit_obj
  结论: (𝟙_ (FGModuleCat R)).obj = 𝟙_ (模范畴 R)
  证明: rfl
-/
@[simp] lemma tensorUnit_obj : (𝟙_ (FGModuleCat R)).obj = 𝟙_ (ModuleCat R) := rfl
/--
lemma `tensorObj_obj` / 引理 `tensorObj_obj`

English:
lemma tensorObj_obj
  given: (M N : FGModuleCat.{u} R)
  statement: (M otimes N).obj = (M.obj otimes N.obj)
  proof: rfl

中文:
引理 tensorObj_obj
  条件: (M N : FGModuleCat.{u} R)
  结论: (M otimes N).obj = (M.obj otimes N.obj)
  证明: rfl
-/
@[simp] lemma tensorObj_obj (M N : FGModuleCat.{u} R) : (M otimes N).obj = (M.obj otimes N.obj) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive

中文:
实例 :
  签名: (forget₂ (FGModuleCat.{u} R) (模范畴.{u} R)).加性
-/
instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Linear R

中文:
实例 :
  签名: (forget₂ (FGModuleCat.{u} R) (模范畴.{u} R)).线性 R
-/
instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Linear R where

/--
theorem `Iso.conj_eq_conj` / 定理 `Iso.conj_eq_conj`

English:
theorem Iso.conj_eq_conj
  given: {V W : FGModuleCat R} (i : V ≅ W) (f : End V)
  proof: rfl

中文:
定理 同构.conj_eq_conj
  条件: {V W : FGModuleCat R} (i : V ≅ W) (f : End V)
  证明: rfl
-/
theorem Iso.conj_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = FGModuleCat.ofHom (LinearEquiv.conj (isoToLinearEquiv i) f.hom.hom) :=
  rfl

/--
theorem `Iso.conj_hom_eq_conj` / 定理 `Iso.conj_hom_eq_conj`

English:
theorem Iso.conj_hom_eq_conj
  given: {V W : FGModuleCat R} (i : V ≅ W) (f : End V)
  proof: rfl

中文:
定理 同构.conj_hom_eq_conj
  条件: {V W : FGModuleCat R} (i : V ≅ W) (f : End V)
  证明: rfl
-/
theorem Iso.conj_hom_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    (Iso.conj i f).hom.hom = (LinearEquiv.conj (isoToLinearEquiv i) f.hom.hom) :=
  rfl

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FGModuleCat.{v} K) : Module.Finite K (V.obj ⟶ W.obj) :=
  ((inferInstance : Module.Finite K (V ->ₗ[K] W))).equiv ModuleCat.homLinearEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
instance (V W : FGModuleCat.{v} K) : Module.Finite K (V ⟶ W) :=
  ((inferInstance : Module.Finite K (V.obj ⟶ W.obj))).equiv
    InducedCategory.homLinearEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ModuleCat.isFG K).IsMonoidalClosed
  body: ((inferInstance : Module.Finite K (X ->ₗ[K] Y))).equiv ModuleCat.homLinearEquiv.symm

中文:
实例 :
  签名: (模范畴.isFG K).是幺半群闭
  定义体: ((inferInstance : Module.Finite K (X ->ₗ[K] Y))).equiv ModuleCat.homLinearEquiv.symm

Depends on / 依赖: Finite, Module, Module.Finite, ModuleCat, ModuleCat.homLinearEquiv.symm, homLinearEquiv
-/
instance : (ModuleCat.isFG K).IsMonoidalClosed where
  prop_ihom {X Y} (_ : Module.Finite _ _) (_ : Module.Finite _ _) :=
    ((inferInstance : Module.Finite K (X ->ₗ[K] Y))).equiv ModuleCat.homLinearEquiv.symm

variable (V W : FGModuleCat K)

@[simp]
/--
theorem `ihom_obj` / 定理 `ihom_obj`

English:
theorem ihom_obj
  statement: (ihom V).obj W = FGModuleCat.of K (V.obj ⟶ W.obj)
  proof: rfl

中文:
定理 ihom_obj
  结论: (ihom V).obj W = FGModuleCat.of K (V.obj ⟶ W.obj)
  证明: rfl
-/
theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V.obj ⟶ W.obj) :=
  rfl

/--
Definition of `FGModuleCatDual` / `FGModuleCatDual` 的定义

English:
definition FGModuleCatDual
  signature: : FGModuleCat K
  body: ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩

中文:
定义 FGModuleCatDual
  签名: : FGModuleCat K
  定义体: ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩

Depends on / 依赖: Module, Module.Dual, ModuleCat, ModuleCat.of, Subspace, Subspace.instModuleDualFiniteDimensional, instModuleDualFiniteDimensional
-/
def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩

/--
lemma `FGModuleCatDual_obj` / 引理 `FGModuleCatDual_obj`

English:
lemma FGModuleCatDual_obj
  statement: (FGModuleCatDual K V).obj = ModuleCat.of K (Module.Dual K V)
  proof: rfl

中文:
引理 FGModuleCatDual_obj
  结论: (FGModuleCatDual K V).obj = 模范畴.of K (模.对偶 K V)
  证明: rfl
-/
@[simp] lemma FGModuleCatDual_obj : (FGModuleCatDual K V).obj = ModuleCat.of K (Module.Dual K V) :=
  rfl
/--
lemma `FGModuleCatDual_coe` / 引理 `FGModuleCatDual_coe`

English:
lemma FGModuleCatDual_coe
  statement: (FGModuleCatDual K V : Type u) = Module.Dual K V
  proof: rfl

中文:
引理 FGModuleCatDual_coe
  结论: (FGModuleCatDual K V : 类型u) = 模.对偶 K V
  证明: rfl
-/
@[simp] lemma FGModuleCatDual_coe : (FGModuleCatDual K V : Type u) = Module.Dual K V := rfl

open CategoryTheory.MonoidalCategory

/--
Definition of `FGModuleCatCoevaluation` / `FGModuleCatCoevaluation` 的定义

English:
definition FGModuleCatCoevaluation
  signature: : 𝟙_ (FGModuleCat K) ⟶ V otimes FGModuleCatDual K V
  body: ConcreteCategory.ofHom coevaluation K V

中文:
定义 FGModuleCatCoevaluation
  签名: : 𝟙_ (FGModuleCat K) ⟶ V otimes FGModuleCatDual K V
  定义体: ConcreteCategory.ofHom coevaluation K V

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, coevaluation
-/
def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V otimes FGModuleCatDual K V :=
ConcreteCategory.ofHom coevaluation K V

/--
theorem `FGModuleCatCoevaluation_apply_one` / 定理 `FGModuleCatCoevaluation_apply_one`

English:
theorem FGModuleCatCoevaluation_apply_one
  proof: coevaluation_apply_one K V

中文:
定理 FGModuleCatCoevaluation_apply_one
  证明: coevaluation_apply_one K V

Depends on / 依赖: coevaluation_apply_one
-/
theorem FGModuleCatCoevaluation_apply_one :
    (FGModuleCatCoevaluation K V).hom (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V,
        (Basis.ofVectorSpace K V) i otimesₜ[K] (Basis.ofVectorSpace K V).coord i :=
  coevaluation_apply_one K V

/--
Definition of `FGModuleCatEvaluation` / `FGModuleCatEvaluation` 的定义

English:
definition FGModuleCatEvaluation
  signature: : FGModuleCatDual K V otimes V ⟶ 𝟙_ (FGModuleCat K)
  body: ConcreteCategory.ofHom contractLeft K V

中文:
定义 FGModuleCatEvaluation
  签名: : FGModuleCatDual K V otimes V ⟶ 𝟙_ (FGModuleCat K)
  定义体: ConcreteCategory.ofHom contractLeft K V

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, contractLeft
-/
def FGModuleCatEvaluation : FGModuleCatDual K V otimes V ⟶ 𝟙_ (FGModuleCat K) :=
ConcreteCategory.ofHom contractLeft K V

/--
theorem `FGModuleCatEvaluation_apply` / 定理 `FGModuleCatEvaluation_apply`

English:
theorem FGModuleCatEvaluation_apply
  given: (f : FGModuleCatDual K V) (x : V)
  proof: contractLeft_apply f x

中文:
定理 FGModuleCatEvaluation_apply
  条件: (f : FGModuleCatDual K V) (x : V)
  证明: contractLeft_apply f x

Depends on / 依赖: contractLeft_apply
-/
theorem FGModuleCatEvaluation_apply (f : FGModuleCatDual K V) (x : V) :
    (FGModuleCatEvaluation K V).hom (f otimesₜ x) = f.toFun x :=
  contractLeft_apply f x

set_option backward.isDefEq.respectTransparency false in
/-- `@[simp]`-normal form of `FGModuleCatEvaluation_apply`, where the carriers have been unfolded.
-/
@[simp]
/--
theorem `FGModuleCatEvaluation_apply'` / 定理 `FGModuleCatEvaluation_apply'`

English:
theorem FGModuleCatEvaluation_apply'
  given: (f : FGModuleCatDual K V) (x : V)
  proof: contractLeft_apply f x

中文:
定理 FGModuleCatEvaluation_apply'
  条件: (f : FGModuleCatDual K V) (x : V)
  证明: contractLeft_apply f x

Depends on / 依赖: Module, Module.Dual, ModuleCat, ModuleCat.of, V.obj, carrier, otimes
-/
theorem FGModuleCatEvaluation_apply' (f : FGModuleCatDual K V) (x : V) :
    DFunLike.coe
      (F := ((ModuleCat.of K (Module.Dual K V) otimes V.obj).carrier ->ₗ[K] (𝟙_ (ModuleCat K))))
      (FGModuleCatEvaluation K V).hom.hom (f otimesₜ x) = f.toFun x :=
  contractLeft_apply f x

set_option backward.privateInPublic true in
/--
theorem `coevaluation_evaluation` / 定理 `coevaluation_evaluation`

English:
theorem coevaluation_evaluation
  proof: FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (fun_ V').inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation K V

中文:
定理 coevaluation_evaluation
  证明: FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (fun_ V').inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation K V
-/
private theorem coevaluation_evaluation :
    letI V' : FGModuleCat K := FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (fun_ V').inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation K V

set_option backward.privateInPublic true in
/--
theorem `evaluation_coevaluation` / 定理 `evaluation_coevaluation`

English:
theorem evaluation_coevaluation
  proof: by
  ext : 1
  apply contractLeft_assoc_coevaluation' K V

中文:
定理 evaluation_coevaluation
  证明: by
  ext : 1
  apply contractLeft_assoc_coevaluation' K V
-/
private theorem evaluation_coevaluation :
    FGModuleCatCoevaluation K V ▷ V ≫
        (α_ V (FGModuleCatDual K V) V).hom ≫ V ◁ FGModuleCatEvaluation K V =
      (fun_ V).hom ≫ (ρ_ V).inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation' K V

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `exactPairing` / 实例 `exactPairing`

English:
instance exactPairing
  signature: : ExactPairing V (FGModuleCatDual K V) where
  body: FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

中文:
实例 exactPairing
  签名: : ExactPairing V (FGModuleCatDual K V) where
  定义体: FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

Depends on / 依赖: FGModuleCatCoevaluation
-/
instance exactPairing : ExactPairing V (FGModuleCatDual K V) where
  coevaluation' := FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

/--
Instance `rightDual` / 实例 `rightDual`

English:
instance rightDual
  signature: : HasRightDual V
  body: ⟨FGModuleCatDual K V⟩

中文:
实例 rightDual
  签名: : 有RightDual V
  定义体: ⟨FGModuleCatDual K V⟩

Depends on / 依赖: FGModuleCatDual
-/
instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩

/--
Instance `rightRigidCategory` / 实例 `rightRigidCategory`

English:
instance rightRigidCategory
  signature: : RightRigidCategory (FGModuleCat K) where

中文:
实例 rightRigidCategory
  签名: : RightRigid范畴 (FGModuleCat K) where
-/
instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where

end Field

end FGModuleCat

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp]
/--
theorem `LinearMap.comp_id_fgModuleCat` / 定理 `LinearMap.comp_id_fgModuleCat`

English:
theorem LinearMap.comp_id_fgModuleCat
  proof: ModuleCat.hom_ext_iff.mp Category.id_comp (ModuleCat.ofHom f)

@[simp]

中文:
定理 线性映射.comp_id_fgModuleCat
  证明: ModuleCat.hom_ext_iff.mp Category.id_comp (ModuleCat.ofHom f)

@[simp]

Depends on / 依赖: Category, Category.id_comp, ModuleCat, ModuleCat.hom_ext_iff.mp, ModuleCat.ofHom, hom_ext_iff, id_comp
-/
theorem LinearMap.comp_id_fgModuleCat
    {R} [Ring R] {G : FGModuleCat.{v} R} {H : Type v} [AddCommGroup H] [Module R H]
    (f : G ->ₗ[R] H) : f.comp (ModuleCat.Hom.hom (InducedCategory.Hom.hom (𝟙 G))) = f :=
ModuleCat.hom_ext_iff.mp Category.id_comp (ModuleCat.ofHom f)

@[simp]
/--
theorem `LinearMap.id_fgModuleCat_comp` / 定理 `LinearMap.id_fgModuleCat_comp`

English:
theorem LinearMap.id_fgModuleCat_comp
  proof: ModuleCat.hom_ext_iff.mp Category.comp_id (ModuleCat.ofHom f)

中文:
定理 线性映射.id_fgModuleCat_comp
  证明: ModuleCat.hom_ext_iff.mp Category.comp_id (ModuleCat.ofHom f)

Depends on / 依赖: Category, Category.comp_id, ModuleCat, ModuleCat.hom_ext_iff.mp, ModuleCat.ofHom, comp_id, hom_ext_iff
-/
theorem LinearMap.id_fgModuleCat_comp
    {R} [Ring R] {G : Type v} [AddCommGroup G] [Module R G] {H : FGModuleCat.{v} R}
    (f : G ->ₗ[R] H) : LinearMap.comp (ModuleCat.Hom.hom (InducedCategory.Hom.hom (𝟙 H))) f = f :=
ModuleCat.hom_ext_iff.mp Category.comp_id (ModuleCat.ofHom f)
