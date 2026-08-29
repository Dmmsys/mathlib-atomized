/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!

## Main Purpose
This file is the preliminary for the `linearize` functor from `Action (Type w) G` to `Rep k G`,
constructing the functor from the `Representation` would reduce the amount of DefEq abuses that we
currently are doing in the `Rep` file.

TODO (Edison) : Refactor `Rep` to be a concrete category of `Representation` and
reconstruct the current `linearize` functor using this file.

-/

universe w w' u u' v v'
@[expose] public section
namespace Representation

open Representation.IntertwiningMap Representation.TensorProduct
open scoped MonoidAlgebra

noncomputable section

variable {k : Type u} {G : Type v} {V : Type u'} {W : Type v'} [Monoid G] [Semiring k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {σ : Representation k G V} {ρ : Representation k G W} {X Y Z : Action (Type w) G}

open CategoryTheory

variable (k G X) in
/-- Every Set `X` that has a `G`-action on it can be made into a `G`-rep by using `X →₀ k` as
  the base module and `G`-action on it is induced by the `G`-action on `X`. -/
@[simps]
/--
Definition of `linearize` / `linearize` 的定义

English:
definition linearize
  signature: : Representation k G k[X.V] where
  body: MonoidAlgebra.mapDomainLinearMap k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

中文:
定义 linearize
  签名: : Representation k G k[X.V] where
  定义体: MonoidAlgebra.mapDomainLinearMap k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.mapDomainLinearMap, mapDomainLinearMap
-/
def linearize : Representation k G k[X.V] where
  toFun g := MonoidAlgebra.mapDomainLinearMap k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/--
lemma `linearize_single` / 引理 `linearize_single`

English:
lemma linearize_single
  given: (g : G) (x : X.V)
  proof: by
  simp

中文:
引理 linearize_single
  条件: (g : G) (x : X.V)
  证明: by
  simp
-/
lemma linearize_single (g : G) (x : X.V) :
    linearize k G X g (.single x 1) = .single (X.ρ g x) 1 := by
  simp

/-- Every morphism between `G`-sets could be made into an intertwining map between
  `Representation`s by the linear map induced on the indexing sets. -/
@[simps toLinearMap]
/--
Definition of `linearizeMap` / `linearizeMap` 的定义

English:
definition linearizeMap
  signature: (f : X ⟶ Y)
  body: MonoidAlgebra.mapDomainLinearMap k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]

中文:
定义 linearizeMap
  签名: (f : X ⟶ Y)
  定义体: MonoidAlgebra.mapDomainLinearMap k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]

Depends on / 依赖: linearize
-/
def linearizeMap (f : X ⟶ Y) : IntertwiningMap (A := k) (linearize k G X) (linearize k G Y) where
  toLinearMap := MonoidAlgebra.mapDomainLinearMap k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]
/--
lemma `linearizeMap_single` / 引理 `linearizeMap_single`

English:
lemma linearizeMap_single
  given: (f : X ⟶ Y) (x : X.V) (r : k)
  proof: by
  simp [linearizeMap]

中文:
引理 linearizeMap_single
  条件: (f : X ⟶ Y) (x : X.V) (r : k)
  证明: by
  simp [linearizeMap]

Depends on / 依赖: linearizeMap
-/
lemma linearizeMap_single (f : X ⟶ Y) (x : X.V) (r : k) :
    (linearizeMap f) (.single x r) = .single (f.hom x) r := by
  simp [linearizeMap]

namespace LinearizeMonoidal

open scoped MonoidalCategory

attribute [local simp] types_tensorObj_def types_tensorUnit_def

-- These two unification hints are to help lean understand the underlying types of these actions
-- which it fails without them because `types` abuses defeq.
unif_hint (X Y : Action (Type w) G) where ⊢ (X otimes Y).V ≟ X.V × Y.V
unif_hint where ⊢ (𝟙_ (Action (Type w) G)).V ≟ PUnit

/--
lemma `_root_.Action.tensor_ρ_apply` / 引理 `_root_.Action.tensor_ρ_apply`

English:
lemma _root_.Action.tensor_ρ_apply
  given: (g : G) (xy : (X otimes Y).V)
  proof: rfl

中文:
引理 _root_.作用.tensor_ρ_apply
  条件: (g : G) (xy : (X otimes Y).V)
  证明: rfl
-/
lemma _root_.Action.tensor_ρ_apply (g : G) (xy : (X otimes Y).V) :
    (X otimes Y).ρ g xy = (X.ρ g xy.1, Y.ρ g xy.2) := rfl

variable (k G) in
-- I could use `Action.trivial G (PUnit)` but that's not reducibly equal to the tensor unit
/-- The counit of the linearize functor. -/
@[simps toLinearMap]
/--
Definition of `ε` / `ε` 的定义

English:
definition ε
  signature: : (trivial k G k).IntertwiningMap (linearize k G (MonoidalCategoryStruct.tensorUnit
  body: MonoidAlgebra.uniqueLinearEquiv k PUnit
  isIntertwining' g := by ext1; simp [linearize_single _]

中文:
定义 ε
  签名: : (trivial k G k).整数ertwining映射 (linearize k G (幺半群范畴结构.tensorUnit
  定义体: MonoidAlgebra.uniqueLinearEquiv k PUnit
  isIntertwining' g := by ext1; simp [linearize_single _]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.uniqueLinearEquiv, uniqueLinearEquiv
-/
def ε : (trivial k G k).IntertwiningMap (linearize k G (MonoidalCategoryStruct.tensorUnit
    (Action (Type w) G))) where
.symm.toLinearMap __ := MonoidAlgebra.uniqueLinearEquiv k PUnit
  isIntertwining' g := by ext1; simp [linearize_single _]

/--
lemma `ε_one` / 引理 `ε_one`

English:
lemma ε_one
  statement: ε k G 1 = .single PUnit.unit 1
  proof: by
  simp [← toLinearMap_apply, types_tensorUnit_def]

中文:
引理 ε_one
  结论: ε k G 1 = .single 命题单元.unit 1
  证明: by
  simp [← toLinearMap_apply, types_tensorUnit_def]

Depends on / 依赖: toLinearMap_apply, types_tensorUnit_def
-/
lemma ε_one : ε k G 1 = .single PUnit.unit 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

open scoped MonoidalCategory

variable (k G) in
/-- The unit of the linearize functor. -/
@[simps toLinearMap]
/--
Definition of `η` / `η` 的定义

English:
definition η
  signature: : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  body: (MonoidAlgebra.uniqueLinearEquiv k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]

中文:
定义 η
  签名: : (linearize k G (𝟙_ (作用 (类型u) G))).整数ertwining映射 (trivial k G k) where
  定义体: (MonoidAlgebra.uniqueLinearEquiv k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.uniqueLinearEquiv, toLinearMap, uniqueLinearEquiv
-/
def η : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  toLinearMap := (MonoidAlgebra.uniqueLinearEquiv k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]

/--
lemma `η_single` / 引理 `η_single`

English:
lemma η_single
  given: (x : PUnit)
  statement: η k G (.single x 1) = 1
  proof: by
  simp [← toLinearMap_apply, types_tensorUnit_def]

中文:
引理 η_single
  条件: (x : 命题单元)
  结论: η k G (.single x 1) = 1
  证明: by
  simp [← toLinearMap_apply, types_tensorUnit_def]

Depends on / 依赖: toLinearMap_apply, types_tensorUnit_def
-/
lemma η_single (x : PUnit) : η k G (.single x 1) = 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

variable (k G) in
/--
lemma `ε_η` / 引理 `ε_η`

English:
lemma ε_η
  statement: (ε k G).comp (η k G) = .id _
  proof: by ext; simp

中文:
引理 ε_η
  结论: (ε k G).comp (η k G) = .id _
  证明: by ext; simp
-/
lemma ε_η : (ε k G).comp (η k G) = .id _ := by ext; simp

variable (k G) in
/--
lemma `η_ε` / 引理 `η_ε`

English:
lemma η_ε
  statement: (η k G).comp (ε k G) = .id _
  proof: by ext; simp

中文:
引理 η_ε
  结论: (η k G).comp (ε k G) = .id _
  证明: by ext; simp
-/
lemma η_ε : (η k G).comp (ε k G) = .id _ := by ext; simp

section comm

open scoped MonoidalCategory

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] {σ : Representation k G V}
  {ρ : Representation k G W}

variable (X Y) in
/-- The tensor (multiplication) of the linearize functor. -/
@[simps toLinearMap]
/--
Definition of `μ` / `μ` 的定义

English:
definition μ
  signature: : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap (linearize k G (X otimes Y)) where
  body: (MonoidAlgebra.tensorEquiv k).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]; rfl

中文:
定义 μ
  签名: : ((linearize k G X).tprod (linearize k G Y)).整数ertwining映射 (linearize k G (X otimes Y)) where
  定义体: (MonoidAlgebra.tensorEquiv k).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]; rfl

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.tensorEquiv, tensorEquiv, toLinearMap
-/
def μ : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap (linearize k G (X otimes Y)) where
  toLinearMap := (MonoidAlgebra.tensorEquiv k).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]; rfl

/--
lemma `μ_apply_single_single` / 引理 `μ_apply_single_single`

English:
lemma μ_apply_single_single
  given: (x : X.V) (y : Y.V) (r s : k)
  proof: by
  ext; simp [← toLinearMap_apply]

中文:
引理 μ_apply_single_single
  条件: (x : X.V) (y : Y.V) (r s : k)
  证明: by
  ext; simp [← toLinearMap_apply]

Depends on / 依赖: single, toLinearMap_apply
-/
lemma μ_apply_single_single (x : X.V) (y : Y.V) (r s : k) :
    μ (k := k) X Y (.single x r otimesₜ .single y s) = .single (x, y) (r * s) := by
  ext; simp [← toLinearMap_apply]

/--
lemma `coeff_μ_tmul` / 引理 `coeff_μ_tmul`

English:
lemma coeff_μ_tmul
  given: (l1 : k[X.V]) (l2 : k[Y.V]) (xy : (X otimes Y).V)
  proof: by
  simp [← toLinearMap_apply, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]

中文:
引理 coeff_μ_tmul
  条件: (l1 : k[X.V]) (l2 : k[Y.V]) (xy : (X otimes Y).V)
  证明: by
  simp [← toLinearMap_apply, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]

Depends on / 依赖: _apply_apply, finsuppTensorFinsupp, toLinearMap_apply, types_tensorObj_def
-/
lemma coeff_μ_tmul (l1 : k[X.V]) (l2 : k[Y.V]) (xy : (X otimes Y).V) :
    (μ X Y (l1 otimesₜ l2)).coeff xy = l1.coeff xy.1 * l2.coeff xy.2 := by
  simp [← toLinearMap_apply, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]

/--
lemma `μ_comp_rTensor` / 引理 `μ_comp_rTensor`

English:
lemma μ_comp_rTensor
  given: (f : X ⟶ Y) (Z : Action (Type w) G)
  proof: by
  ext; simp

中文:
引理 μ_comp_rTensor
  条件: (f : X ⟶ Y) (Z : 作用 (类型 w) G)
  证明: by
  ext; simp
-/
lemma μ_comp_rTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Y Z).comp (rTensor (linearize k G Z) (linearizeMap f)) =
      (linearizeMap (f ▷ Z)).comp (μ X Z) := by
  ext; simp

/--
lemma `μ_comp_lTensor` / 引理 `μ_comp_lTensor`

English:
lemma μ_comp_lTensor
  given: (f : X ⟶ Y) (Z : Action (Type w) G)
  proof: by
  ext; simp

中文:
引理 μ_comp_lTensor
  条件: (f : X ⟶ Y) (Z : 作用 (类型 w) G)
  证明: by
  ext; simp
-/
lemma μ_comp_lTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Z Y).comp ((linearizeMap f).lTensor (linearize k G Z)) =
      (linearizeMap (Z ◁ f)).comp (μ Z X) := by
  ext; simp

variable (X Y Z) in
/--
lemma `μ_comp_assoc` / 引理 `μ_comp_assoc`

English:
lemma μ_comp_assoc
  statement: ((linearizeMap (α_ X Y Z).hom).comp
  proof: by
  ext x y z : 9
  -- experiment with monoidal structure of `Action` on `Type`
  simp only [Action.tensorObj_V, types_tensorObj_def, comp_toLinearMap, μ_toLinearMap,
    toLinearMap_rTensor, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restr

中文:
引理 μ_comp_assoc
  结论: ((linearizeMap (α_ X Y Z).hom).comp
  证明: by
  ext x y z : 9
  -- experiment with monoidal structure of `Action` on `Type`
  simp only [Action.tensorObj_V, types_tensorObj_def, comp_toLinearMap, μ_toLinearMap,
    toLinearMap_rTensor, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restr
-/
lemma μ_comp_assoc : ((linearizeMap (α_ X Y Z).hom).comp
    (μ (X otimes Y) Z)).comp ((μ X Y).rTensor (linearize k G Z)) = ((μ X (Y otimes Z)).comp
    ((μ Y Z).lTensor (linearize k G X))).comp (assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap := by
  ext x y z : 9
  -- experiment with monoidal structure of `Action` on `Type`
  simp only [Action.tensorObj_V, types_tensorObj_def, comp_toLinearMap, μ_toLinearMap,
    toLinearMap_rTensor, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul, toLinearMap_apply,
    toLinearMap_lTensor, toLinearMap_assoc, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul]
  -- after fixing the defeq problems in `Action` and in the monoidal category structure of `types`
  -- this line should close the goal so this is left as an indicator.
  convert dsimp% linearizeMap_single (α_ X Y Z).hom ((x, y), z) (1 : k)
  all_goals with_reducible simp

variable (X) in
/--
lemma `μ_leftUnitor` / 引理 `μ_leftUnitor`

English:
lemma μ_leftUnitor
  statement: (lid k (linearize k G X)).toIntertwiningMap =
  proof: by
  ext; simp

中文:
引理 μ_leftUnitor
  结论: (lid k (linearize k G X)).to整数ertwiningMap =
  证明: by
  ext; simp
-/
lemma μ_leftUnitor : (lid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (fun_ X).hom).comp (μ (𝟙_ (Action (Type w) G)) X)).comp (rTensor
    (linearize k G X) (ε k G)) := by
  ext; simp

variable (X) in
/--
lemma `μ_rightUnitor` / 引理 `μ_rightUnitor`

English:
lemma μ_rightUnitor
  statement: (rid k (linearize k G X)).toIntertwiningMap =
  proof: by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom]

中文:
引理 μ_rightUnitor
  结论: (rid k (linearize k G X)).to整数ertwiningMap =
  证明: by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom]

Depends on / 依赖: Action, Action.rightUnitor_hom_hom, Action.tensorObj_V, linearizeMap, rightUnitor_hom_hom, tensorObj_V, types_tensorObj_def, types_tensorUnit_def
-/
lemma μ_rightUnitor : (rid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (ρ_ X).hom).comp (μ X (𝟙_ (Action (Type w) G)))).comp ((ε k G).lTensor
    (linearize k G X)) := by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom]

variable (X Y) in
/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: : (linearize k G (X otimes Y)).IntertwiningMap
  body: (MonoidAlgebra.tensorEquiv k).symm.toLinearMap
  isIntertwining' g := by
    ext; simp [linearize_single _, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]; rfl

中文:
定义 δ
  签名: : (linearize k G (X otimes Y)).整数ertwining映射
  定义体: (MonoidAlgebra.tensorEquiv k).symm.toLinearMap
  isIntertwining' g := by
    ext; simp [linearize_single _, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]; rfl

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.tensorEquiv, symm.toLinearMap, tensorEquiv, toLinearMap
-/
def δ : (linearize k G (X otimes Y)).IntertwiningMap
    ((linearize k G X).tprod (linearize k G Y)) where
  toLinearMap := (MonoidAlgebra.tensorEquiv k).symm.toLinearMap
  isIntertwining' g := by
    ext; simp [linearize_single _, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]; rfl

/--
lemma `δ_apply_single` / 引理 `δ_apply_single`

English:
lemma δ_apply_single
  given: (xy : (X otimes Y).V)
  proof: by
  simp [δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

中文:
引理 δ_apply_single
  条件: (xy : (X otimes Y).V)
  证明: by
  simp [δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul, single, tensorEquiv_symm_single_eq_single_one_tmul
-/
lemma δ_apply_single (xy : (X otimes Y).V) :
    (δ (k := k) X Y) (.single xy 1) = .single xy.1 1 otimesₜ .single xy.2 1 := by
  simp [δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

variable (Z) in
/--
lemma `rTensor_comp_δ` / 引理 `rTensor_comp_δ`

English:
lemma rTensor_comp_δ
  given: (f : X ⟶ Y)
  proof: by
  ext; simp [δ_apply_single _]

中文:
引理 rTensor_comp_δ
  条件: (f : X ⟶ Y)
  证明: by
  ext; simp [δ_apply_single _]
-/
lemma rTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).rTensor (linearize k G Z)).comp (δ X Z) =
      (δ Y Z).comp (linearizeMap (f ▷ Z)) := by
  ext; simp [δ_apply_single _]

variable (Z) in
/--
lemma `lTensor_comp_δ` / 引理 `lTensor_comp_δ`

English:
lemma lTensor_comp_δ
  given: (f : X ⟶ Y)
  proof: by
  ext; simp [δ_apply_single _]

中文:
引理 lTensor_comp_δ
  条件: (f : X ⟶ Y)
  证明: by
  ext; simp [δ_apply_single _]
-/
lemma lTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).lTensor (linearize k G Z)).comp (δ Z X) =
      (δ Z Y).comp (linearizeMap (Z ◁ f)) := by
  ext; simp [δ_apply_single _]

variable (X Y Z) in
/--
lemma `assoc_comp_δ` / 引理 `assoc_comp_δ`

English:
lemma assoc_comp_δ
  statement: ((assoc (linearize k G X) (linearize k G Y)
  proof: by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

中文:
引理 assoc_comp_δ
  结论: ((assoc (linearize k G X) (linearize k G Y)
  证明: by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]
-/
lemma assoc_comp_δ : ((assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap.comp ((δ X Y).rTensor (linearize k G Z))).comp
    (δ (X otimes Y) Z) = (((δ Y Z).lTensor (linearize k G X)).comp (δ X (Y otimes Z))).comp
    (linearizeMap (α_ X Y Z).hom) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

/--
lemma `leftUnitor_δ` / 引理 `leftUnitor_δ`

English:
lemma leftUnitor_δ
  given: (X : Action (Type u) G)
  statement: (lid k (linearize k G X)).symm.toIntertwiningMap =
  proof: by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

unif_hint (X : Action (Type u) G) where ⊢ (X otimes 𝟙_ (Action (Type u) G)).V ≟ X.V × PUnit in

中文:
引理 leftUnitor_δ
  条件: (X : 作用 (类型u) G)
  结论: (lid k (linearize k G X)).symm.to整数ertwiningMap =
  证明: by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

unif_hint (X : Action (Type u) G) where ⊢ (X otimes 𝟙_ (Action (Type u) G)).V ≟ X.V × PUnit in
-/
lemma leftUnitor_δ (X : Action (Type u) G) : (lid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).rTensor (linearize k G X)).comp (δ (𝟙_ (Action (Type u) G)) X)).comp
      (linearizeMap (fun_ X).inv) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

unif_hint (X : Action (Type u) G) where ⊢ (X otimes 𝟙_ (Action (Type u) G)).V ≟ X.V × PUnit in
/--
lemma `rightUnitor_δ` / 引理 `rightUnitor_δ`

English:
lemma rightUnitor_δ
  given: (X : Action (Type u) G)
  statement: (rid k (linearize k G X)).symm.toIntertwiningMap =
  proof: by
  ext; simp [δ_apply_single _]

中文:
引理 rightUnitor_δ
  条件: (X : 作用 (类型u) G)
  结论: (rid k (linearize k G X)).symm.to整数ertwiningMap =
  证明: by
  ext; simp [δ_apply_single _]
-/
lemma rightUnitor_δ (X : Action (Type u) G) : (rid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).lTensor (linearize k G X)).comp (δ X (𝟙_ (Action (Type u) G)))).comp
      (linearizeMap (ρ_ X).inv) := by
  ext; simp [δ_apply_single _]

variable (X Y) in
/--
lemma `μ_δ` / 引理 `μ_δ`

English:
lemma μ_δ
  statement: (μ X Y).comp (δ (k := k) X Y) = .id _
  proof: by
  ext; simp [δ_apply_single _]

中文:
引理 μ_δ
  结论: (μ X Y).comp (δ (k := k) X Y) = .id _
  证明: by
  ext; simp [δ_apply_single _]
-/
lemma μ_δ : (μ X Y).comp (δ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

variable (X Y) in
/--
lemma `δ_μ` / 引理 `δ_μ`

English:
lemma δ_μ
  statement: (δ X Y).comp (μ (k := k) X Y) = .id _
  proof: by
  ext; simp [δ_apply_single _]

中文:
引理 δ_μ
  结论: (δ X Y).comp (μ (k := k) X Y) = .id _
  证明: by
  ext; simp [δ_apply_single _]
-/
lemma δ_μ : (δ X Y).comp (μ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

end comm

end LinearizeMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `linearizeTrivial_def` / 引理 `linearizeTrivial_def`

English:
lemma linearizeTrivial_def
  given: (X : Type w) (g : G)
  proof: by
  ext (x : X) : 2
  rw [LinearMap.comp_apply]; rw [LinearMap.id_comp]; rw [MonoidAlgebra.lsingle_apply]; rw [linearize_single]
  simp only [Action.trivial_ρ]
  rfl

中文:
引理 linearizeTrivial_def
  条件: (X : 类型 w) (g : G)
  证明: by
  ext (x : X) : 2
  rw [LinearMap.comp_apply]; rw [LinearMap.id_comp]; rw [MonoidAlgebra.lsingle_apply]; rw [linearize_single]
  simp only [Action.trivial_ρ]
  rfl

Depends on / 依赖: Action, Action.trivial_, LinearMap, LinearMap.comp_apply, LinearMap.id_comp, MonoidAlgebra, MonoidAlgebra.lsingle_apply, comp_apply, id_comp, linearize_single, lsingle_apply
-/
lemma linearizeTrivial_def (X : Type w) (g : G) :
    linearize k G (Action.trivial _ X) g = LinearMap.id := by
  ext (x : X) : 2
  rw [LinearMap.comp_apply]; rw [LinearMap.id_comp]; rw [MonoidAlgebra.lsingle_apply]; rw [linearize_single]
  simp only [Action.trivial_ρ]
  rfl

variable (k G) in
/--
Definition of `linearizeTrivialIso` / `linearizeTrivialIso` 的定义

English:
definition linearizeTrivialIso
  signature: (X : Type w)
  body: .mk (.refl ..) fun g => by erw [linearizeTrivial_def, LinearMap.comp_id]

中文:
定义 linearizeTrivialIso
  签名: (X : 类型 w)
  定义体: .mk (.refl ..) fun g => by erw [linearizeTrivial_def, LinearMap.comp_id]

Depends on / 依赖: LinearMap, LinearMap.comp_id, comp_id, linearizeTrivial_def
-/
def linearizeTrivialIso (X : Type w) : (linearize k G (.trivial _ X)).Equiv (trivial k G k[X]) :=
  .mk (.refl ..) fun g => by erw [linearizeTrivial_def, LinearMap.comp_id]

open CategoryTheory
/--
lemma `linearizeTrivialIso_apply` / 引理 `linearizeTrivialIso_apply`

English:
lemma linearizeTrivialIso_apply
  given: {X : Type w} (f : k[(Action.trivial _ X).V])
  proof: rfl

中文:
引理 linearizeTrivialIso_apply
  条件: {X : 类型 w} (f : k[(作用.trivial _ X).V])
  证明: rfl
-/
lemma linearizeTrivialIso_apply {X : Type w} (f : k[(Action.trivial _ X).V]) :
    linearizeTrivialIso k G X f = f := rfl

/--
lemma `linearizeTrivialIso_symm_apply` / 引理 `linearizeTrivialIso_symm_apply`

English:
lemma linearizeTrivialIso_symm_apply
  given: {X : Type w} (f : k[X])
  proof: rfl

中文:
引理 linearizeTrivialIso_symm_apply
  条件: {X : 类型 w} (f : k[X])
  证明: rfl
-/
lemma linearizeTrivialIso_symm_apply {X : Type w} (f : k[X]) :
    (linearizeTrivialIso k G X).symm f = f := rfl

variable (k G) in
/--
Definition of `linearizeOfMulActionIso` / `linearizeOfMulActionIso` 的定义

English:
definition linearizeOfMulActionIso
  signature: (H : Type w) [MulAction G H]
  body: .mk (.refl ..) fun _ => rfl

中文:
定义 linearizeOfMulActionIso
  签名: (H : 类型 w) [乘法作用 G H]
  定义体: .mk (.refl ..) fun _ => rfl
-/
def linearizeOfMulActionIso (H : Type w) [MulAction G H] :
    (linearize k G (Action.ofMulAction G H)).Equiv (ofMulAction k G H) :=
  .mk (.refl ..) fun _ => rfl

variable (k G) in
/--
Definition of `linearizeDiagonalEquiv` / `linearizeDiagonalEquiv` 的定义

English:
abbreviation linearizeDiagonalEquiv
  signature: (n : Nat)
  body: linearizeOfMulActionIso k G (Fin n -> G)

中文:
缩写 linearizeDiagonalEquiv
  签名: (n : 自然数)
  定义体: linearizeOfMulActionIso k G (Fin n -> G)

Depends on / 依赖: linearizeOfMulActionIso
-/
abbrev linearizeDiagonalEquiv (n : Nat) : (linearize k G (Action.diagonal G n)).Equiv
    (diagonal k G n) := linearizeOfMulActionIso k G (Fin n -> G)

end

end Representation
