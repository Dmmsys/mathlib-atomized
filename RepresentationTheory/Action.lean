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
/-
**Representation.linearize** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：linearize : Representation k G k[X.V] where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Set `X` that has a `G`-action on it can be made into a `G`-rep by using `X
 →₀ k` as
  the base module and `G`-action on it is induced by the `G`-action on `X`.
-/
def linearize : Representation k G k[X.V] where
  toFun g := MonoidAlgebra.mapDomainLinearMap k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
/-
**Representation.linearize_single** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：linearize_single (g : G) (x : X.V) : linearize k G X g (.single x 1) = .si
ngle (X.ρ g x) 1
参数：g : G；x : X.V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.linearize_apply`：∀ (k : Type u) (G : Type v) [inst : Mono
id G] [inst_1 : Semiring k] (X : Action (Type w) G) (g : G),   (Representation.l
inearize k G X) g = …
· 使用引理 `MonoidAlgebra.mapDomainLinearMap_single`：mapDomainLinearMap_single (f : 
M -> N) (s : S) (m : M) : mapDomainLinearMap R S f (single m s) = single (f m) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearize_single (g : G) (x : X.V) :
    linearize k G X g (.single x 1) = .single (X.ρ g x) 1 := by
  simp

/-- Every morphism between `G`-sets could be made into an intertwining map between
  `Representation`s by the linear map induced on the indexing sets. -/
@[simps toLinearMap]
/-
**Representation.linearizeMap** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：linearizeMap (f : X ⟶ Y) : IntertwiningMap (A
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every morphism between `G`-sets could be made into an intertwining map between
  `Representation`s by the linear map induced on the indexing sets.
-/
def linearizeMap (f : X ⟶ Y) : IntertwiningMap (A := k) (linearize k G X) (linearize k G Y) where
  toLinearMap := MonoidAlgebra.mapDomainLinearMap k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]
/-
**Representation.linearizeMap_single** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：linearizeMap_single (f : X ⟶ Y) (x : X.V) (r : k) : (linearizeMap f) (.sin
gle x r) = .single (f.hom x) r
参数：f : X ⟶ Y；x : X.V；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomainLinearMap_single`：mapDomainLinearMap_single (f : 
M -> N) (s : S) (m : M) : mapDomainLinearMap R S f (single m s) = single (f m) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearizeMap_single (f : X ⟶ Y) (x : X.V) (r : k) :
    (linearizeMap f) (.single x r) = .single (f.hom x) r := by
  simp [linearizeMap]

namespace LinearizeMonoidal

open scoped MonoidalCategory

attribute [local simp] types_tensorObj_def types_tensorUnit_def

-- These two unification hints are to help lean understand the underlying types of these actions
-- which it fails without them because `types` abuses defeq.
unif_hint (X Y : Action (Type w) G) where ⊢ (X ⊗ Y).V ≟ X.V × Y.V
unif_hint where ⊢ (𝟙_ (Action (Type w) G)).V ≟ PUnit

/-
**Representation.LinearizeMonoidal._root_.Action.tensor_** 是 Mathlib 中的一个引理，位于命名
空间 `Representation.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Action.tensor_ρ_apply (g : G) (xy : (X ⊗ Y).V) :
    (X ⊗ Y).ρ g xy = (X.ρ g xy.1, Y.ρ g xy.2) := rfl

variable (k G) in
-- I could use `Action.trivial G (PUnit)` but that's not reducibly equal to the tensor unit
/-- The counit of the linearize functor. -/
@[simps toLinearMap]
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the linearize functor.
-/
def ε : (trivial k G k).IntertwiningMap (linearize k G (MonoidalCategoryStruct.tensorUnit
    (Action (Type w) G))) where
  __ := MonoidAlgebra.uniqueLinearEquiv k PUnit |>.symm.toLinearMap
  isIntertwining' g := by ext1; simp [linearize_single _]
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_one : ε k G 1 = .single PUnit.unit 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

open scoped MonoidalCategory

variable (k G) in
/-- The unit of the linearize functor. -/
@[simps toLinearMap]
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the linearize functor.
-/
def η : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  toLinearMap := (MonoidAlgebra.uniqueLinearEquiv k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_single (x : PUnit) : η k G (.single x 1) = 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

variable (k G) in
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_η : (ε k G).comp (η k G) = .id _ := by ext; simp

variable (k G) in
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_ε : (η k G).comp (ε k G) = .id _ := by ext; simp

section comm

open scoped MonoidalCategory

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] {σ : Representation k G V}
  {ρ : Representation k G W}

variable (X Y) in
/-- The tensor (multiplication) of the linearize functor. -/
@[simps toLinearMap]
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor (multiplication) of the linearize functor.
-/
def μ : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap (linearize k G (X ⊗ Y)) where
  toLinearMap := (MonoidAlgebra.tensorEquiv k).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]; rfl
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_apply_single_single (x : X.V) (y : Y.V) (r s : k) :
    μ (k := k) X Y (.single x r ⊗ₜ .single y s) = .single (x, y) (r * s) := by
  ext; simp [← toLinearMap_apply]
/-
**Representation.LinearizeMonoidal.coeff_** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_μ_tmul (l1 : k[X.V]) (l2 : k[Y.V]) (xy : (X ⊗ Y).V) :
    (μ X Y (l1 ⊗ₜ l2)).coeff xy = l1.coeff xy.1 * l2.coeff xy.2 := by
  simp [← toLinearMap_apply, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_comp_rTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Y Z).comp (rTensor (linearize k G Z) (linearizeMap f)) =
      (linearizeMap (f ▷ Z)).comp (μ X Z) := by
  ext; simp
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_comp_lTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Z Y).comp ((linearizeMap f).lTensor (linearize k G Z)) =
      (linearizeMap (Z ◁ f)).comp (μ Z X) := by
  ext; simp

variable (X Y Z) in
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_comp_assoc : ((linearizeMap (α_ X Y Z).hom).comp
    (μ (X ⊗ Y) Z)).comp ((μ X Y).rTensor (linearize k G Z)) = ((μ X (Y ⊗ Z)).comp
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
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_leftUnitor : (lid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (λ_ X).hom).comp (μ (𝟙_ (Action (Type w) G)) X)).comp (rTensor
    (linearize k G X) (ε k G)) := by
  ext; simp

variable (X) in
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_rightUnitor : (rid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (ρ_ X).hom).comp (μ X (𝟙_ (Action (Type w) G)))).comp ((ε k G).lTensor
    (linearize k G X)) := by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom]

variable (X Y) in
/-- The comultiplication of the linearize functor. -/
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个定义，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comultiplication of the linearize functor.
-/
def δ : (linearize k G (X ⊗ Y)).IntertwiningMap
    ((linearize k G X).tprod (linearize k G Y)) where
  toLinearMap := (MonoidAlgebra.tensorEquiv k).symm.toLinearMap
  isIntertwining' g := by
    ext; simp [linearize_single _, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]; rfl
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_apply_single (xy : (X ⊗ Y).V) :
    (δ (k := k) X Y) (.single xy 1) = .single xy.1 1 ⊗ₜ .single xy.2 1 := by
  simp [δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

variable (Z) in
/-
**Representation.LinearizeMonoidal.rTensor_comp_** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).rTensor (linearize k G Z)).comp (δ X Z) =
      (δ Y Z).comp (linearizeMap (f ▷ Z)) := by
  ext; simp [δ_apply_single _]

variable (Z) in
/-
**Representation.LinearizeMonoidal.lTensor_comp_** 是 Mathlib 中的一个引理，位于命名空间 `Repr
esentation.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).lTensor (linearize k G Z)).comp (δ Z X) =
      (δ Z Y).comp (linearizeMap (Z ◁ f)) := by
  ext; simp [δ_apply_single _]

variable (X Y Z) in
/-
**Representation.LinearizeMonoidal.assoc_comp_** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma assoc_comp_δ : ((assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap.comp ((δ X Y).rTensor (linearize k G Z))).comp
    (δ (X ⊗ Y) Z) = (((δ Y Z).lTensor (linearize k G X)).comp (δ X (Y ⊗ Z))).comp
    (linearizeMap (α_ X Y Z).hom) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]
/-
**Representation.LinearizeMonoidal.leftUnitor_** 是 Mathlib 中的一个引理，位于命名空间 `Repres
entation.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_δ (X : Action (Type u) G) : (lid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).rTensor (linearize k G X)).comp (δ (𝟙_ (Action (Type u) G)) X)).comp
      (linearizeMap (λ_ X).inv) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

unif_hint (X : Action (Type u) G) where ⊢ (X ⊗ 𝟙_ (Action (Type u) G)).V ≟ X.V × PUnit in
/-
**Representation.LinearizeMonoidal.rightUnitor_** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation.LinearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_δ (X : Action (Type u) G) : (rid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).lTensor (linearize k G X)).comp (δ X (𝟙_ (Action (Type u) G)))).comp
      (linearizeMap (ρ_ X).inv) := by
  ext; simp [δ_apply_single _]

variable (X Y) in
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_δ : (μ X Y).comp (δ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

variable (X Y) in
/-
**Representation.LinearizeMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `Representation.Li
nearizeMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_μ : (δ X Y).comp (μ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

end comm

end LinearizeMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**Representation.linearizeTrivial_def** 是 Mathlib 中的一个引理，位于命名空间 `Representation`
。
形式化陈述：linearizeTrivial_def (X : Type w) (g : G) : linearize k G (Action.trivial 
_ X) g = LinearMap.id
参数：X : Type w；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.lhom_ext'`：lhom_ext' {N : Type*} [Semiring R] [AddCommMono
id N] [Module R N] [Module R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), Linea
rMap.comp f (…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
· 使用引理 `MonoidAlgebra.lsingle_apply`：lsingle_apply [Semiring R] [Module R S] (a 
: M) (b : S) : lsingle (R
· 使用引理 `Representation.linearize_single`：linearize_single (g : G) (x : X.V) : li
nearize k G X g (.single x 1) = .single (X.ρ g x) 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Action.trivial_ρ`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} V] (G : Type u_2) [inst_1 : Monoid G] (X : V),   (Action.trivial G X).ρ = 
1
-/
lemma linearizeTrivial_def (X : Type w) (g : G) :
    linearize k G (Action.trivial _ X) g = LinearMap.id := by
  ext (x : X) : 2
  rw [LinearMap.comp_apply, LinearMap.id_comp, MonoidAlgebra.lsingle_apply, linearize_single]
  simp only [Action.trivial_ρ]
  rfl

variable (k G) in
/-- This a type-changing equivalence (which requires a non-trivial proof that
  `LinearEquiv.refl _ _` is `G`-equivariant) to avoid abusing defeq. -/
/-
**Representation.linearizeTrivialIso** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：linearizeTrivialIso (X : Type w) : (linearize k G (.trivial _ X)).Equiv (t
rivial k G k[X])
参数：X : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This a type-changing equivalence (which requires a non-trivial proof that
  `LinearEquiv.refl _ _` is `G`-equivariant) to avoid abusing defeq.
-/
def linearizeTrivialIso (X : Type w) : (linearize k G (.trivial _ X)).Equiv (trivial k G k[X]) :=
  .mk (.refl ..) fun g ↦ by erw [linearizeTrivial_def, LinearMap.comp_id]

open CategoryTheory
/-
**Representation.linearizeTrivialIso_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representa
tion`。
形式化陈述：linearizeTrivialIso_apply {X : Type w} (f : k[(Action.trivial _ X).V]) : l
inearizeTrivialIso k G X f = f
参数：f : k[(Action.trivial _ X).V]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linearizeTrivialIso_apply {X : Type w} (f : k[(Action.trivial _ X).V]) :
    linearizeTrivialIso k G X f = f := rfl
/-
**Representation.linearizeTrivialIso_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation`。
形式化陈述：linearizeTrivialIso_symm_apply {X : Type w} (f : k[X]) : (linearizeTrivial
Iso k G X).symm f = f
参数：f : k[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linearizeTrivialIso_symm_apply {X : Type w} (f : k[X]) :
    (linearizeTrivialIso k G X).symm f = f := rfl

variable (k G) in
/-- This a type-changing equivalence to avoid abusing defeq. -/
/-
**Representation.linearizeOfMulActionIso** 是 Mathlib 中的一个定义，位于命名空间 `Representati
on`。
形式化陈述：linearizeOfMulActionIso (H : Type w) [MulAction G H] : (linearize k G (Act
ion.ofMulAction G H)).Equiv (ofMulAction k G H)
参数：H : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This a type-changing equivalence to avoid abusing defeq.
-/
def linearizeOfMulActionIso (H : Type w) [MulAction G H] :
    (linearize k G (Action.ofMulAction G H)).Equiv (ofMulAction k G H) :=
  .mk (.refl ..) fun _ ↦ rfl

variable (k G) in
/-- This a type-changing equivalence to avoid abusing defeq. -/
/-
**Representation.linearizeDiagonalEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representat
ion`。
形式化陈述：linearizeDiagonalEquiv (n : Nat) : (linearize k G (Action.diagonal G n)).E
quiv (diagonal k G n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This a type-changing equivalence to avoid abusing defeq.
-/
abbrev linearizeDiagonalEquiv (n : ℕ) : (linearize k G (Action.diagonal G n)).Equiv
    (diagonal k G n) := linearizeOfMulActionIso k G (Fin n → G)

end

end Representation

