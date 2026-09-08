/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive

/-!

# Inner product space structure on tensor product spaces

This file provides the inner product space structure on tensor product spaces.

We define the inner product on `E ⊗ F` by `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, when `E` and `F` are
inner product spaces.

## Main definitions:

* `TensorProduct.instNormedAddCommGroup`: the normed additive group structure on tensor products,
  where `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`.
* `TensorProduct.instInnerProductSpace`: the inner product space structure on tensor products, where
  `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`.
* `TensorProduct.mapIsometry`: the linear isometry version of `TensorProduct.map f g` when
  `f` and `g` are linear isometries.
* `TensorProduct.congrIsometry`: the linear isometry equivalence version of
  `TensorProduct.congr f g` when `f` and `g` are linear isometry equivalences.
* `TensorProduct.mapInclIsometry`: the linear isometry version of `TensorProduct.mapIncl`.
* `TensorProduct.commIsometry`: the linear isometry version of `TensorProduct.comm`.
* `TensorProduct.lidIsometry`: the linear isometry version of `TensorProduct.lid`.
* `TensorProduct.assocIsometry`: the linear isometry version of `TensorProduct.assoc`.
* `TensorProduct.mapL`: the continuous version of `TensorProduct.map f g` when
  `f` and `g` are continuous linear maps.
* `OrthonormalBasis.tensorProduct`: the orthonormal basis of the tensor product of two orthonormal
  bases.

## TODO:

* Define the normed space without needing inner products, this should be analogous to
  `Mathlib/Analysis/NormedSpace/PiTensorProduct/InjectiveSeminorm.lean`.

-/

@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

/-
**TensorProduct.instInner** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：instInner : Inner 𝕜 (E otimes[𝕜] F) where inner x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInner : Inner 𝕜 (E ⊗[𝕜] F) where inner x y :=
  ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y
/-
**TensorProduct.inner_def** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：inner_def (x y : E otimes[𝕜] F) : inner 𝕜 x y = ((lift <| mapBilinear (.id
 𝕜) E F 𝕜 𝕜).compr₂ (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y
参数：x y : E otimes[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inner_def (x y : E ⊗[𝕜] F) :
    inner 𝕜 x y = ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂
      (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y := rfl

variable (𝕜) in
/-
**TensorProduct.inner_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x x' : E)   (y y' : F), inner 𝕜 (x ⊗
ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y'
参数：𝕜 : Type u_1；x x' : E；y y' : F；x ⊗ₜ[𝕜] y；x' ⊗ₜ[𝕜] y'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl
/-
**TensorProduct.inner_map_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H)
   (x y : TensorProduct 𝕜 E F),   inner 𝕜 ((TensorProduct.map f.toLinearMap g.to
LinearMap) x) ((TensorProduct.map f.toLinearMap g.toLinearMap) y) =     inner 𝕜 
x y
参数：f : E →ₗᵢ[𝕜] G；g : F →ₗᵢ[𝕜] H；x y : TensorProduct 𝕜 E F；(TensorProduct.map f.
toLinearMap g.toLinearMap) x；(TensorProduct.map f.toLinearMap g.toLinearMap) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
@[simp] lemma inner_map_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x y : E ⊗[𝕜] F) :
    inner 𝕜 (map f.toLinearMap g.toLinearMap x) (map f.toLinearMap g.toLinearMap y) = inner 𝕜 x y :=
  x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])
/-
**TensorProduct.inner_mapIncl_mapIncl** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：inner_mapIncl_mapIncl (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' 
otimes[𝕜] F') : inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) = inner 𝕜 x y
参数：E' : Submodule 𝕜 E；F' : Submodule 𝕜 F；x y : E' otimes[𝕜] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.inner_map_map`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGro
up E] [inst_2 : I…
-/
lemma inner_mapIncl_mapIncl (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' ⊗[𝕜] F') :
    inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) = inner 𝕜 x y :=
  inner_map_map E'.subtypeₗᵢ F'.subtypeₗᵢ x y

open scoped ComplexOrder
open Module

/-- This holds in any inner product space, but we need this to set up the instance.
This is a helper lemma for showing that this inner product is positive definite. -/
/-
**TensorProduct.inner_self** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This holds in any inner product space, but we need this to set up the instance.
This is a helper lemma for showing that this inner product is positive definite.
-/
private theorem inner_self {ι ι' : Type*} [Fintype ι] [Fintype ι'] (x : E ⊗[𝕜] F)
    (e : OrthonormalBasis ι 𝕜 E) (f : OrthonormalBasis ι' 𝕜 F) :
    inner 𝕜 x x = ∑ i, ‖(e.toBasis.tensorProduct f.toBasis).repr x i‖ ^ 2 := by
  classical
  have : x = ∑ i : ι, ∑ j : ι', (e.toBasis.tensorProduct f.toBasis).repr x (i, j) • e i ⊗ₜ f j := by
    conv_lhs => rw [← (e.toBasis.tensorProduct f.toBasis).sum_repr x]
    simp [← Finset.sum_product', Basis.tensorProduct_apply']
  conv_lhs => rw [this]
  simp only [inner_def, map_sum, LinearMap.sum_apply]
  simp [OrthonormalBasis.inner_eq_ite, ← Finset.sum_product', RCLike.mul_conj]

set_option backward.privateInPublic true in
/-
**TensorProduct.inner_definite** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  /-
  The way we prove this is by noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y : E' ⊗ F', rfl : mapIncl E' F' y = x⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have (i) (j) : (e.toBasis.tensorProduct f.toBasis).repr y (i, j) = 0 := by
    rw [inner_mapIncl_mapIncl, inner_self y e f, RCLike.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hx
    simpa using hx (i, j)
  have : y = 0 := by simp [(e.toBasis.tensorProduct f.toBasis).ext_elem_iff, this]
  rw [this, map_zero]

set_option backward.privateInPublic true in
/-
**TensorProduct.re_inner_self_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private protected theorem re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  rw [inner_mapIncl_mapIncl, inner_self y e f, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**TensorProduct.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`
。
形式化陈述：instNormedAddCommGroup : NormedAddCommGroup (E otimes[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.TensorProduct.0.TensorProduc
t.re_inner_self_nonneg`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : R
CLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [ins
t_3 …
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.TensorProduct.0.TensorProduc
t.inner_definite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 
𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
-/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  letI : InnerProductSpace.Core 𝕜 (E ⊗[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (by simp)
        (by simp_all [inner])) (by simp_all [inner])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }
  this.toNormedAddCommGroup
/-
**TensorProduct.instInnerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：instInnerProductSpace : InnerProductSpace 𝕜 (E otimes[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.TensorProduct.0.TensorProduc
t.re_inner_self_nonneg`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : R
CLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [ins
t_3 …
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.TensorProduct.0.TensorProduc
t.inner_definite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 
𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
-/
instance instInnerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F) := .ofCore _
/-
**TensorProduct.norm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y : F),   ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ 
* ‖y‖
参数：x : E；y : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.re_ofReal_pow`：re_ofReal_pow (a : Real) (n : Nat) : re ((a : K) ^
 n) = a ^ n
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.im_ofReal_pow`：im_ofReal_pow (a : Real) (n : Nat) : im ((a : K) ^
 n) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `TensorProduct.inner_tmul`：∀ (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] [inst_3 …
-/
@[simp] theorem norm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  simpa using congr(√(RCLike.re $(inner_tmul 𝕜 x x y y)))
/-
**TensorProduct.nnnorm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y : F),   ‖x ⊗ₜ[𝕜] y‖₊ = ‖x‖
₊ * ‖y‖₊
参数：x : E；y : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.norm_tmul`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem nnnorm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖₊ = ‖x‖₊ * ‖y‖₊ := by simp [← NNReal.coe_inj]
/-
**TensorProduct.enorm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E) (y : F),   ‖x ⊗ₜ[𝕜] y‖ₑ = ‖x‖
ₑ * ‖y‖ₑ
参数：x : E；y : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.nnnorm_tmul`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem enorm_tmul (x : E) (y : F) :
    ‖x ⊗ₜ[𝕜] y‖ₑ = ‖x‖ₑ * ‖y‖ₑ := ENNReal.coe_inj.mpr <| by simp
/-
**TensorProduct.dist_tmul_le** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：dist_tmul_le (x x' : E) (y y' : F) : dist (x otimesₜ[𝕜] y) (x' otimesₜ y')
 <= ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖
参数：x x' : E；y y' : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.norm_tmul`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] [inst_3 …
-/
theorem dist_tmul_le (x x' : E) (y y' : F) :
    dist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ := by
  grw [dist_eq_norm, norm_sub_le]; simp
/-
**TensorProduct.nndist_tmul_le** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：nndist_tmul_le (x x' : E) (y y' : F) : nndist (x otimesₜ[𝕜] y) (x' otimesₜ
 y') <= ‖x‖₊ * ‖y‖₊ + ‖x'‖₊ * ‖y'‖₊
参数：x x' : E；y y' : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `nnnorm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E),
 ‖a - b‖₊ ≤ ‖a‖₊ + ‖b‖₊
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.nnnorm_tmul`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
-/
theorem nndist_tmul_le (x x' : E) (y y' : F) :
    nndist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖₊ * ‖y‖₊ + ‖x'‖₊ * ‖y'‖₊ := by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp
/-
**TensorProduct.edist_tmul_le** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：edist_tmul_le (x x' : E) (y y' : F) : edist (x otimesₜ[𝕜] y) (x' otimesₜ y
') <= ‖x‖ₑ * ‖y‖ₑ + ‖x'‖ₑ * ‖y'‖ₑ
参数：x x' : E；y y' : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `enorm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a b : E}, 
‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.enorm_tmul`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] [inst_3 …
-/
theorem edist_tmul_le (x x' : E) (y y' : F) :
    edist (x ⊗ₜ[𝕜] y) (x' ⊗ₜ y') ≤ ‖x‖ₑ * ‖y‖ₑ + ‖x'‖ₑ * ‖y'‖ₑ := by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

/-- In `ℝ` or `ℂ` fields, the inner product on tensor products is essentially just the inner product
with multiplication instead of tensors, i.e., `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a * b, c * d⟫`. -/
/-
**TensorProduct._root_.RCLike.inner_tmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In `ℝ` or `ℂ` fields, the inner product on tensor products is essentially just t
he inner product
with multiplication instead of tensors, i.e., `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a * b, c * d⟫
`.
-/
theorem _root_.RCLike.inner_tmul_eq (a b c d : 𝕜) :
    inner 𝕜 (a ⊗ₜ[𝕜] b) (c ⊗ₜ[𝕜] d) = inner 𝕜 (a * b) (c * d) := by
  simp; ring

/-- Given `x, y : E ⊗ F`, `x = y` iff `⟪x, a ⊗ₜ b⟫ = ⟪y, a ⊗ₜ b⟫` for all `a, b`. -/
/-
**TensorProduct.ext_iff_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   {x y : TensorProduct 𝕜 E F}, x = y 
↔ ∀ (a : E) (b : F), inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b)
参数：a : E；b : F；a ⊗ₜ[𝕜] b；a ⊗ₜ[𝕜] b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `innerSL_inj`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {x y : E}, (innerSL 𝕜)
 …
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h

--- 原说明 ---
Given `x, y : E ⊗ F`, `x = y` iff `⟪x, a ⊗ₜ b⟫ = ⟪y, a ⊗ₜ b⟫` for all `a, b`.
-/
protected theorem ext_iff_inner_right {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) :=
  ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ innerSL_inj.mp <| ContinuousLinearMap.coe_inj.mp <| ext' h⟩

/-- Given `x, y : E ⊗ F`, `x = y` iff `⟪a ⊗ₜ b, x⟫ = ⟪a ⊗ₜ b, y⟫` for all `a, b`. -/
/-
**TensorProduct.ext_iff_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   {x y : TensorProduct 𝕜 E F}, x = y 
↔ ∀ (a : E) (b : F), inner 𝕜 (a ⊗ₜ[𝕜] b) x = inner 𝕜 (a ⊗ₜ[𝕜] b) y
参数：a : E；b : F；a ⊗ₜ[𝕜] b；a ⊗ₜ[𝕜] b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `TensorProduct.ext_iff_inner_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …

--- 原说明 ---
Given `x, y : E ⊗ F`, `x = y` iff `⟪a ⊗ₜ b, x⟫ = ⟪a ⊗ₜ b, y⟫` for all `a, b`.
-/
protected theorem ext_iff_inner_left {x y : E ⊗[𝕜] F} :
    x = y ↔ ∀ a b, inner 𝕜 (a ⊗ₜ b) x = inner 𝕜 (a ⊗ₜ b) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    TensorProduct.ext_iff_inner_right (x := x) (y := y)

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪x, a ⊗ₜ b ⊗ₜ c⟫ = ⟪y, a ⊗ₜ b ⊗ₜ c⟫` for all `a, b, c`.

See also `ext_iff_inner_right_threefold'` for when `x, y : E ⊗ (F ⊗ G)`. -/
/-
**TensorProduct.ext_iff_inner_right_threefold** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct`。
形式化陈述：ext_iff_inner_right_threefold {x y : E otimes[𝕜] F otimes[𝕜] G} : x = y ↔ 
forall a b c, inner 𝕜 x (a otimesₜ[𝕜] b otimesₜ[𝕜] c) = inner 𝕜 y (a otimesₜ[𝕜] 
b otimesₜ[𝕜] c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `innerSL_inj`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_3} [inst_1 :
 NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {x y : E}, (innerSL 𝕜)
 …
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `TensorProduct.ext_threefold`：ext_threefold {g h : M otimes[R] N otimes[R
] P ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y 
otimesₜ z)) : g =…

--- 原说明 ---
Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪x, a ⊗ₜ b ⊗ₜ c⟫ = ⟪y, a ⊗ₜ b ⊗ₜ c⟫` for 
all `a, b, c`.

See also `ext_iff_inner_right_threefold'` for when `x, y : E ⊗ (F ⊗ G)`.
-/
theorem ext_iff_inner_right_threefold {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) = inner 𝕜 y (a ⊗ₜ[𝕜] b ⊗ₜ[𝕜] c) :=
  ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ innerSL_inj.mp (ContinuousLinearMap.coe_inj.mp (ext_threefold h))⟩

/-- Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪a ⊗ₜ b ⊗ₜ c, x⟫ = ⟪a ⊗ₜ b ⊗ₜ c, y⟫` for all `a, b, c`.

See also `ext_iff_inner_left_threefold'` for when `x, y : E ⊗ (F ⊗ G)`. -/
/-
**TensorProduct.ext_iff_inner_left_threefold** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct`。
形式化陈述：ext_iff_inner_left_threefold {x y : E otimes[𝕜] F otimes[𝕜] G} : x = y ↔ f
orall a b c, inner 𝕜 (a otimesₜ b otimesₜ c) x = inner 𝕜 (a otimesₜ b otimesₜ c)
 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `TensorProduct.ext_iff_inner_right_threefold`：ext_iff_inner_right_threefo
ld {x y : E otimes[𝕜] F otimes[𝕜] G} : x = y ↔ forall a b c, inner 𝕜 x (a otimes
ₜ[𝕜] b otimesₜ[𝕜] c) = inner 𝕜 y …

--- 原说明 ---
Given `x, y : E ⊗ F ⊗ G`, `x = y` iff `⟪a ⊗ₜ b ⊗ₜ c, x⟫ = ⟪a ⊗ₜ b ⊗ₜ c, y⟫` for 
all `a, b, c`.

See also `ext_iff_inner_left_threefold'` for when `x, y : E ⊗ (F ⊗ G)`.
-/
theorem ext_iff_inner_left_threefold {x y : E ⊗[𝕜] F ⊗[𝕜] G} :
    x = y ↔ ∀ a b c, inner 𝕜 (a ⊗ₜ b ⊗ₜ c) x = inner 𝕜 (a ⊗ₜ b ⊗ₜ c) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold (x := x) (y := y)

variable (𝕜 E F) in
/-- The canonical continuous bilinear map `E → F → E ⊗ F`. This is the continuous version of
`mk`. -/
/-
**TensorProduct.mkL** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mkL : E ->L[𝕜] F ->L[𝕜] E otimes[𝕜] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical continuous bilinear map `E → F → E ⊗ F`. This is the continuous ve
rsion of
`mk`.
-/
noncomputable def mkL : E →L[𝕜] F →L[𝕜] E ⊗[𝕜] F := (mk 𝕜 E F).mkContinuous₂ 1 fun _ _ ↦ by simp
/-
**TensorProduct.coe_mkL_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E),   ⇑((TensorProduct.mkL 𝕜 E F
) x) = ⇑((TensorProduct.mk 𝕜 E F) x)
参数：x : E；(TensorProduct.mkL 𝕜 E F) x；(TensorProduct.mk 𝕜 E F) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
@[simp] lemma coe_mkL_apply (x : E) : ⇑(mkL 𝕜 E F x) = mk 𝕜 E F x := rfl
/-
**TensorProduct.toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap₁₂_mkL : (mkL 𝕜 E F).toLinearMap₁₂ = mk 𝕜 E F := rfl
/-
**TensorProduct.toLinearMap_mkL_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (x : E),   ↑((TensorProduct.mkL 𝕜 E F
) x) = (TensorProduct.mk 𝕜 E F) x
参数：x : E；(TensorProduct.mkL 𝕜 E F) x；TensorProduct.mk 𝕜 E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
@[simp] lemma toLinearMap_mkL_apply (x : E) : (mkL 𝕜 E F x).toLinearMap = mk 𝕜 E F x := rfl
/-
**TensorProduct.mkL_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mkL_apply_apply (x : E) (y : F) : mkL 𝕜 E F x y = x otimesₜ y
参数：x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma mkL_apply_apply (x : E) (y : F) : mkL 𝕜 E F x y = x ⊗ₜ y := rfl
/-
**TensorProduct.continuous_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F],   Continuous fun x => x.1 ⊗ₜ[𝕜] x.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
-/
@[fun_prop] lemma continuous_tmul : Continuous fun x : E × F ↦ x.1 ⊗ₜ[𝕜] x.2 :=
  (mkL 𝕜 E F).continuous₂

section isometry

/-- The tensor product map of two linear isometries is a linear isometry. In particular, this is
the linear isometry version of `TensorProduct.map f g` when `f` and `g` are linear isometries. -/
/-
**TensorProduct.mapIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mapIsometry (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) : E otimes[𝕜] F ->ₗᵢ[𝕜] G 
otimes[𝕜] H
参数：f : E ->ₗᵢ[𝕜] G；g : F ->ₗᵢ[𝕜] H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.inner_map_map`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGro
up E] [inst_2 : I…

--- 原说明 ---
The tensor product map of two linear isometries is a linear isometry. In particu
lar, this is
the linear isometry version of `TensorProduct.map f g` when `f` and `g` are line
ar isometries.
-/
noncomputable def mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F →ₗᵢ[𝕜] G ⊗[𝕜] H :=
  map f.toLinearMap g.toLinearMap |>.isometryOfInner <| inner_map_map _ _
/-
**TensorProduct.mapIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H)
   (x : TensorProduct 𝕜 E F), (TensorProduct.mapIsometry f g) x = (TensorProduct
.map f.toLinearMap g.toLinearMap) x
参数：f : E →ₗᵢ[𝕜] G；g : F →ₗᵢ[𝕜] H；x : TensorProduct 𝕜 E F；TensorProduct.mapIsomet
ry f g；TensorProduct.map f.toLinearMap g.toLinearMap。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapIsometry_apply (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    mapIsometry f g x = map f.toLinearMap g.toLinearMap x := rfl
/-
**TensorProduct.toLinearMap_mapIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H)
,   (TensorProduct.mapIsometry f g).toLinearMap = TensorProduct.map f.toLinearMa
p g.toLinearMap
参数：f : E →ₗᵢ[𝕜] G；g : F →ₗᵢ[𝕜] H；TensorProduct.mapIsometry f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_mapIsometry (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    (mapIsometry f g).toLinearMap = map f.toLinearMap g.toLinearMap := rfl
/-
**TensorProduct.norm_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H)
   (x : TensorProduct 𝕜 E F), ‖(TensorProduct.map f.toLinearMap g.toLinearMap) x
‖ = ‖x‖
参数：f : E →ₗᵢ[𝕜] G；g : F →ₗᵢ[𝕜] H；x : TensorProduct 𝕜 E F；TensorProduct.map f.toL
inearMap g.toLinearMap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
@[simp] lemma norm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖ = ‖x‖ := mapIsometry f g |>.norm_map x
/-
**TensorProduct.nnnorm_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H)
   (x : TensorProduct 𝕜 E F), ‖(TensorProduct.map f.toLinearMap g.toLinearMap) x
‖₊ = ‖x‖₊
参数：f : E →ₗᵢ[𝕜] G；g : F →ₗᵢ[𝕜] H；x : TensorProduct 𝕜 E F；TensorProduct.map f.toL
inearMap g.toLinearMap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.nnnorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_
5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂}
 [inst_2 : Semi…
-/
@[simp] lemma nnnorm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖₊ = ‖x‖₊ := mapIsometry f g |>.nnnorm_map x
/-
**TensorProduct.enorm_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H)
   (x : TensorProduct 𝕜 E F), ‖(TensorProduct.map f.toLinearMap g.toLinearMap) x
‖ₑ = ‖x‖ₑ
参数：f : E →ₗᵢ[𝕜] G；g : F →ₗᵢ[𝕜] H；x : TensorProduct 𝕜 E F；TensorProduct.map f.toL
inearMap g.toLinearMap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.enorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5
} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
@[simp] lemma enorm_map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    ‖map f.toLinearMap g.toLinearMap x‖ₑ = ‖x‖ₑ := mapIsometry f g |>.enorm_map x
/-
**TensorProduct.mapIsometry_id_id** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F],   TensorProduct.mapIsometry LinearIs
ometry.id LinearIsometry.id = LinearIsometry.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.ext`：ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapIsometry_id_id :
    mapIsometry (.id : E →ₗᵢ[𝕜] E) (.id : F →ₗᵢ[𝕜] F) = .id := by ext; simp

variable (E) in
/-- This is the natural linear isometry induced by `f : F ≃ₗᵢ G`. -/
/-
**TensorProduct._root_.LinearIsometry.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `TensorP
roduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the natural linear isometry induced by `f : F ≃ₗᵢ G`.
-/
noncomputable def _root_.LinearIsometry.lTensor (f : F →ₗᵢ[𝕜] G) :
    E ⊗[𝕜] F →ₗᵢ[𝕜] E ⊗[𝕜] G := mapIsometry .id f

variable (G) in
/-- This is the natural linear isometry induced by `f : E ≃ₗᵢ F`. -/
/-
**TensorProduct._root_.LinearIsometry.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `TensorP
roduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the natural linear isometry induced by `f : E ≃ₗᵢ F`.
-/
noncomputable def _root_.LinearIsometry.rTensor (f : E →ₗᵢ[𝕜] F) :
    E ⊗[𝕜] G →ₗᵢ[𝕜] F ⊗[𝕜] G := mapIsometry f .id
/-
**TensorProduct._root_.LinearIsometry.lTensor_def** 是 Mathlib 中的一个引理，位于命名空间 `Ten
sorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometry.lTensor_def (f : F →ₗᵢ[𝕜] G) :
    f.lTensor E = mapIsometry .id f := rfl
/-
**TensorProduct._root_.LinearIsometry.rTensor_def** 是 Mathlib 中的一个引理，位于命名空间 `Ten
sorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometry.rTensor_def (f : E →ₗᵢ[𝕜] F) :
    f.rTensor G = mapIsometry f .id := rfl
/-
**TensorProduct._root_.LinearIsometry.toLinearMap_lTensor** 是 Mathlib 中的一个引理，位于命
名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometry.toLinearMap_lTensor (f : F →ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearMap = f.toLinearMap.lTensor E := rfl
/-
**TensorProduct._root_.LinearIsometry.toLinearMap_rTensor** 是 Mathlib 中的一个引理，位于命
名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometry.toLinearMap_rTensor (f : E →ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl
/-
**TensorProduct._root_.LinearIsometry.lTensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `T
ensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometry.lTensor_apply (f : F →ₗᵢ[𝕜] G) (x : E ⊗[𝕜] F) :
    f.lTensor E x = f.toLinearMap.lTensor E x := rfl
/-
**TensorProduct._root_.LinearIsometry.rTensor_apply** 是 Mathlib 中的一个引理，位于命名空间 `T
ensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometry.rTensor_apply (f : E →ₗᵢ[𝕜] F) (x : E ⊗[𝕜] G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

/-- The tensor product of two linear isometry equivalences is a linear isometry equivalence.
In particular, this is the linear isometry equivalence version of `TensorProduct.congr f g` when `f`
and `g` are linear isometry equivalences. -/
/-
**TensorProduct.congrIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) : E otimes[𝕜] F ≃ₗᵢ[𝕜] G o
times[𝕜] H
参数：f : E ≃ₗᵢ[𝕜] G；g : F ≃ₗᵢ[𝕜] H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two linear isometry equivalences is a linear isometry equi
valence.
In particular, this is the linear isometry equivalence version of `TensorProduct
.congr f g` when `f`
and `g` are linear isometry equivalences.
-/
noncomputable def congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] G ⊗[𝕜] H :=
  congr f.toLinearEquiv g.toLinearEquiv |>.isometryOfInner <|
    inner_map_map f.toLinearIsometry g.toLinearIsometry
/-
**TensorProduct.congrIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
   (x : TensorProduct 𝕜 E F), (TensorProduct.congrIsometry f g) x = (TensorProdu
ct.congr ↑↑f ↑↑g) x
参数：f : E ≃ₗᵢ[𝕜] G；g : F ≃ₗᵢ[𝕜] H；x : TensorProduct 𝕜 E F；TensorProduct.congrIsom
etry f g；TensorProduct.congr ↑↑f ↑↑g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma congrIsometry_apply (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E ⊗[𝕜] F) :
    congrIsometry f g x = congr (σ₁₂ := .id _) f g x := rfl
/-
**TensorProduct.congrIsometry_symm** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：congrIsometry_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) : (congrIsometry f g)
.symm = congrIsometry f.symm g.symm
参数：f : E ≃ₗᵢ[𝕜] G；g : F ≃ₗᵢ[𝕜] H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congrIsometry_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).symm = congrIsometry f.symm g.symm := rfl
/-
**TensorProduct.toLinearEquiv_congrIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
,   (TensorProduct.congrIsometry f g).toLinearEquiv = TensorProduct.congr f.toLi
nearEquiv g.toLinearEquiv
参数：f : E ≃ₗᵢ[𝕜] G；g : F ≃ₗᵢ[𝕜] H；TensorProduct.congrIsometry f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).toLinearEquiv = congr f.toLinearEquiv g.toLinearEquiv := rfl
/-
**TensorProduct.congrIsometry_refl_refl** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F],   TensorProduct.congrIsometry (Linea
rIsometryEquiv.refl 𝕜 E) (LinearIsometryEquiv.refl 𝕜 F) =     LinearIsometryEqui
v.refl 𝕜 (TensorProduct 𝕜 E F)
参数：LinearIsometryEquiv.refl 𝕜 E；LinearIsometryEquiv.refl 𝕜 F；TensorProduct 𝕜 E F
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearIsometryEquiv.toLinearEquiv_inj`：toLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ
₁₂] E₂} : f.toLinearEquiv = g.toLinearEquiv ↔ f = g
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.congr_refl_refl`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id N] [inst_3 : _ro…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma congrIsometry_refl_refl :
    congrIsometry (.refl 𝕜 E) (.refl 𝕜 F) = .refl 𝕜 (E ⊗ F) :=
  LinearIsometryEquiv.toLinearEquiv_inj.mp <| LinearEquiv.toLinearMap_inj.mp <| by ext; simp

variable (E) in
/-- This is the natural linear isometric equivalence induced by `f : F ≃ₗᵢ G`. -/
/-
**TensorProduct._root_.LinearIsometryEquiv.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `Te
nsorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the natural linear isometric equivalence induced by `f : F ≃ₗᵢ G`.
-/
noncomputable def _root_.LinearIsometryEquiv.lTensor (f : F ≃ₗᵢ[𝕜] G) :
    E ⊗[𝕜] F ≃ₗᵢ[𝕜] E ⊗[𝕜] G := congrIsometry (.refl 𝕜 E) f

variable (G) in
/-- This is the natural linear isometric equivalence induced by `f : E ≃ₗᵢ F`. -/
/-
**TensorProduct._root_.LinearIsometryEquiv.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `Te
nsorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the natural linear isometric equivalence induced by `f : E ≃ₗᵢ F`.
-/
noncomputable def _root_.LinearIsometryEquiv.rTensor (f : E ≃ₗᵢ[𝕜] F) :
    E ⊗[𝕜] G ≃ₗᵢ[𝕜] F ⊗[𝕜] G := congrIsometry f (.refl 𝕜 G)
/-
**TensorProduct._root_.LinearIsometryEquiv.lTensor_def** 是 Mathlib 中的一个引理，位于命名空间
 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometryEquiv.lTensor_def (f : F ≃ₗᵢ[𝕜] G) :
    f.lTensor E = congrIsometry (.refl 𝕜 E) f := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.rTensor_def** 是 Mathlib 中的一个引理，位于命名空间
 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometryEquiv.rTensor_def (f : E ≃ₗᵢ[𝕜] F) :
    f.rTensor G = congrIsometry f (.refl 𝕜 G) := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.symm_lTensor** 是 Mathlib 中的一个引理，位于命名空
间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometryEquiv.symm_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).symm = f.symm.lTensor E := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.symm_rTensor** 是 Mathlib 中的一个引理，位于命名空
间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometryEquiv.symm_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).symm = f.symm.rTensor G := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.toLinearEquiv_lTensor** 是 Mathlib 中的一
个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearEquiv = f.toLinearEquiv.lTensor E := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.toLinearIsometry_lTensor** 是 Mathlib 
中的一个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearIsometry = f.toLinearIsometry.lTensor E := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.toLinearEquiv_rTensor** 是 Mathlib 中的一
个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearEquiv = f.toLinearEquiv.rTensor G := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.toLinearIsometry_rTensor** 是 Mathlib 
中的一个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearIsometry = f.toLinearIsometry.rTensor G := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.lTensor_apply** 是 Mathlib 中的一个引理，位于命名
空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometryEquiv.lTensor_apply (f : F ≃ₗᵢ[𝕜] G) (x : E ⊗[𝕜] F) :
    f.lTensor E x = f.toLinearEquiv.lTensor E x := rfl
/-
**TensorProduct._root_.LinearIsometryEquiv.rTensor_apply** 是 Mathlib 中的一个引理，位于命名
空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometryEquiv.rTensor_apply (f : E ≃ₗᵢ[𝕜] F) (x : E ⊗[𝕜] G) :
    f.rTensor G x = f.toLinearEquiv.rTensor G x := rfl

/-- The linear isometry version of `TensorProduct.mapIncl`. -/
/-
**TensorProduct.mapInclIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) : E' otimes[𝕜] F
' ->ₗᵢ[𝕜] E otimes[𝕜] F
参数：E' : Submodule 𝕜 E；F' : Submodule 𝕜 F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear isometry version of `TensorProduct.mapIncl`.
-/
noncomputable def mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    E' ⊗[𝕜] F' →ₗᵢ[𝕜] E ⊗[𝕜] F :=
  mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ
/-
**TensorProduct.mapInclIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (E' : Submodule 𝕜 E)   (F' : Submodul
e 𝕜 F) (x : TensorProduct 𝕜 ↥E' ↥F'),   (TensorProduct.mapInclIsometry E' F') x 
= (TensorProduct.mapIncl E' F') x
参数：E' : Submodule 𝕜 E；F' : Submodule 𝕜 F；x : TensorProduct 𝕜 ↥E' ↥F'；TensorProdu
ct.mapInclIsometry E' F'；TensorProduct.mapIncl E' F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapInclIsometry_apply (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (x : E' ⊗[𝕜] F') : mapInclIsometry E' F' x = mapIncl E' F' x := rfl
/-
**TensorProduct.toLinearMap_mapInclIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (E' : Submodule 𝕜 E)   (F' : Submodul
e 𝕜 F), (TensorProduct.mapInclIsometry E' F').toLinearMap = TensorProduct.mapInc
l E' F'
参数：E' : Submodule 𝕜 E；F' : Submodule 𝕜 F；TensorProduct.mapInclIsometry E' F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    (mapInclIsometry E' F').toLinearMap = mapIncl E' F' := rfl
/-
**TensorProduct.inner_comm_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   (x y : TensorProduct 𝕜 E F), inner 
𝕜 ((TensorProduct.comm 𝕜 E F) x) ((TensorProduct.comm 𝕜 E F) y) = inner 𝕜 x y
参数：x y : TensorProduct 𝕜 E F；(TensorProduct.comm 𝕜 E F) x；(TensorProduct.comm 𝕜 
E F) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
-/
@[simp] theorem inner_comm_comm (x y : E ⊗[𝕜] F) :
    inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [mul_comm])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F) in
/-- The linear isometry equivalence version of `TensorProduct.comm`. -/
/-
**TensorProduct.commIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：commIsometry : E otimes[𝕜] F ≃ₗᵢ[𝕜] F otimes[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.inner_comm_comm`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] [inst_3 …

--- 原说明 ---
The linear isometry equivalence version of `TensorProduct.comm`.
-/
noncomputable def commIsometry : E ⊗[𝕜] F ≃ₗᵢ[𝕜] F ⊗[𝕜] E :=
  TensorProduct.comm 𝕜 E F |>.isometryOfInner inner_comm_comm
/-
**TensorProduct.commIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   (x : TensorProduct 𝕜 E F), (TensorP
roduct.commIsometry 𝕜 E F) x = (TensorProduct.comm 𝕜 E F) x
参数：x : TensorProduct 𝕜 E F；TensorProduct.commIsometry 𝕜 E F；TensorProduct.comm 𝕜
 E F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma commIsometry_apply (x : E ⊗[𝕜] F) :
    commIsometry 𝕜 E F x = TensorProduct.comm 𝕜 E F x := rfl
/-
**TensorProduct.commIsometry_symm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F],   (TensorProduct.commIsometry 𝕜 E F)
.symm = TensorProduct.commIsometry 𝕜 F E
参数：TensorProduct.commIsometry 𝕜 E F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma commIsometry_symm :
    (commIsometry 𝕜 E F).symm = commIsometry 𝕜 F E := rfl
/-
**TensorProduct.toLinearEquiv_commIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorProd
uct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F],   (TensorProduct.commIsometry 𝕜 E F)
.toLinearEquiv = TensorProduct.comm 𝕜 E F
参数：TensorProduct.commIsometry 𝕜 E F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_commIsometry :
    (commIsometry 𝕜 E F).toLinearEquiv = TensorProduct.comm 𝕜 E F := rfl
/-
**TensorProduct.norm_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   (x : TensorProduct 𝕜 E F), ‖(Tensor
Product.comm 𝕜 E F) x‖ = ‖x‖
参数：x : TensorProduct 𝕜 E F；TensorProduct.comm 𝕜 E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma norm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖ = ‖x‖ := commIsometry 𝕜 E F |>.norm_map x
/-
**TensorProduct.nnnorm_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   (x : TensorProduct 𝕜 E F), ‖(Tensor
Product.comm 𝕜 E F) x‖₊ = ‖x‖₊
参数：x : TensorProduct 𝕜 E F；TensorProduct.comm 𝕜 E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.nnnorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma nnnorm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖₊ = ‖x‖₊ := commIsometry 𝕜 E F |>.nnnorm_map x
/-
**TensorProduct.enorm_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F]   (x : TensorProduct 𝕜 E F), ‖(Tensor
Product.comm 𝕜 E F) x‖ₑ = ‖x‖ₑ
参数：x : TensorProduct 𝕜 E F；TensorProduct.comm 𝕜 E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.enorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5
} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
@[simp] lemma enorm_comm (x : E ⊗[𝕜] F) :
    ‖TensorProduct.comm 𝕜 E F x‖ₑ = ‖x‖ₑ := commIsometry 𝕜 E F |>.toLinearIsometry.enorm_map x
/-
**TensorProduct.inner_lid_lid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x y : TensorProduct 𝕜 𝕜 E), inner 𝕜 
((TensorProduct.lid 𝕜 E) x) ((TensorProduct.lid 𝕜 E) y) = inner 𝕜 x y
参数：x y : TensorProduct 𝕜 𝕜 E；(TensorProduct.lid 𝕜 E) x；(TensorProduct.lid 𝕜 E) y
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
-/
@[simp] theorem inner_lid_lid (x y : 𝕜 ⊗[𝕜] E) :
    inner 𝕜 (TensorProduct.lid 𝕜 E x) (TensorProduct.lid 𝕜 E y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.lid`. -/
/-
**TensorProduct.lidIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：lidIsometry : 𝕜 otimes[𝕜] E ≃ₗᵢ[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.inner_lid_lid`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (x y :
 TensorProduct 𝕜 …

--- 原说明 ---
The linear isometry equivalence version of `TensorProduct.lid`.
-/
noncomputable def lidIsometry : 𝕜 ⊗[𝕜] E ≃ₗᵢ[𝕜] E :=
  TensorProduct.lid 𝕜 E |>.isometryOfInner inner_lid_lid
/-
**TensorProduct.toLinearEquiv_lidIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorProdu
ct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E],   (TensorProduct.lidIsometry 𝕜 E).toLi
nearEquiv = TensorProduct.lid 𝕜 E
参数：TensorProduct.lidIsometry 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_lidIsometry :
    (lidIsometry 𝕜 E).toLinearEquiv = TensorProduct.lid 𝕜 E := rfl
/-
**TensorProduct.toContinuousLinearMap_symm_lidIsometry** 是 Mathlib 中的一个引理，位于命名空间
 `TensorProduct`。
形式化陈述：toContinuousLinearMap_symm_lidIsometry : (lidIsometry 𝕜 E).symm.toContinuo
usLinearEquiv.toContinuousLinearMap = mkL 𝕜 𝕜 E 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_symm_lidIsometry :
    (lidIsometry 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap = mkL 𝕜 𝕜 E 1 := rfl
/-
**TensorProduct.lidIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 𝕜 E), (TensorPro
duct.lidIsometry 𝕜 E) x = (TensorProduct.lid 𝕜 E) x
参数：x : TensorProduct 𝕜 𝕜 E；TensorProduct.lidIsometry 𝕜 E；TensorProduct.lid 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lidIsometry_apply (x : 𝕜 ⊗[𝕜] E) : lidIsometry 𝕜 E x = TensorProduct.lid 𝕜 E x := rfl
/-
**TensorProduct.lidIsometry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`
。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : E), (TensorProduct.lidIsometry 𝕜
 E).symm x = 1 ⊗ₜ[𝕜] x
参数：x : E；TensorProduct.lidIsometry 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lidIsometry_symm_apply (x : E) : (lidIsometry 𝕜 E).symm x = 1 ⊗ₜ x := rfl
/-
**TensorProduct.norm_lid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 𝕜 E), ‖(TensorPr
oduct.lid 𝕜 E) x‖ = ‖x‖
参数：x : TensorProduct 𝕜 𝕜 E；TensorProduct.lid 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma norm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖ = ‖x‖ := (lidIsometry 𝕜 E).norm_map x
/-
**TensorProduct.nnnorm_lid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 𝕜 E), ‖(TensorPr
oduct.lid 𝕜 E) x‖₊ = ‖x‖₊
参数：x : TensorProduct 𝕜 𝕜 E；TensorProduct.lid 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.nnnorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma nnnorm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖₊ = ‖x‖₊ := lidIsometry 𝕜 E |>.nnnorm_map x
/-
**TensorProduct.enorm_lid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 𝕜 E), ‖(TensorPr
oduct.lid 𝕜 E) x‖ₑ = ‖x‖ₑ
参数：x : TensorProduct 𝕜 𝕜 E；TensorProduct.lid 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.enorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5
} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
@[simp] lemma enorm_lid (x : 𝕜 ⊗[𝕜] E) :
    ‖TensorProduct.lid 𝕜 E x‖ₑ = ‖x‖ₑ := lidIsometry 𝕜 E |>.toLinearIsometry.enorm_map x
/-
**TensorProduct.inner_rid_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x y : TensorProduct 𝕜 E 𝕜), inner 𝕜 
((TensorProduct.rid 𝕜 E) x) ((TensorProduct.rid 𝕜 E) y) = inner 𝕜 x y
参数：x y : TensorProduct 𝕜 E 𝕜；(TensorProduct.rid 𝕜 E) x；(TensorProduct.rid 𝕜 E) y
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.inner_lid_lid`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (x y :
 TensorProduct 𝕜 …
· 使用定理 `TensorProduct.inner_comm_comm`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem inner_rid_rid (x y : E ⊗[𝕜] 𝕜) :
    inner 𝕜 (TensorProduct.rid 𝕜 E x) (TensorProduct.rid 𝕜 E y) = inner 𝕜 x y := by
  simp [← lid_comm]

variable (𝕜 E) in
/-- The linear isometry equivalence version of `TensorProduct.rid`. -/
/-
**TensorProduct.ridIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：ridIsometry : E otimes[𝕜] 𝕜 ≃ₗᵢ[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.inner_rid_rid`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (x y :
 TensorProduct 𝕜 …

--- 原说明 ---
The linear isometry equivalence version of `TensorProduct.rid`.
-/
noncomputable def ridIsometry : E ⊗[𝕜] 𝕜 ≃ₗᵢ[𝕜] E :=
  TensorProduct.rid 𝕜 E |>.isometryOfInner inner_rid_rid
/-
**TensorProduct.toLinearEquiv_ridIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorProdu
ct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E],   (TensorProduct.ridIsometry 𝕜 E).toLi
nearEquiv = TensorProduct.rid 𝕜 E
参数：TensorProduct.ridIsometry 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_ridIsometry :
    (ridIsometry 𝕜 E).toLinearEquiv = TensorProduct.rid 𝕜 E := rfl
/-
**TensorProduct.toContinuousLinearMap_symm_ridIsometry** 是 Mathlib 中的一个引理，位于命名空间
 `TensorProduct`。
形式化陈述：toContinuousLinearMap_symm_ridIsometry : (ridIsometry 𝕜 E).symm.toContinuo
usLinearEquiv.toContinuousLinearMap = (mkL 𝕜 E 𝕜).flip 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_symm_ridIsometry :
    (ridIsometry 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap = (mkL 𝕜 E 𝕜).flip 1 := rfl
/-
**TensorProduct.ridIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 E 𝕜), (TensorPro
duct.ridIsometry 𝕜 E) x = (TensorProduct.rid 𝕜 E) x
参数：x : TensorProduct 𝕜 E 𝕜；TensorProduct.ridIsometry 𝕜 E；TensorProduct.rid 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ridIsometry_apply (x) : ridIsometry 𝕜 E x = TensorProduct.rid 𝕜 E x := rfl
/-
**TensorProduct.symm_ridIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`
。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : E), (TensorProduct.ridIsometry 𝕜
 E).symm x = x ⊗ₜ[𝕜] 1
参数：x : E；TensorProduct.ridIsometry 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_ridIsometry_apply (x) : (ridIsometry 𝕜 E).symm x = x ⊗ₜ 1 := rfl
/-
**TensorProduct.lidIsometry_eq_ridIsometry** 是 Mathlib 中的一个引理，位于命名空间 `TensorProd
uct`。
形式化陈述：lidIsometry_eq_ridIsometry : lidIsometry 𝕜 𝕜 = ridIsometry 𝕜 𝕜
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.lid_eq_rid`：lid_eq_rid : TensorProduct.lid R R = TensorPro
duct.rid R R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lidIsometry_eq_ridIsometry : lidIsometry 𝕜 𝕜 = ridIsometry 𝕜 𝕜 := by ext; simp [lid_eq_rid]
/-
**TensorProduct.norm_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 E 𝕜), ‖(TensorPr
oduct.rid 𝕜 E) x‖ = ‖x‖
参数：x : TensorProduct 𝕜 E 𝕜；TensorProduct.rid 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma norm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖ = ‖x‖ := (ridIsometry 𝕜 E).norm_map x
/-
**TensorProduct.nnnorm_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 E 𝕜), ‖(TensorPr
oduct.rid 𝕜 E) x‖₊ = ‖x‖₊
参数：x : TensorProduct 𝕜 E 𝕜；TensorProduct.rid 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.norm_rid`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : Tensor
Product 𝕜 E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nnnorm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖₊ = ‖x‖₊ := by simp [← NNReal.coe_inj]
/-
**TensorProduct.enorm_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : TensorProduct 𝕜 E 𝕜), ‖(TensorPr
oduct.rid 𝕜 E) x‖ₑ = ‖x‖ₑ
参数：x : TensorProduct 𝕜 E 𝕜；TensorProduct.rid 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.enorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5
} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
@[simp] lemma enorm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖ₑ = ‖x‖ₑ :=
  ridIsometry 𝕜 E |>.toLinearIsometry.enorm_map x
/-
**TensorProduct.commIsometry_trans_lidIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E],   (TensorProduct.commIsometry 𝕜 E 𝕜).t
rans (TensorProduct.lidIsometry 𝕜 E) = TensorProduct.ridIsometry 𝕜 E
参数：TensorProduct.commIsometry 𝕜 E 𝕜；TensorProduct.lidIsometry 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.lid_comm`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Ty
pe u_5} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (x : TensorPro
duct R M R),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma commIsometry_trans_lidIsometry :
    (commIsometry 𝕜 E 𝕜).trans (lidIsometry 𝕜 E) = ridIsometry 𝕜 E := by ext; simp
/-
**TensorProduct.commIsometry_trans_ridIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E],   (TensorProduct.commIsometry 𝕜 𝕜 E).t
rans (TensorProduct.ridIsometry 𝕜 E) = TensorProduct.lidIsometry 𝕜 E
参数：TensorProduct.commIsometry 𝕜 𝕜 E；TensorProduct.ridIsometry 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.rid_comm`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Ty
pe u_5} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (x : TensorPro
duct R R M),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma commIsometry_trans_ridIsometry :
    (commIsometry 𝕜 𝕜 E).trans (ridIsometry 𝕜 E) = lidIsometry 𝕜 E := by ext; simp
/-
**TensorProduct.inner_assoc_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (x y : TensorProduct 𝕜 (TensorProdu
ct 𝕜 E F) G),   inner 𝕜 ((TensorProduct.assoc 𝕜 E F G) x) ((TensorProduct.assoc 
𝕜 E F G) y) = inner 𝕜 x y
参数：x y : TensorProduct 𝕜 (TensorProduct 𝕜 E F) G；(TensorProduct.assoc 𝕜 E F G) x
；(TensorProduct.assoc 𝕜 E F G) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
-/
@[simp] theorem inner_assoc_assoc (x y : E ⊗[𝕜] F ⊗[𝕜] G) :
    inner 𝕜 (TensorProduct.assoc 𝕜 E F G x) (TensorProduct.assoc 𝕜 E F G y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun a _ =>
    y.induction_on (by simp) (fun c _ =>
      a.induction_on (by simp) (fun _ _ =>
        c.induction_on (by simp) (by simp [mul_assoc])
        fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2])
      fun _ _ h1 h2 => by simp only [add_tmul, inner_add_left, map_add, h1, h2])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F G) in
/-- The linear isometry equivalence version of `TensorProduct.assoc`. -/
/-
**TensorProduct.assocIsometry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：assocIsometry : E otimes[𝕜] F otimes[𝕜] G ≃ₗᵢ[𝕜] E otimes[𝕜] (F otimes[𝕜] 
G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.inner_assoc_assoc`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Ty
pe u_3} {G : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : InnerProductSpac…

--- 原说明 ---
The linear isometry equivalence version of `TensorProduct.assoc`.
-/
noncomputable def assocIsometry : E ⊗[𝕜] F ⊗[𝕜] G ≃ₗᵢ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G) :=
  TensorProduct.assoc 𝕜 E F G |>.isometryOfInner inner_assoc_assoc
/-
**TensorProduct.assocIsometry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (x : TensorProduct 𝕜 (TensorProduct
 𝕜 E F) G),   (TensorProduct.assocIsometry 𝕜 E F G) x = (TensorProduct.assoc 𝕜 E
 F G) x
参数：x : TensorProduct 𝕜 (TensorProduct 𝕜 E F) G；TensorProduct.assocIsometry 𝕜 E F
 G；TensorProduct.assoc 𝕜 E F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma assocIsometry_apply (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    assocIsometry 𝕜 E F G x = TensorProduct.assoc 𝕜 E F G x := rfl
/-
**TensorProduct.assocIsometry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduc
t`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (x : TensorProduct 𝕜 E (TensorProdu
ct 𝕜 F G)),   (TensorProduct.assocIsometry 𝕜 E F G).symm x = (TensorProduct.asso
c 𝕜 E F G).symm x
参数：x : TensorProduct 𝕜 E (TensorProduct 𝕜 F G)；TensorProduct.assocIsometry 𝕜 E F
 G；TensorProduct.assoc 𝕜 E F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma assocIsometry_symm_apply (x : E ⊗[𝕜] (F ⊗[𝕜] G)) :
    (assocIsometry 𝕜 E F G).symm x = (TensorProduct.assoc 𝕜 E F G).symm x := rfl
/-
**TensorProduct.toLinearEquiv_assocIsometry** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G],   (TensorProduct.assocIsometry 𝕜 E
 F G).toLinearEquiv = TensorProduct.assoc 𝕜 E F G
参数：TensorProduct.assocIsometry 𝕜 E F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_assocIsometry :
    (assocIsometry 𝕜 E F G).toLinearEquiv = TensorProduct.assoc 𝕜 E F G := rfl
/-
**TensorProduct.norm_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (x : TensorProduct 𝕜 (TensorProduct
 𝕜 E F) G),   ‖(TensorProduct.assoc 𝕜 E F G) x‖ = ‖x‖
参数：x : TensorProduct 𝕜 (TensorProduct 𝕜 E F) G；TensorProduct.assoc 𝕜 E F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma norm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖ = ‖x‖ := assocIsometry 𝕜 E F G |>.norm_map x
/-
**TensorProduct.nnnorm_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (x : TensorProduct 𝕜 (TensorProduct
 𝕜 E F) G),   ‖(TensorProduct.assoc 𝕜 E F G) x‖₊ = ‖x‖₊
参数：x : TensorProduct 𝕜 (TensorProduct 𝕜 E F) G；TensorProduct.assoc 𝕜 E F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.nnnorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
@[simp] lemma nnnorm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖₊ = ‖x‖₊ := assocIsometry 𝕜 E F G |>.nnnorm_map x
/-
**TensorProduct.enorm_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (x : TensorProduct 𝕜 (TensorProduct
 𝕜 E F) G),   ‖(TensorProduct.assoc 𝕜 E F G) x‖ₑ = ‖x‖ₑ
参数：x : TensorProduct 𝕜 (TensorProduct 𝕜 E F) G；TensorProduct.assoc 𝕜 E F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.enorm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5
} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
@[simp] lemma enorm_assoc (x : E ⊗[𝕜] F ⊗[𝕜] G) :
    ‖TensorProduct.assoc 𝕜 E F G x‖ₑ = ‖x‖ₑ := assocIsometry 𝕜 E F G |>.toLinearIsometry.enorm_map x

end isometry

end TensorProduct

namespace ContinuousLinearMap

open TensorProduct

variable (G)

/-- `LinearMap.rTensor` as a continuous linear map, i.e. the continuous linear map `f` extended to
the map `x ⊗ₜ[𝕜] y ↦ f(x) ⊗ₜ[𝕜] y`. -/
/-
**ContinuousLinearMap.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：rTensor (f : E ->L[𝕜] F) : (E otimes[𝕜] G) ->L[𝕜] (F otimes[𝕜] G)
参数：f : E ->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.rTensor` as a continuous linear map, i.e. the continuous linear map `
f` extended to
the map `x ⊗ₜ[𝕜] y ↦ f(x) ⊗ₜ[𝕜] y`.
-/
noncomputable def rTensor (f : E →L[𝕜] F) : (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] G) :=
  (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x ↦ by
    /-
    Any tensor `x` can be written as a linear combination of pure tensors, `x = ∑ e n ⊗ₜ g n`. This
    induces three Gram matrices, one based on `e`, one on `f ∘ e` and one on `g`. Up to a constant,
    the `e`-based Gram matrix is larger than the `f ∘ e`-based one. This implies the existence of
    a matrix, whose form is used to show that `‖f‖ ^ 2 * ‖x‖ ^ 2 - ‖f x‖ ^ 2` is a sum of
    nonnegative terms.
    -/
    obtain ⟨n, e, g, hx⟩ := exists_sum_tmul_eq x
    obtain ⟨c, hc_supp, hc⟩ := Submodule.mem_span_set.mp
      ((span_tmul_eq_top 𝕜 E G) ▸ Submodule.mem_top (x := x))
    obtain ⟨m, A, hA⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp
      (Matrix.posSemidef_opNorm_smul_gram_sub_gram e f)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simp_rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, ← Matrix.ext_iff, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.gram_apply, Function.comp_apply] at hA
    simp_rw [mul_pow, hx, map_sum, LinearMap.rTensor_tmul, coe_coe,
      ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sum, sum_inner, inner_tmul, ← hA, sub_mul,
      Finset.sum_sub_distrib, map_sub, ← RCLike.smul_re, Finset.smul_sum, smul_mul_assoc,
      sub_le_self_iff, Matrix.sum_apply, mul_comm, Finset.mul_sum]
    simp_rw +singlePass [Finset.sum_comm_cycle, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
      ← mul_left_comm, ← mul_assoc, ← starRingEnd_self_apply (A _ _), ← inner_smul_left]
    simp [mul_comm, ← inner_smul_right, ← sum_inner, ← inner_sum, Finset.sum_nonneg]

variable {G} in
/-
**ContinuousLinearMap.rTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f : E →L[𝕜] F) (x : TensorProduct 
𝕜 E G),   (ContinuousLinearMap.rTensor G f) x = (LinearMap.rTensor G ↑f) x
参数：f : E →L[𝕜] F；x : TensorProduct 𝕜 E G；ContinuousLinearMap.rTensor G f；LinearM
ap.rTensor G ↑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rTensor_apply (f : E →L[𝕜] F) (x : E ⊗ G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

variable {G} in
/-
**ContinuousLinearMap.rTensor_tmul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：rTensor_tmul (f : E ->L[𝕜] F) (m : E) (n : G) : f.rTensor G (m otimesₜ n) 
= f m otimesₜ n
参数：f : E ->L[𝕜] F；m : E；n : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rTensor_tmul (f : E →L[𝕜] F) (m : E) (n : G) : f.rTensor G (m ⊗ₜ n) = f m ⊗ₜ n := rfl
/-
**ContinuousLinearMap.toLinearMap_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f : E →L[𝕜] F),   ↑(ContinuousLine
arMap.rTensor G f) = LinearMap.rTensor G ↑f
参数：G : Type u_4；f : E →L[𝕜] F；ContinuousLinearMap.rTensor G f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_rTensor (f : E →L[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl
/-
**ContinuousLinearMap._root_.LinearIsometry.toContinuousLinearMap_rTensor** 是 Ma
thlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometry.toContinuousLinearMap_rTensor (f : E →ₗᵢ[𝕜] F) :
    (f.rTensor G).toContinuousLinearMap = f.toContinuousLinearMap.rTensor G := rfl
/-
**ContinuousLinearMap.norm_rTensor_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：norm_rTensor_le (f : E ->L[𝕜] F) : ‖f.rTensor G‖ <= ‖f‖
参数：f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_rTensor_le (f : E →L[𝕜] F) : ‖f.rTensor G‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
/-
**ContinuousLinearMap.rTensor_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f₁ f₂ : E →L[𝕜] F),   ContinuousLi
nearMap.rTensor G (f₁ + f₂) = ContinuousLinearMap.rTensor G f₁ + ContinuousLinea
rMap.rTensor G f₂
参数：G : Type u_4；f₁ f₂ : E →L[𝕜] F；f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_add`：rTensor_add (f g : N ->ₗ[R] P) : (f + g).rTensor 
M = f.rTensor M + g.rTensor M
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_add (f₁ f₂ : E →L[𝕜] F) :
    (f₁ + f₂).rTensor G = f₁.rTensor G + f₂.rTensor G := by ext; simp
/-
**ContinuousLinearMap.rTensor_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (r : 𝕜) (f : E →L[𝕜] F),   Continuo
usLinearMap.rTensor G (r • f) = r • ContinuousLinearMap.rTensor G f
参数：G : Type u_4；r : 𝕜；f : E →L[𝕜] F；r • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_smul`：rTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).
rTensor M = r • f.rTensor M
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_smul (r : 𝕜) (f : E →L[𝕜] F) :
    (r • f).rTensor G = r • f.rTensor G := by ext; simp
/-
**ContinuousLinearMap.rTensor_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G],   ContinuousLinearMap.rTensor G (Con
tinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (TensorProduct 𝕜 E G)
参数：G : Type u_4；ContinuousLinearMap.id 𝕜 E；TensorProduct 𝕜 E G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_id`：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_id : (.id 𝕜 E : E →L[𝕜] E).rTensor G = .id 𝕜 _ := by ext; simp
/-
**ContinuousLinearMap.rTensor_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G],   ContinuousLinearMap.rTensor G 1 = 
1
参数：G : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.rTensor_id`：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Typ
e u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduc
tSpace 𝕜 E] [inst_3 …
-/
@[simp] lemma rTensor_one : (1 : E →L[𝕜] E).rTensor G = 1 := rTensor_id _
/-
**ContinuousLinearMap.rTensor_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G], ContinuousLinearMap.rTensor G 0 = 
0
参数：G : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_zero`：rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_zero : (0 : E →L[𝕜] F).rTensor G = 0 := by ext; simp
/-
**ContinuousLinearMap.rTensor_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f : E →L[𝕜] F),   ContinuousLinear
Map.rTensor G (-f) = -ContinuousLinearMap.rTensor G f
参数：G : Type u_4；f : E →L[𝕜] F；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_neg`：rTensor_neg (f : N ->ₗ[R] P) : (-f).rTensor Q = -
f.rTensor Q
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_neg (f : E →L[𝕜] F) : (-f).rTensor G = -f.rTensor G := by ext; simp
/-
**ContinuousLinearMap.rTensor_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f₁ f₂ : E →L[𝕜] F),   ContinuousLi
nearMap.rTensor G (f₁ - f₂) = ContinuousLinearMap.rTensor G f₁ - ContinuousLinea
rMap.rTensor G f₂
参数：G : Type u_4；f₁ f₂ : E →L[𝕜] F；f₁ - f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_sub`：rTensor_sub (f g : N ->ₗ[R] P) : (f - g).rTensor 
Q = f.rTensor Q - g.rTensor Q
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_sub (f₁ f₂ : E →L[𝕜] F) :
    (f₁ - f₂).rTensor G = f₁.rTensor G - f₂.rTensor G := by ext; simp
/-
**ContinuousLinearMap.rTensor_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：rTensor_comp (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E) : (f₁ ∘L f₂).rTensor G = 
f₁.rTensor G ∘L f₂.rTensor G
参数：f₁ : E ->L[𝕜] F；f₂ : H ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensor_comp (f₁ : E →L[𝕜] F) (f₂ : H →L[𝕜] E) :
    (f₁ ∘L f₂).rTensor G = f₁.rTensor G ∘L f₂.rTensor G := by ext; simp [LinearMap.rTensor_comp]
/-
**ContinuousLinearMap.rTensor_mul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：rTensor_mul (f₁ f₂ : E ->L[𝕜] E) : (f₁ * f₂).rTensor G = f₁.rTensor G * f₂
.rTensor G
参数：f₁ f₂ : E ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.rTensor_comp`：rTensor_comp (f₁ : E ->L[𝕜] F) (f₂ : H
 ->L[𝕜] E) : (f₁ ∘L f₂).rTensor G = f₁.rTensor G ∘L f₂.rTensor G
-/
lemma rTensor_mul (f₁ f₂ : E →L[𝕜] E) : (f₁ * f₂).rTensor G = f₁.rTensor G * f₂.rTensor G :=
  rTensor_comp _ _ _
/-
**ContinuousLinearMap.rTensor_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G] (f : E →L[𝕜] E)   (n : ℕ), Continuous
LinearMap.rTensor G (f ^ n) = ContinuousLinearMap.rTensor G f ^ n
参数：G : Type u_4；f : E →L[𝕜] E；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toLinearMap_pow`：toLinearMap_pow (f : M₁ ->L[R₁] M₁)
 (n : Nat) : (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n
· 使用定理 `LinearMap.rTensor_pow`：rTensor_pow (f : M ->ₗ[R] M) (n : Nat) : f.rTenso
r N ^ n = (f ^ n).rTensor N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rTensor_pow (f : E →L[𝕜] E) (n : ℕ) : (f ^ n).rTensor G = (f.rTensor G) ^ n := by
  simp [← coe_inj]

/-- `LinearMap.lTensor` as a continuous linear map, i.e. the continuous linear map `g` extended to
the map `x ⊗ₜ[𝕜] y ↦ x ⊗ₜ[𝕜] g(y)`. -/
/-
**ContinuousLinearMap.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：lTensor (g : E ->L[𝕜] F) : (G otimes[𝕜] E) ->L[𝕜] (G otimes[𝕜] F)
参数：g : E ->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.lTensor` as a continuous linear map, i.e. the continuous linear map `
g` extended to
the map `x ⊗ₜ[𝕜] y ↦ x ⊗ₜ[𝕜] g(y)`.
-/
noncomputable def lTensor (g : E →L[𝕜] F) : (G ⊗[𝕜] E) →L[𝕜] (G ⊗[𝕜] F) :=
  commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E

variable {G} in
/-
**ContinuousLinearMap.lTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {G : Type u_4} {H : Type u_5} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup G] [inst_4 : InnerProductSpace 𝕜 G]   [inst_5 : NormedAddC
ommGroup H] [inst_6 : InnerProductSpace 𝕜 H] (g : G →L[𝕜] H) (x : TensorProduct 
𝕜 E G),   (ContinuousLinearMap.lTensor E g) x = (LinearMap.lTensor E ↑g) x
参数：g : G →L[𝕜] H；x : TensorProduct 𝕜 E G；ContinuousLinearMap.lTensor E g；LinearM
ap.lTensor E ↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_apply (g : G →L[𝕜] H) (x : E ⊗ G) :
    g.lTensor E x = g.toLinearMap.lTensor E x := by
  simp [lTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]
/-
**ContinuousLinearMap.lTensor_tmul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：lTensor_tmul (g : E ->L[𝕜] F) (m : G) (n : E) : g.lTensor G (m otimesₜ n) 
= m otimesₜ g n
参数：g : E ->L[𝕜] F；m : G；n : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lTensor_tmul (g : E →L[𝕜] F) (m : G) (n : E) : g.lTensor G (m ⊗ₜ n) = m ⊗ₜ g n := rfl
/-
**ContinuousLinearMap.commIsometry_comp_lTensor_comp_commIsometry_eq** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：commIsometry_comp_lTensor_comp_commIsometry_eq (g : E ->L[𝕜] F) : commIsom
etry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E = g.lTensor G
参数：g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commIsometry_comp_lTensor_comp_commIsometry_eq (g : E →L[𝕜] F) :
    commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E = g.lTensor G :=
  rfl
/-
**ContinuousLinearMap.commIsometry_comp_rTensor_comp_commIsometry_eq** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：commIsometry_comp_rTensor_comp_commIsometry_eq (f : E ->L[𝕜] F) : commIsom
etry 𝕜 G F ∘L f.lTensor G ∘L commIsometry 𝕜 E G = f.rTensor G
参数：f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_comm`：∀ (R : Type u_1) [inst : CommSemiring R] (M : T
ype u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commIsometry_comp_rTensor_comp_commIsometry_eq (f : E →L[𝕜] F) :
    commIsometry 𝕜 G F ∘L f.lTensor G ∘L commIsometry 𝕜 E G = f.rTensor G := by
  ext; simp [lTensor]
/-
**ContinuousLinearMap.lTensor_comp_commIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：lTensor_comp_commIsometry (f : E ->L[𝕜] F) : f.lTensor G ∘L commIsometry 𝕜
 E G = commIsometry 𝕜 F G ∘L f.rTensor G
参数：f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_comm`：∀ (R : Type u_1) [inst : CommSemiring R] (M : T
ype u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lTensor_comp_commIsometry (f : E →L[𝕜] F) :
    f.lTensor G ∘L commIsometry 𝕜 E G = commIsometry 𝕜 F G ∘L f.rTensor G := by
  ext; simp [lTensor]
/-
**ContinuousLinearMap.rTensor_comp_commIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：rTensor_comp_commIsometry (g : E ->L[𝕜] F) : g.rTensor G ∘L commIsometry 𝕜
 G E = commIsometry 𝕜 G F ∘L g.lTensor G
参数：g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_comm`：∀ (R : Type u_1) [inst : CommSemiring R] (M : T
ype u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensor_comp_commIsometry (g : E →L[𝕜] F) :
    g.rTensor G ∘L commIsometry 𝕜 G E = commIsometry 𝕜 G F ∘L g.lTensor G := by
  ext; simp [lTensor]
/-
**ContinuousLinearMap.toLinearMap_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (g : E →L[𝕜] F),   ↑(ContinuousLine
arMap.lTensor G g) = LinearMap.lTensor G ↑g
参数：G : Type u_4；g : E →L[𝕜] F；ContinuousLinearMap.lTensor G g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toLinearMap_lTensor (g : E →L[𝕜] F) :
    (g.lTensor G).toLinearMap = g.toLinearMap.lTensor G := by ext; simp
/-
**ContinuousLinearMap._root_.LinearIsometry.toContinuousLinearMap_lTensor** 是 Ma
thlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearIsometry.toContinuousLinearMap_lTensor (g : E →ₗᵢ[𝕜] F) :
    (g.lTensor G).toContinuousLinearMap = g.toContinuousLinearMap.lTensor G := by ext; simp
/-
**ContinuousLinearMap.norm_lTensor_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：norm_lTensor_le (g : E ->L[𝕜] F) : ‖g.lTensor G‖ <= ‖g‖
参数：g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap_le`：norm_toContinuousLinearMap
_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ <= 1
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousLinearMap.norm_rTensor_le`：norm_rTensor_le (f : E ->L[𝕜] F) : 
‖f.rTensor G‖ <= ‖f‖
-/
theorem norm_lTensor_le (g : E →L[𝕜] F) : ‖g.lTensor G‖ ≤ ‖g‖ := by
  simp_rw [lTensor, ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [opNorm_comp_le, opNorm_comp_le, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le, mul_one, one_mul, norm_rTensor_le]
/-
**ContinuousLinearMap.lTensor_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f₁ f₂ : E →L[𝕜] F),   ContinuousLi
nearMap.lTensor G (f₁ + f₂) = ContinuousLinearMap.lTensor G f₁ + ContinuousLinea
rMap.lTensor G f₂
参数：G : Type u_4；f₁ f₂ : E →L[𝕜] F；f₁ + f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_add`：lTensor_add (f g : N ->ₗ[R] P) : (f + g).lTensor 
M = f.lTensor M + g.lTensor M
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_add (f₁ f₂ : E →L[𝕜] F) :
    (f₁ + f₂).lTensor G = f₁.lTensor G + f₂.lTensor G := by ext; simp
/-
**ContinuousLinearMap.lTensor_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (r : 𝕜) (f : E →L[𝕜] F),   Continuo
usLinearMap.lTensor G (r • f) = r • ContinuousLinearMap.lTensor G f
参数：G : Type u_4；r : 𝕜；f : E →L[𝕜] F；r • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_smul`：lTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).
lTensor M = r • f.lTensor M
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_smul (r : 𝕜) (f : E →L[𝕜] F) : (r • f).lTensor G = r • f.lTensor G := by
  ext; simp
/-
**ContinuousLinearMap.lTensor_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G],   ContinuousLinearMap.lTensor G (Con
tinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (TensorProduct 𝕜 G E)
参数：G : Type u_4；ContinuousLinearMap.id 𝕜 E；TensorProduct 𝕜 G E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_id : (.id 𝕜 E : E →L[𝕜] E).lTensor G = .id 𝕜 _ := by ext; simp
/-
**ContinuousLinearMap.lTensor_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G],   ContinuousLinearMap.lTensor G 1 = 
1
参数：G : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.lTensor_id`：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Typ
e u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduc
tSpace 𝕜 E] [inst_3 …
-/
@[simp] lemma lTensor_one : (1 : E →L[𝕜] E).lTensor G = 1 := lTensor_id _
/-
**ContinuousLinearMap.lTensor_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G], ContinuousLinearMap.lTensor G 0 = 
0
参数：G : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_zero : (0 : E →L[𝕜] F).lTensor G = 0 := by ext; simp
/-
**ContinuousLinearMap.lTensor_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f : E →L[𝕜] F),   ContinuousLinear
Map.lTensor G (-f) = -ContinuousLinearMap.lTensor G f
参数：G : Type u_4；f : E →L[𝕜] F；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_neg`：lTensor_neg (f : N ->ₗ[R] P) : (-f).lTensor M = -
f.lTensor M
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_neg (f : E →L[𝕜] F) : (-f).lTensor G = -f.lTensor G := by ext; simp
/-
**ContinuousLinearMap.lTensor_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} (G : Type u_4) [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3
 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : NormedAddC
ommGroup G] [inst_6 : InnerProductSpace 𝕜 G] (f₁ f₂ : E →L[𝕜] F),   ContinuousLi
nearMap.lTensor G (f₁ - f₂) = ContinuousLinearMap.lTensor G f₁ - ContinuousLinea
rMap.lTensor G f₂
参数：G : Type u_4；f₁ f₂ : E →L[𝕜] F；f₁ - f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_sub`：lTensor_sub (f g : N ->ₗ[R] P) : (f - g).lTensor 
M = f.lTensor M - g.lTensor M
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_sub (f₁ f₂ : E →L[𝕜] F) :
    (f₁ - f₂).lTensor G = f₁.lTensor G - f₂.lTensor G := by ext; simp
/-
**ContinuousLinearMap.lTensor_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：lTensor_comp (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E) : (f₁ ∘L f₂).lTensor G = 
f₁.lTensor G ∘L f₂.lTensor G
参数：f₁ : E ->L[𝕜] F；f₂ : H ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensor_comp (f₁ : E →L[𝕜] F) (f₂ : H →L[𝕜] E) :
    (f₁ ∘L f₂).lTensor G = f₁.lTensor G ∘L f₂.lTensor G := by ext; simp [LinearMap.lTensor_comp]
/-
**ContinuousLinearMap.lTensor_mul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：lTensor_mul (f₁ f₂ : E ->L[𝕜] E) : (f₁ * f₂).lTensor G = f₁.lTensor G * f₂
.lTensor G
参数：f₁ f₂ : E ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.lTensor_comp`：lTensor_comp (f₁ : E ->L[𝕜] F) (f₂ : H
 ->L[𝕜] E) : (f₁ ∘L f₂).lTensor G = f₁.lTensor G ∘L f₂.lTensor G
-/
lemma lTensor_mul (f₁ f₂ : E →L[𝕜] E) : (f₁ * f₂).lTensor G = f₁.lTensor G * f₂.lTensor G :=
  lTensor_comp _ _ _
/-
**ContinuousLinearMap.lTensor_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G] (f : E →L[𝕜] E)   (n : ℕ), Continuous
LinearMap.lTensor G (f ^ n) = ContinuousLinearMap.lTensor G f ^ n
参数：G : Type u_4；f : E →L[𝕜] E；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toLinearMap_lTensor`：∀ {𝕜 : Type u_1} {E : Type u_2}
 {F : Type u_3} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
   [inst_2 : InnerProductSpac…
· 使用定理 `ContinuousLinearMap.toLinearMap_pow`：toLinearMap_pow (f : M₁ ->L[R₁] M₁)
 (n : Nat) : (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_pow`：lTensor_pow (f : N ->ₗ[R] N) (n : Nat) : f.lTenso
r M ^ n = (f ^ n).lTensor M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lTensor_pow (f : E →L[𝕜] E) (n : ℕ) : (f ^ n).lTensor G = (f.lTensor G) ^ n := by
  simp [← coe_inj]

end ContinuousLinearMap

namespace TensorProduct

/-- `TensorProduct.map` as a continuous linear map, i.e. the continuous linear map
`x ⊗ₜ[𝕜] y ↦ f(x) ⊗ₜ[𝕜] g(y)` formed from the continuous linear maps `f` and `g`. -/
/-
**TensorProduct.mapL** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mapL (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : (E otimes[𝕜] G) ->L[𝕜] (F otimes[
𝕜] H)
参数：f : E ->L[𝕜] F；g : G ->L[𝕜] H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TensorProduct.map` as a continuous linear map, i.e. the continuous linear map
`x ⊗ₜ[𝕜] y ↦ f(x) ⊗ₜ[𝕜] g(y)` formed from the continuous linear maps `f` and `g`
.
-/
noncomputable def mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) : (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] H) :=
  f.rTensor H ∘L g.lTensor E
/-
**TensorProduct.norm_mapL_le** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：norm_mapL_le (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : ‖mapL f g‖ <= ‖f‖ * ‖g‖
参数：f : E ->L[𝕜] F；g : G ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
{G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E
] [inst_2 : I…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.norm_rTensor_le`：norm_rTensor_le (f : E ->L[𝕜] F) : 
‖f.rTensor G‖ <= ‖f‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ContinuousLinearMap.norm_lTensor_le`：norm_lTensor_le (g : E ->L[𝕜] F) : 
‖g.lTensor G‖ <= ‖g‖
-/
theorem norm_mapL_le (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ := by
  grw [mapL, ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.norm_rTensor_le,
    ContinuousLinearMap.norm_lTensor_le]
/-
**TensorProduct.mapL_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H)  
 (x : TensorProduct 𝕜 E G), (TensorProduct.mapL f g) x = (TensorProduct.map ↑f ↑
g) x
参数：f : E →L[𝕜] F；g : G →L[𝕜] H；x : TensorProduct 𝕜 E G；TensorProduct.mapL f g；Te
nsorProduct.map ↑f ↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.lTensor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : 
Type u_4} {H : Type u_5} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [in
st_2 : InnerProductSpac…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapL_apply (f : E →L[𝕜] F) (g : G →L[𝕜] H) (x) :
    mapL f g x = map f.toLinearMap g.toLinearMap x := by
  simp [mapL, ← LinearMap.rTensor_comp_lTensor]
/-
**TensorProduct.mapL_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_tmul (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (m : E) (n : G) : mapL f g (m 
otimesₜ n) = f m otimesₜ g n
参数：f : E ->L[𝕜] F；g : G ->L[𝕜] H；m : E；n : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapL_tmul (f : E →L[𝕜] F) (g : G →L[𝕜] H) (m : E) (n : G) :
    mapL f g (m ⊗ₜ n) = f m ⊗ₜ g n := rfl
/-
**TensorProduct.mapL_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →L[𝕜] F), TensorProduct.ma
pL 0 f = 0
参数：f : E →L[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.rTensor_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpac…
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapL_zero_left (f : E →L[𝕜] F) : mapL (0 : G →L[𝕜] H) f = 0 := by simp [mapL]
/-
**TensorProduct.mapL_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →L[𝕜] F), TensorProduct.ma
pL f 0 = 0
参数：f : E →L[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.lTensor_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} (G : Type u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpac…
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapL_zero_right (f : E →L[𝕜] F) : mapL f (0 : G →L[𝕜] H) = 0 := by simp [mapL]
/-
**TensorProduct.mapL_id_id** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {G : Type u_4} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup G] [inst_4 : InnerProductSpace 𝕜 G],   TensorProduct.mapL (ContinuousLine
arMap.id 𝕜 E) (ContinuousLinearMap.id 𝕜 G) =     ContinuousLinearMap.id 𝕜 (Tenso
rProduct 𝕜 E G)
参数：ContinuousLinearMap.id 𝕜 E；ContinuousLinearMap.id 𝕜 G；TensorProduct 𝕜 E G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.rTensor_id`：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Typ
e u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduc
tSpace 𝕜 E] [inst_3 …
· 使用定理 `ContinuousLinearMap.lTensor_id`：∀ {𝕜 : Type u_1} {E : Type u_2} (G : Typ
e u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduc
tSpace 𝕜 E] [inst_3 …
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapL_id_id : mapL (.id 𝕜 E) (.id 𝕜 G) = .id 𝕜 _ := by simp [mapL]
/-
**TensorProduct.mapL_comp_commIsometry** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`
。
形式化陈述：mapL_comp_commIsometry (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : mapL f g ∘L com
mIsometry 𝕜 G E = commIsometry 𝕜 H F ∘L mapL g f
参数：f : E ->L[𝕜] F；g : G ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用引理 `TensorProduct.map_comm`：map_comm (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N
₂) (x : N otimes[R] M) : map f g (TensorProduct.comm R N M x) = TensorProduct.co
mm R₂ N₂ M₂ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapL_comp_commIsometry (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f g ∘L commIsometry 𝕜 G E = commIsometry 𝕜 H F ∘L mapL g f := by ext; simp [map_comm]
/-
**TensorProduct.mapL_add_left** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_add_left (f₁ f₂ : E ->L[𝕜] F) (g : G ->L[𝕜] H) : mapL (f₁ + f₂) g = m
apL f₁ g + mapL f₂ g
参数：f₁ f₂ : E ->L[𝕜] F；g : G ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_add_left`：map_add_left (f₁ f₂ : M ->ₛₗ[σ₁₂] M₂) (g : N
 ->ₛₗ[σ₁₂] N₂) : map (f₁ + f₂) g = map f₁ g + map f₂ g
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapL_add_left (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (f₁ + f₂) g = mapL f₁ g + mapL f₂ g := by ext; simp [map_add_left]
/-
**TensorProduct.mapL_add_right** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_add_right (f : E ->L[𝕜] F) (g₁ g₂ : G ->L[𝕜] H) : mapL f (g₁ + g₂) = 
mapL f g₁ + mapL f g₂
参数：f : E ->L[𝕜] F；g₁ g₂ : G ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_add_right`：map_add_right (f : M ->ₛₗ[σ₁₂] M₂) (g₁ g₂ :
 N ->ₛₗ[σ₁₂] N₂) : map f (g₁ + g₂) = map f g₁ + map f g₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapL_add_right (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    mapL f (g₁ + g₂) = mapL f g₁ + mapL f g₂ := by ext; simp [map_add_right]
/-
**TensorProduct.mapL_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_smul_left (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : mapL (r • f) g 
= r • mapL f g
参数：r : 𝕜；f : E ->L[𝕜] F；g : G ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_smul_left`：map_smul_left (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂)
 (g : N ->ₛₗ[σ₁₂] N₂) : map (r • f) g = r • map f g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapL_smul_left (r : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL (r • f) g = r • mapL f g := by ext; simp [map_smul_left]
/-
**TensorProduct.mapL_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_smul_right (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : mapL f (r • g)
 = r • mapL f g
参数：r : 𝕜；f : E ->L[𝕜] F；g : G ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_smul_right`：map_smul_right (r : R₂) (f : M ->ₛₗ[σ₁₂] M
₂) (g : N ->ₛₗ[σ₁₂] N₂) : map f (r • g) = r • map f g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapL_smul_right (r : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapL f (r • g) = r • mapL f g := by ext; simp [map_smul_right]
/-
**TensorProduct.toLinearMap_mapL** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H), 
  ↑(TensorProduct.mapL f g) = TensorProduct.map ↑f ↑g
参数：f : E →L[𝕜] F；g : G →L[𝕜] H；TensorProduct.mapL f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toLinearMap_mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapL f g).toLinearMap = map f g := by ext; simp
/-
**TensorProduct.toContinuousLinearMap_mapIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Ten
sorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] (f : E →ₗᵢ[𝕜] F) (g : G →ₗᵢ[𝕜] H)
,   (TensorProduct.mapIsometry f g).toContinuousLinearMap =     TensorProduct.ma
pL f.toContinuousLinearMap g.toContinuousLinearMap
参数：f : E →ₗᵢ[𝕜] F；g : G →ₗᵢ[𝕜] H；TensorProduct.mapIsometry f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toContinuousLinearMap_mapIsometry (f : E →ₗᵢ[𝕜] F) (g : G →ₗᵢ[𝕜] H) :
    (mapIsometry f g).toContinuousLinearMap =
      mapL f.toContinuousLinearMap g.toContinuousLinearMap := by
  ext; simp

section comp

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B]

/-
**TensorProduct.mapL_comp** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_comp (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E) (g₁ : G ->L[𝕜] H) (g₂ : B ->
L[𝕜] G) : mapL (f₁ ∘L f₂) (g₁ ∘L g₂) = mapL f₁ g₁ ∘L mapL f₂ g₂
参数：f₁ : E ->L[𝕜] F；f₂ : A ->L[𝕜] E；g₁ : G ->L[𝕜] H；g₂ : B ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapL_comp (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E) (g₁ : G →L[𝕜] H) (g₂ : B →L[𝕜] G) :
    mapL (f₁ ∘L f₂) (g₁ ∘L g₂) = mapL f₁ g₁ ∘L mapL f₂ g₂ := by ext; simp [map_map]
/-
**TensorProduct.mapL_mul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：mapL_mul (f₁ f₂ : E ->L[𝕜] E) (g₁ g₂ : F ->L[𝕜] F) : mapL (f₁ * f₂) (g₁ * 
g₂) = mapL f₁ g₁ * mapL f₂ g₂
参数：f₁ f₂ : E ->L[𝕜] E；g₁ g₂ : F ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.mapL_comp`：mapL_comp (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E) (
g₁ : G ->L[𝕜] H) (g₂ : B ->L[𝕜] G) : mapL (f₁ ∘L f₂) (g₁ ∘L g₂) = mapL f₁ g₁ ∘L 
mapL f₂ g₂
-/
lemma mapL_mul (f₁ f₂ : E →L[𝕜] E) (g₁ g₂ : F →L[𝕜] F) :
    mapL (f₁ * f₂) (g₁ * g₂) = mapL f₁ g₁ * mapL f₂ g₂ := mapL_comp _ _ _ _
/-
**TensorProduct.mapL_pow** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (f : E →L[𝕜] E)   (g : F →L[𝕜] F) (n 
: ℕ), TensorProduct.mapL f g ^ n = TensorProduct.mapL (f ^ n) (g ^ n)
参数：f : E →L[𝕜] E；g : F →L[𝕜] F；n : ℕ；f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toLinearMap_pow`：toLinearMap_pow (f : M₁ ->L[R₁] M₁)
 (n : Nat) : (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.toLinearMap_mapL`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddComm
Group E] [inst_2 : I…
· 使用定理 `TensorProduct.map_pow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Typ
e u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [i
nst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapL_pow (f : E →L[𝕜] E) (g : F →L[𝕜] F) (n : ℕ) :
    (mapL f g) ^ n = mapL (f ^ n) (g ^ n) := by simp [← ContinuousLinearMap.coe_inj]
/-
**TensorProduct._root_.ContinuousLinearMap.mapL_comp_rTensor** 是 Mathlib 中的一个引理，
位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearMap.mapL_comp_rTensor (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E)
    (g : G →L[𝕜] H) : mapL f₁ g ∘L f₂.rTensor G = mapL (f₁ ∘L f₂) g := by ext; simp
/-
**TensorProduct._root_.ContinuousLinearMap.mapL_comp_lTensor** 是 Mathlib 中的一个引理，
位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearMap.mapL_comp_lTensor (f : E →L[𝕜] F) (g₁ : G →L[𝕜] H)
    (g₂ : A →L[𝕜] G) : mapL f g₁ ∘L g₂.lTensor E = mapL f (g₁ ∘L g₂) := by ext; simp
/-
**TensorProduct._root_.ContinuousLinearMap.rTensor_comp_mapL** 是 Mathlib 中的一个引理，
位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearMap.rTensor_comp_mapL (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E)
    (g : G →L[𝕜] H) : f₁.rTensor H ∘L mapL f₂ g = mapL (f₁ ∘L f₂) g := by ext; simp
/-
**TensorProduct._root_.ContinuousLinearMap.lTensor_comp_mapL** 是 Mathlib 中的一个引理，
位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearMap.lTensor_comp_mapL (f : E →L[𝕜] F) (g₁ : G →L[𝕜] H)
    (g₂ : A →L[𝕜] G) : g₁.lTensor F ∘L mapL f g₂ = mapL f (g₁ ∘L g₂) := by ext; simp

end comp

variable (G) in
/-
**TensorProduct._root_.ContinuousLinearMap.rTensor_eq_mapL** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.rTensor_eq_mapL (f : E →L[𝕜] F) :
    f.rTensor G = mapL f (.id 𝕜 G) := by simp [mapL]

variable (E) in
/-
**TensorProduct._root_.ContinuousLinearMap.lTensor_eq_mapL** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.lTensor_eq_mapL (g : G →L[𝕜] H) :
    g.lTensor E = mapL (.id 𝕜 E) g := by simp [mapL]
/-
**TensorProduct._root_.ContinuousLinearMap.lTensor_comp_rTensor** 是 Mathlib 中的一个
引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearMap.lTensor_comp_rTensor (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    f.lTensor H ∘L g.rTensor E = mapL g f := by ext; simp [← LinearMap.lTensor_comp_rTensor]
/-
**TensorProduct._root_.ContinuousLinearMap.rTensor_comp_lTensor** 是 Mathlib 中的一个
引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousLinearMap.rTensor_comp_lTensor (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    f.rTensor H ∘L g.lTensor E = mapL f g := rfl
/-
**TensorProduct.adjoint_mapL** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace E]   [ins
t_10 : CompleteSpace G] [inst_11 : CompleteSpace (TensorProduct 𝕜 E G)] [inst_12
 : CompleteSpace F]   [inst_13 : CompleteSpace H] [inst_14 : CompleteSpace (Tens
orProduct 𝕜 F H)] (f : E →L[𝕜] F) (g : G →L[𝕜] H),   ContinuousLinearMap.adjoint
 (TensorProduct.mapL f g) =     TensorProduct.mapL (ContinuousLinearMap.adjoint 
f) (ContinuousLinearMap.adjoint g)
参数：TensorProduct 𝕜 E G；TensorProduct 𝕜 F H；f : E →L[𝕜] F；g : G →L[𝕜] H；TensorPro
duct.mapL f g；ContinuousLinearMap.adjoint f；ContinuousLinearMap.adjoint g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.toLinearMap_mapL`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddComm
Group E] [inst_2 : I…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `TensorProduct.mapL_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 {G : Type u_4} {H : Type u_5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup 
E] [inst_2 : I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem adjoint_mapL [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E ⊗[𝕜] G)]
    [CompleteSpace F] [CompleteSpace H] [CompleteSpace (F ⊗[𝕜] H)]
    (f : E →L[𝕜] F) (g : G →L[𝕜] H) : (mapL f g).adjoint = mapL f.adjoint g.adjoint := by
  apply ContinuousLinearMap.coe_inj.mp <| ext' ?_
  simp [TensorProduct.ext_iff_inner_right, ContinuousLinearMap.adjoint_inner_left]

set_option backward.isDefEq.respectTransparency.types false in
variable (G) in
/-
**TensorProduct._root_.ContinuousLinearMap.adjoint_rTensor** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.ContinuousLinearMap.adjoint_rTensor [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] [CompleteSpace (F ⊗[𝕜] G)] [CompleteSpace F] (f : E →L[𝕜] F) :
    (f.rTensor G).adjoint = f.adjoint.rTensor G := by simp [ContinuousLinearMap.rTensor_eq_mapL]

set_option backward.isDefEq.respectTransparency.types false in
variable (E) in
/-
**TensorProduct._root_.ContinuousLinearMap.adjoint_lTensor** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.ContinuousLinearMap.adjoint_lTensor [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] H)] [CompleteSpace (E ⊗[𝕜] G)] [CompleteSpace H] (g : G →L[𝕜] H) :
    (g.lTensor E).adjoint = g.adjoint.lTensor E := by simp [ContinuousLinearMap.lTensor_eq_mapL]

open LinearMap
/-
**TensorProduct.adjoint_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {H : Type u_
5} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 : NormedAddCommGroup F]   [inst_4 : InnerProductSpace 𝕜 F] [inst
_5 : NormedAddCommGroup G] [inst_6 : InnerProductSpace 𝕜 G]   [inst_7 : NormedAd
dCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : FiniteDimensional 𝕜 E] 
  [inst_10 : FiniteDimensional 𝕜 F] [inst_11 : FiniteDimensional 𝕜 G] [inst_12 :
 FiniteDimensional 𝕜 H] (f : E →ₗ[𝕜] F)   (g : G →ₗ[𝕜] H),   LinearMap.adjoint (
TensorProduct.map f g) = TensorProduct.map (LinearMap.adjoint f) (LinearMap.adjo
int g)
参数：f : E →ₗ[𝕜] F；g : G →ₗ[𝕜] H；TensorProduct.map f g；LinearMap.adjoint f；LinearM
ap.adjoint g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem adjoint_map [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E →ₗ[𝕜] F) (g : G →ₗ[𝕜] H) :
    (map f g).adjoint = map f.adjoint g.adjoint :=
  ext' fun _ _ => by simp [TensorProduct.ext_iff_inner_right, adjoint_inner_left]
/-
**TensorProduct._root_.LinearMap.adjoint_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.LinearMap.adjoint_rTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E →ₗ[𝕜] F) :
    (f.rTensor G).adjoint = f.adjoint.rTensor G := by simp [rTensor]
/-
**TensorProduct._root_.LinearMap.adjoint_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.LinearMap.adjoint_lTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E →ₗ[𝕜] F) :
    (f.lTensor G).adjoint = f.adjoint.lTensor G := by simp [lTensor]

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪x, a ⊗ₜ (b ⊗ₜ c)⟫ = ⟪y, a ⊗ₜ (b ⊗ₜ c)⟫` for all
`a, b, c`.

See also `ext_iff_inner_right_threefold` for when `x, y : E ⊗ F ⊗ G`. -/
/-
**TensorProduct.ext_iff_inner_right_threefold'** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product`。
形式化陈述：ext_iff_inner_right_threefold' {x y : E otimes[𝕜] (F otimes[𝕜] G)} : x = y
 ↔ forall a b c, inner 𝕜 x (a otimesₜ[𝕜] (b otimesₜ[𝕜] c)) = inner 𝕜 y (a otimes
ₜ[𝕜] (b otimesₜ[𝕜] c))
参数：F otimes[𝕜] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearIsometryEquiv.inner_map_eq_flip`：LinearIsometryEquiv.inner_map_eq_
flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') : ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪x, a ⊗ₜ (b ⊗ₜ c)⟫ = ⟪y, a ⊗ₜ (b ⊗ₜ c)⟫
` for all
`a, b, c`.

See also `ext_iff_inner_right_threefold` for when `x, y : E ⊗ F ⊗ G`.
-/
theorem ext_iff_inner_right_threefold' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 x (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) = inner 𝕜 y (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) := by
  simp only [← (assocIsometry 𝕜 E F G).symm.injective.eq_iff,
    ext_iff_inner_right_threefold, LinearIsometryEquiv.inner_map_eq_flip]
  simp

/-- Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪a ⊗ₜ (b ⊗ₜ c), x⟫ = ⟪a ⊗ₜ (b ⊗ₜ c), y⟫` for all
`a, b, c`.

See also `ext_iff_inner_left_threefold` for when `x, y : E ⊗ F ⊗ G`. -/
/-
**TensorProduct.ext_iff_inner_left_threefold'** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct`。
形式化陈述：ext_iff_inner_left_threefold' {x y : E otimes[𝕜] (F otimes[𝕜] G)} : x = y 
↔ forall a b c, inner 𝕜 (a otimesₜ[𝕜] (b otimesₜ[𝕜] c)) x = inner 𝕜 (a otimesₜ[𝕜
] (b otimesₜ[𝕜] c)) y
参数：F otimes[𝕜] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `TensorProduct.ext_iff_inner_right_threefold'`：ext_iff_inner_right_threef
old' {x y : E otimes[𝕜] (F otimes[𝕜] G)} : x = y ↔ forall a b c, inner 𝕜 x (a ot
imesₜ[𝕜] (b otimesₜ[𝕜] c)) = inner…

--- 原说明 ---
Given `x, y : E ⊗ (F ⊗ G)`, `x = y` iff `⟪a ⊗ₜ (b ⊗ₜ c), x⟫ = ⟪a ⊗ₜ (b ⊗ₜ c), y⟫
` for all
`a, b, c`.

See also `ext_iff_inner_left_threefold` for when `x, y : E ⊗ F ⊗ G`.
-/
theorem ext_iff_inner_left_threefold' {x y : E ⊗[𝕜] (F ⊗[𝕜] G)} :
    x = y ↔ ∀ a b c, inner 𝕜 (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) x = inner 𝕜 (a ⊗ₜ[𝕜] (b ⊗ₜ[𝕜] c)) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold' (x := x) (y := y)

end TensorProduct

section orthonormal
variable {ι₁ ι₂ : Type*}

open Module

/-- The tensor product of two orthonormal vectors is orthonormal. -/
/-
**Orthonormal.tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.tmul {b₁ : ι₁ -> E} {b₂ : ι₂ -> F} (hb₁ : Orthonormal 𝕜 b₁) (h
b₂ : Orthonormal 𝕜 b₂) : Orthonormal 𝕜 fun i : ι₁ × ι₂ => b₁ i.1 otimesₜ[𝕜] b₂ i
.2
参数：hb₁ : Orthonormal 𝕜 b₁；hb₂ : Orthonormal 𝕜 b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The tensor product of two orthonormal vectors is orthonormal.
-/
theorem Orthonormal.tmul
    {b₁ : ι₁ → E} {b₂ : ι₂ → F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ ↦ b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

/-- The tensor product of two orthonormal bases is orthonormal. -/
/-
**Orthonormal.basisTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.basisTensorProduct {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb
₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) : Orthonormal 𝕜 (b₁.tensorProduct
 b₂)
参数：hb₁ : Orthonormal 𝕜 b₁；hb₂ : Orthonormal 𝕜 b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.tensorProduct_apply'`：tensorProduct_apply' (b : Basis ι S M
) (c : Basis κ R N) (i : ι × κ) : tensorProduct b c i = b i.1 otimesₜ c i.2
· 使用定理 `Orthonormal.tmul`：Orthonormal.tmul {b₁ : ι₁ -> E} {b₂ : ι₂ -> F} (hb₁ : 
Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) : Orthonormal 𝕜 fun i : ι₁ × ι₂ => b₁
 i.1 o…

--- 原说明 ---
The tensor product of two orthonormal bases is orthonormal.
-/
theorem Orthonormal.basisTensorProduct
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := by
  convert! hb₁.tmul hb₂
  exact b₁.tensorProduct_apply' b₂ _

namespace OrthonormalBasis
variable [Fintype ι₁] [Fintype ι₂]

/-- The orthonormal basis of the tensor product of two orthonormal bases. -/
/-
**OrthonormalBasis.tensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : RCL
ike 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             [inst_3 : NormedAddCommGroup F] →               [ins
t_4 : InnerProductSpace 𝕜 F] →                 {ι₁ : Type u_6} →                
   {ι₂ : Type u_7} →                     [inst_5 : Fintype ι₁] →                
       [inst_6 : Fintype ι₂] →                         OrthonormalBasis ι₁ 𝕜 E →
                           OrthonormalBasis ι₂ 𝕜 F → OrthonormalBasis (ι₁ × ι₂) 
𝕜 (TensorProduct 𝕜 E F)
参数：ι₁ × ι₂；TensorProduct 𝕜 E F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthonormal basis of the tensor product of two orthonormal bases.
-/
protected noncomputable def tensorProduct
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ × ι₂) 𝕜 (E ⊗[𝕜] F) :=
  (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (b₁.orthonormal.basisTensorProduct b₂.orthonormal)

@[simp]
/-
**OrthonormalBasis.tensorProduct_apply** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBas
is`。
形式化陈述：tensorProduct_apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis 
ι₂ 𝕜 F) (i : ι₁) (j : ι₂) : b₁.tensorProduct b₂ (i, j) = b₁ i otimesₜ[𝕜] b₂ j
参数：b₁ : OrthonormalBasis ι₁ 𝕜 E；b₂ : OrthonormalBasis ι₂ 𝕜 F；i : ι₁；j : ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [in
st : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.tensorProduct_apply`：tensorProduct_apply (b : Basis ι S M) 
(c : Basis κ R N) (i : ι) (j : κ) : tensorProduct b c (i, j) = b i otimesₜ c j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorProduct_apply
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) :
    b₁.tensorProduct b₂ (i, j) = b₁ i ⊗ₜ[𝕜] b₂ j := by simp [OrthonormalBasis.tensorProduct]
/-
**OrthonormalBasis.tensorProduct_apply'** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBa
sis`。
形式化陈述：tensorProduct_apply' (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis
 ι₂ 𝕜 F) (i : ι₁ × ι₂) : b₁.tensorProduct b₂ i = b₁ i.1 otimesₜ[𝕜] b₂ i.2
参数：b₁ : OrthonormalBasis ι₁ 𝕜 E；b₂ : OrthonormalBasis ι₂ 𝕜 F；i : ι₁ × ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrthonormalBasis.tensorProduct_apply`：tensorProduct_apply (b₁ : Orthonor
malBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) : b₁.tensorPro
duct b₂ (i, j) = b₁ i otim…
-/
lemma tensorProduct_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁ × ι₂) :
    b₁.tensorProduct b₂ i = b₁ i.1 ⊗ₜ[𝕜] b₂ i.2 := tensorProduct_apply _ _ _ _

@[simp]
/-
**OrthonormalBasis.tensorProduct_repr_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Orth
onormalBasis`。
形式化陈述：tensorProduct_repr_tmul_apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : Orthono
rmalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁) (j : ι₂) : (b₁.tensorProduct b₂).repr
 (x otimesₜ[𝕜] y) (i, j) = b₂.repr y j * b₁.repr x i
参数：b₁ : OrthonormalBasis ι₁ 𝕜 E；b₂ : OrthonormalBasis ι₂ 𝕜 F；x : E；y : F；i : ι₁；
j : ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Module.Basis.tensorProduct_repr_tmul_apply`：tensorProduct_repr_tmul_appl
y (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N) (i : ι) (j : κ) : (tensorP
roduct b c).repr (m otimesₜ n) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorProduct_repr_tmul_apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
    (x : E) (y : F) (i : ι₁) (j : ι₂) :
    (b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y) (i, j) = b₂.repr y j * b₁.repr x i := by
  simp [OrthonormalBasis.tensorProduct]
/-
**OrthonormalBasis.tensorProduct_repr_tmul_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Ort
honormalBasis`。
形式化陈述：tensorProduct_repr_tmul_apply' (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : Orthon
ormalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁ × ι₂) : (b₁.tensorProduct b₂).repr (x
 otimesₜ[𝕜] y) i = b₂.repr y i.2 * b₁.repr x i.1
参数：b₁ : OrthonormalBasis ι₁ 𝕜 E；b₂ : OrthonormalBasis ι₂ 𝕜 F；x : E；y : F；i : ι₁ 
× ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrthonormalBasis.tensorProduct_repr_tmul_apply`：tensorProduct_repr_tmul_
apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E) (y :
 F) (i : ι₁) (j : ι₂) : (b₁.tensorPr…
-/
lemma tensorProduct_repr_tmul_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁ × ι₂) :
    (b₁.tensorProduct b₂).repr (x ⊗ₜ[𝕜] y) i = b₂.repr y i.2 * b₁.repr x i.1 :=
  tensorProduct_repr_tmul_apply _ _ _ _ _ _

@[simp]
/-
**OrthonormalBasis.toBasis_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalB
asis`。
形式化陈述：toBasis_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasi
s ι₂ 𝕜 F) : (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis
参数：b₁ : OrthonormalBasis ι₁ 𝕜 E；b₂ : OrthonormalBasis ι₂ 𝕜 F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toBasis_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toBasis_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis := by
  simp [OrthonormalBasis.tensorProduct]

end OrthonormalBasis
end orthonormal

