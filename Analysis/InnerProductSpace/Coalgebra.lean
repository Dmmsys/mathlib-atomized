/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Finite-dimensional inner product space with a (co)algebra structure

This file proves that a finite-dimensional inner product space has a
coalgebra structure if it has an algebra structure, where
the comultiplication and counit maps are given by taking adjoints of the
multiplication and algebra linear maps, respectively.
This is implemented by providing a linear equivalence between the inner product space
and an algebra.

And similarly, a finite-dimensional inner product space has an algebra
structure if it has a coalgebra structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`,
`(1 : A) = (adjoint counit) (1 : 𝕜)` and `algebraMap = adjoint counit`.

This is useful for when we have a finite-dimensional C⋆-algebra with a faithful and
positive linear functional (so that it induces an inner product structure), and want the coalgebra
structure to be the _adjoint_ of the algebra structure.
This comes up in non-commutative graph theory for example.
-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open TensorProduct LinearMap LinearIsometryEquiv Coalgebra

open EuclideanSpace in
/-- The comultiplication on `n → 𝕜` corresponds to the Euclidean space adjoint of the
multiplication map. -/
/-
**Pi.comul_eq_adjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.comul_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n] : comul = map 
(equiv n 𝕜).toLinearMap (equiv n 𝕜).toLinearMap ∘ₗ ((equiv n 𝕜).symm.toLinearMap
 ∘ₗ mul' 𝕜 (n -> 𝕜) ∘ₗ map (equiv n 𝕜).toLinearMap (equiv n 𝕜).toLinearMap).adjo
int ∘ₗ (equiv n 𝕜).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `PiLp.continuousLinearEquiv_symm_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) {ι
 : Type u_2} (β : ι → Type u_4) [inst : Semiring 𝕜]   [inst_1 : (i : ι) → AddCom
mGroup (β i)] [inst_2 : (i …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x :
 E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y
· 使用定理 `PiLp.continuousLinearEquiv_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) {ι : Ty
pe u_2} (β : ι → Type u_4) [inst : Semiring 𝕜]   [inst_1 : (i : ι) → AddCommGrou
p (β i)] [inst_2 : (i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The comultiplication on `n → 𝕜` corresponds to the Euclidean space adjoint of th
e
multiplication map.
-/
theorem Pi.comul_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n] :
    comul = map (equiv n 𝕜).toLinearMap (equiv n 𝕜).toLinearMap ∘ₗ
      ((equiv n 𝕜).symm.toLinearMap ∘ₗ mul' 𝕜 (n → 𝕜) ∘ₗ
        map (equiv n 𝕜).toLinearMap (equiv n 𝕜).toLinearMap).adjoint ∘ₗ
      (equiv n 𝕜).symm.toLinearMap := by
  ext
  simp only [comp_apply, ← toLinearMap_congr, LinearEquiv.coe_coe, ← LinearEquiv.symm_apply_eq]
  simp [TensorProduct.ext_iff_inner_left, adjoint_inner_right, inner_eq_star_dotProduct]

open EuclideanSpace in
/-- The counit on `n → 𝕜` corresponds to the Euclidean space adjoint of the algebra linear map. -/
/-
**Pi.counit_eq_adjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.counit_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n] : counit = ((
equiv n 𝕜).symm.toLinearMap ∘ₗ Algebra.linearMap 𝕜 (n -> 𝕜)).adjoint ∘ₗ (equiv n
 𝕜).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.counit_comp_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemir
ing R] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_
3 : (i : n)…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.comp_toSpanSingleton`：comp_toSpanSingleton [AddCommMonoid M₂] 
[Module R M₂] (f : M ->ₗ[R] M₂) (x : M) : f ∘ₗ toSpanSingleton R M x = toSpanSin
gleton R M₂ (f x)
· 使用定理 `PiLp.continuousLinearEquiv_symm_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) {ι
 : Type u_2} (β : ι → Type u_4) [inst : Semiring 𝕜]   [inst_1 : (i : ι) → AddCom
mGroup (β i)] [inst_2 : (i …
· 使用定理 `LinearMap.adjoint_toSpanSingleton`：adjoint_toSpanSingleton (x : E) : adj
oint (toSpanSingleton 𝕜 E x) = innerₛₗ 𝕜 x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The counit on `n → 𝕜` corresponds to the Euclidean space adjoint of the algebra 
linear map.
-/
theorem Pi.counit_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n] :
    counit = ((equiv n 𝕜).symm.toLinearMap ∘ₗ Algebra.linearMap 𝕜 (n → 𝕜)).adjoint ∘ₗ
      (equiv n 𝕜).symm.toLinearMap := by
  ext
  simp [← toSpanSingleton_one_eq_algebraLinearMap, comp_toSpanSingleton,
    adjoint_toSpanSingleton, inner_eq_star_dotProduct]

namespace InnerProductSpace

section coalgebraOfAlgebra
variable {A : Type*} [Ring A] [Module 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- A finite-dimensional inner product space with an algebra structure induces
a coalgebra, where comultiplication is given by the adjoint of multiplication
and the counit is given by the adjoint of the algebra map.

This is implemented by providing a linear equivalence between the inner product
space and an algebra.

See note [reducible non-instances]. -/
/-
**InnerProductSpace.coalgebraOfAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `InnerProduct
Space`。
形式化陈述：coalgebraOfAlgebra (e : E ≃ₗ[𝕜] A) : Coalgebra 𝕜 E where comul
参数：e : E ≃ₗ[𝕜] A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-dimensional inner product space with an algebra structure induces
a coalgebra, where comultiplication is given by the adjoint of multiplication
and the counit is given by the adjoint of the algebra map.

This is implemented by providing a linear equivalence between the inner product
space and an algebra.

See note [reducible non-instances].
-/
noncomputable abbrev coalgebraOfAlgebra (e : E ≃ₗ[𝕜] A) : Coalgebra 𝕜 E where
  comul := adjoint (e.symm.toLinearMap ∘ₗ mul' 𝕜 A ∘ₗ map e.toLinearMap e.toLinearMap)
  counit := innerₛₗ 𝕜 (e.symm 1)
  coassoc := by
    rw [← adjoint_lTensor, ← adjoint_rTensor, ← toLinearEquiv_assocIsometry,
      ← (assocIsometry 𝕜 _ _ _).symm_symm, ← adjoint_toLinearMap_eq_symm]
    simp_rw [← adjoint_comp]
    congr 1; ext; simp [mul_assoc]
  rTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton, ← adjoint_rTensor, ← adjoint_comp, ← toLinearMap_symm_lid,
      ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm, ← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp
  lTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton, ← adjoint_lTensor, ← adjoint_comp, ← toLinearMap_symm_rid,
      ← comm_trans_lid, ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_trans, ← toLinearEquiv_symm, ← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp

end coalgebraOfAlgebra

section algebraOfCoalgebra
variable [Coalgebra 𝕜 E]

/-- The multiplication on a finite-dimensional inner product space with a coalgebra structure
given by `x * y = (adjoint comul) (x ⊗ₜ y)`.

See note [reducible non-instances]. -/
/-
**InnerProductSpace.mulOfCoalgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `InnerProductSpac
e`。
形式化陈述：mulOfCoalgebra : Mul E where mul x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication on a finite-dimensional inner product space with a coalgebra 
structure
given by `x * y = (adjoint comul) (x ⊗ₜ y)`.

See note [reducible non-instances].
-/
noncomputable abbrev mulOfCoalgebra :
    Mul E where mul x y := adjoint (comul (R := 𝕜) (A := E)) (x ⊗ₜ y)

attribute [local instance] InnerProductSpace.mulOfCoalgebra in
/-
**InnerProductSpace.AlgebraOfCoalgebra.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.AlgebraOfCoalgebra`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] [ins
t_4 : Coalgebra 𝕜 E] (x y : E),   x * y = (LinearMap.adjoint CoalgebraStruct.com
ul) (x ⊗ₜ[𝕜] y)
参数：x y : E；LinearMap.adjoint CoalgebraStruct.comul；x ⊗ₜ[𝕜] y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AlgebraOfCoalgebra.mul_def (x y : E) :
    x * y = adjoint (comul (R := 𝕜) (A := E)) (x ⊗ₜ y) := rfl

attribute [local simp] AlgebraOfCoalgebra.mul_def

attribute [local instance] InnerProductSpace.mulOfCoalgebra in
/-- A finite-dimensional inner product space with a coalgebra structure induces a ring structure,
where multiplication is given by `x * y = (adjoint comul) (x ⊗ₜ y)` and
`1 = (adjoint counit) (1 : 𝕜)`.

See note [reducible non-instances]. -/
/-
**InnerProductSpace.ringOfCoalgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `InnerProductSpa
ce`。
形式化陈述：ringOfCoalgebra : Ring E where left_distrib x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-dimensional inner product space with a coalgebra structure induces a ri
ng structure,
where multiplication is given by `x * y = (adjoint comul) (x ⊗ₜ y)` and
`1 = (adjoint counit) (1 : 𝕜)`.

See note [reducible non-instances].
-/
noncomputable abbrev ringOfCoalgebra :
    Ring E where
  left_distrib x y z := by simp [tmul_add]
  right_distrib x y z := by simp [add_tmul]
  zero_mul x := by simp
  mul_zero x := by simp
  mul_assoc x y z := by
    simp_rw [AlgebraOfCoalgebra.mul_def, ← rTensor_tmul, ← comp_apply, ← adjoint_rTensor,
      ← adjoint_comp, ← coassoc_symm, adjoint_comp, adjoint_lTensor, comp_apply,
      ← toLinearEquiv_assocIsometry, ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp only [symm_symm, toLinearEquiv_assocIsometry, LinearEquiv.coe_coe, assoc_tmul,
      lTensor_tmul]
  one := adjoint (counit (R := 𝕜) (A := E)) 1
  one_mul x := by
    dsimp [OfNat.ofNat]
    rw [← rTensor_tmul, ← comp_apply, ← adjoint_rTensor, ← adjoint_comp, rTensor_counit_comp_comul,
      ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
      adjoint_toLinearMap_eq_symm]
    exact one_smul _ _
  mul_one x := by
    dsimp [OfNat.ofNat]
    rw [← lTensor_tmul, ← comp_apply, ← adjoint_lTensor, ← adjoint_comp, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← comm_trans_lid, ← toLinearEquiv_commIsometry,
      ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans, ← toLinearEquiv_symm,
      adjoint_toLinearMap_eq_symm]
    exact one_smul _ _

attribute [local instance] InnerProductSpace.ringOfCoalgebra in
/-- A finite-dimensional inner product space with a coalgebra structure induces an algebra
structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`, `1 = (adjoint counit) 1` and
`algebraMap = adjoint counit`.

See note [reducible non-instances]. -/
/-
**InnerProductSpace.algebraOfCoalgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `InnerProduct
Space`。
形式化陈述：algebraOfCoalgebra : Algebra 𝕜 E where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-dimensional inner product space with a coalgebra structure induces an a
lgebra
structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`, `1 = (adjoint counit) 1` an
d
`algebraMap = adjoint counit`.

See note [reducible non-instances].
-/
noncomputable abbrev algebraOfCoalgebra : Algebra 𝕜 E where
  algebraMap :=
    { toFun := adjoint (Coalgebra.counit (R := 𝕜) (A := E))
      map_one' := rfl
      map_mul' x y := by
        simp_rw [AlgebraOfCoalgebra.mul_def, ← map_tmul, ← adjoint_map, ← comp_apply,
          ← adjoint_comp, ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul,
          adjoint_comp, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
          adjoint_toLinearMap_eq_symm]
        simp only [LinearIsometryEquiv.symm_symm, toLinearEquiv_lidIsometry, adjoint_lTensor,
          coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_tmul, lid_tmul]
        rw [← smul_eq_mul, ← _root_.map_smul]
      map_zero' := map_zero _
      map_add' := map_add _ }
  commutes' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← lTensor_tmul, ← adjoint_lTensor, ← adjoint_rTensor,
      ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← toLinearMap_symm_lid, ← comm_trans_lid,
      ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp
  smul_def' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← adjoint_rTensor, ← comp_apply, ← adjoint_comp,
      rTensor_counit_comp_comul, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp

end algebraOfCoalgebra
end InnerProductSpace

