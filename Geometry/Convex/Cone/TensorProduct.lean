/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Tensor products of cones

Given ordered modules `M` and `N`, there are in general several distinct possible
orderings of the tensor product module `M ⊗ N`. Since the ordering of an ordered module
can be represented by its cone of nonnegative elements, there are likewise multiple
ways to construct a cone in `M ⊗ N` from cones in `M` and `N`. Such constructions
are referred to as tensor products of cones.

"Sufficiently nice" candidates for tensor products of cones are bounded by the minimal
and maximal tensor products. These products are generally distinct but coincide in special cases.

We define the minimal and maximal tensor products of pointed cones:

* `minTensorProduct C₁ C₂`: all conical combinations of elementary tensor products
  `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`.
* `maxTensorProduct C₁ C₂`: the dual cone of the minimal tensor product of the dual cones.

## Main results

* `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## Notation

* no special notation defined
* x, y, z are elements of the (original) cones
* φ, ψ are elements of the dual cones

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

@[expose] public section

open TensorProduct Module

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G : Type*} [AddCommGroup G] [Module R G]
variable {H : Type*} [AddCommGroup H] [Module R H]

namespace PointedCone

/-- The minimal tensor product of two cones is given by all conical combinations of elementary
tensor products `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`. -/
/-
**PointedCone.minTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) : PointedCo
ne R (G otimes[R] H)
参数：C₁ : PointedCone R G；C₂ : PointedCone R H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal tensor product of two cones is given by all conical combinations of 
elementary
tensor products `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`.
-/
noncomputable def minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .hull R (.image2 (· ⊗ₜ[R] ·) C₁ C₂)

/-- The maximal tensor product of two cones is the dual (pointed cone) of the minimal tensor product
of the dual cones. -/
/-
**PointedCone.maxTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) : PointedCo
ne R (G otimes[R] H)
参数：C₁ : PointedCone R G；C₂ : PointedCone R H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal tensor product of two cones is the dual (pointed cone) of the minima
l tensor product
of the dual cones.
-/
noncomputable def maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .dual (dualDistrib R G H) (minTensorProduct (.dual (Dual.eval R G) C₁)
    (.dual (Dual.eval R H) C₂))

/-- Characterization of the maximal tensor product: `z` lies in `maxTensorProduct C₁ C₂` iff
all pairings with elementary dual tensors are nonnegative. -/
@[simp]
/-
**PointedCone.mem_maxTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：mem_maxTensorProduct {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G 
otimes[R] H} : z in maxTensorProduct (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PointedCone.dual_hull`：dual_hull (s : Set M) : dual p (hull R s) = dual 
p s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterization of the maximal tensor product: `z` lies in `maxTensorProduct C₁
 C₂` iff
all pairings with elementary dual tensors are nonnegative.
-/
theorem mem_maxTensorProduct {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G ⊗[R] H} :
    z ∈ maxTensorProduct (R := R) C₁ C₂ ↔
      ∀ φ ∈ PointedCone.dual (Dual.eval R G) C₁,
      ∀ ψ ∈ PointedCone.dual (Dual.eval R H) C₂,
      0 ≤ dualDistrib R G H (φ ⊗ₜ[R] ψ) z := by
  simp only [maxTensorProduct, minTensorProduct, dual_hull, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, mem_dual]

/-- Elementary tensors are members of the maximal tensor product. -/
/-
**PointedCone.tmul_mem_maxTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：tmul_mem_maxTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R
 H} (hx : x in C₁) (hy : y in C₂) : x otimesₜ[R] y in maxTensorProduct C₁ C₂
参数：hx : x in C₁；hy : y in C₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b

--- 原说明 ---
Elementary tensors are members of the maximal tensor product.
-/
theorem tmul_mem_maxTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[R] y ∈ maxTensorProduct C₁ C₂ := by
  simp only [mem_maxTensorProduct, dualDistrib_apply]
  exact fun φ hφ ψ hψ => mul_nonneg (hφ hx) (hψ hy)

/-- Elementary tensors are members of the minimal tensor product. -/
/-
**PointedCone.tmul_mem_minTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：tmul_mem_minTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R
 H} (hx : x in C₁) (hy : y in C₂) : x otimesₜ[R] y in minTensorProduct C₁ C₂
参数：hx : x in C₁；hy : y in C₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t

--- 原说明 ---
Elementary tensors are members of the minimal tensor product.
-/
theorem tmul_mem_minTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[R] y ∈ minTensorProduct C₁ C₂ :=
  Submodule.subset_span (Set.mem_image2_of_mem hx hy)

/-- The maximal tensor product contains the set of all elementary tensors. -/
/-
**PointedCone.tmul_subset_maxTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `PointedCon
e`。
形式化陈述：tmul_subset_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H)
 : .image2 (· otimesₜ[R] ·) C₁ C₂ subseteq (maxTensorProduct C₁ C₂ : Set (G otim
es[R] H))
参数：C₁ : PointedCone R G；C₂ : PointedCone R H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.tmul_mem_maxTensorProduct`：tmul_mem_maxTensorProduct {x y} {
C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁) (hy : y in C₂) : x o
timesₜ[R] y in maxTensorPro…

--- 原说明 ---
The maximal tensor product contains the set of all elementary tensors.
-/
theorem tmul_subset_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    .image2 (· ⊗ₜ[R] ·) C₁ C₂ ⊆ (maxTensorProduct C₁ C₂ : Set (G ⊗[R] H)) :=
  fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_maxTensorProduct hx hy

/-- The minimal tensor product contains the set of all elementary tensors. -/
/-
**PointedCone.tmul_subset_minTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `PointedCon
e`。
形式化陈述：tmul_subset_minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H)
 : .image2 (· otimesₜ[R] ·) C₁ C₂ subseteq (minTensorProduct C₁ C₂ : Set (G otim
es[R] H))
参数：C₁ : PointedCone R G；C₂ : PointedCone R H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.tmul_mem_minTensorProduct`：tmul_mem_minTensorProduct {x y} {
C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁) (hy : y in C₂) : x o
timesₜ[R] y in minTensorPro…

--- 原说明 ---
The minimal tensor product contains the set of all elementary tensors.
-/
theorem tmul_subset_minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    .image2 (· ⊗ₜ[R] ·) C₁ C₂ ⊆ (minTensorProduct C₁ C₂ : Set (G ⊗[R] H)) :=
  fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_minTensorProduct hx hy

/-- The minimal tensor product is less than or equal to the maximal tensor product. -/
/-
**PointedCone.minTensorProduct_le_maxTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `Po
intedCone`。
形式化陈述：minTensorProduct_le_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedC
one R H) : minTensorProduct C₁ C₂ <= maxTensorProduct C₁ C₂
参数：C₁ : PointedCone R G；C₂ : PointedCone R H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `PointedCone.tmul_subset_maxTensorProduct`：tmul_subset_maxTensorProduct (
C₁ : PointedCone R G) (C₂ : PointedCone R H) : .image2 (· otimesₜ[R] ·) C₁ C₂ su
bseteq (maxTensorProduct C₁ C₂…

--- 原说明 ---
The minimal tensor product is less than or equal to the maximal tensor product.
-/
theorem minTensorProduct_le_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    minTensorProduct C₁ C₂ ≤ maxTensorProduct C₁ C₂ := by
  exact Submodule.span_le.mpr (tmul_subset_maxTensorProduct C₁ C₂)

variable {C₁ C₁' : PointedCone R G} {C₂ C₂' : PointedCone R H} {z : G ⊗[R] H}

/-- The minimal tensor product is commutative. -/
@[simp]
/-
**PointedCone.minTensorProduct_comm** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：minTensorProduct_comm : (minTensorProduct C₁ C₂).map (TensorProduct.comm R
 G H) = minTensorProduct C₂ C₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The minimal tensor product is commutative.
-/
theorem minTensorProduct_comm :
    (minTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = minTensorProduct C₂ C₁ := by
  simp [minTensorProduct, map, hull, Submodule.map_span, Set.image_image2,
    Set.image2_swap (· ⊗ₜ[R] · : H → G → _)]

/-- The maximal tensor product is commutative. -/
@[simp]
/-
**PointedCone.maxTensorProduct_comm** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：maxTensorProduct_comm : (maxTensorProduct C₁ C₂).map (TensorProduct.comm R
 G H) = maxTensorProduct C₂ C₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TensorProduct.dualDistrib_apply_comm`：dualDistrib_apply_comm (w : Dual R
 N otimes[R] Dual R M) (z : M otimes[R] N) : dualDistrib R N M w (TensorProduct.
comm R M N z) = dualDistri…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b

--- 原说明 ---
The maximal tensor product is commutative.
-/
theorem maxTensorProduct_comm :
    (maxTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = maxTensorProduct C₂ C₁ := by
  ext z
  simp only [mem_map, mem_maxTensorProduct]
  refine ⟨?_, fun hz ↦
    ⟨(TensorProduct.comm R H G) z, ?_, (TensorProduct.comm R H G).symm_apply_apply z⟩⟩
  · rintro ⟨w, hw, rfl⟩ ψ hψ φ hφ
    simpa [dualDistrib_apply_comm] using hw φ hφ ψ hψ
  · intro φ hφ ψ hψ
    simpa [dualDistrib_apply_comm] using hz ψ hψ φ hφ

/-- `minTensorProduct` is monotone. -/
@[gcongr]
/-
**PointedCone.minTensorProduct_mono** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：minTensorProduct_mono (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂') : minTensorProduct
 C₁ C₂ <= minTensorProduct C₁' C₂'
参数：h₁ : C₁ <= C₁'；h₂ : C₂ <= C₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'

--- 原说明 ---
`minTensorProduct` is monotone.
-/
theorem minTensorProduct_mono (h₁ : C₁ ≤ C₁') (h₂ : C₂ ≤ C₂') :
    minTensorProduct C₁ C₂ ≤ minTensorProduct C₁' C₂' :=
  Submodule.span_mono <| Set.image2_subset h₁ h₂

/-- `maxTensorProduct` is monotone. -/
/-
**PointedCone.maxTensorProduct_mono** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：maxTensorProduct_mono (h₁ : C₁ <= C₁') (h₂ : C₂ <= C₂') : maxTensorProduct
 C₁ C₂ <= maxTensorProduct C₁' C₂'
参数：h₁ : C₁ <= C₁'；h₂ : C₂ <= C₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.mem_maxTensorProduct`：mem_maxTensorProduct {C₁ : PointedCone
 R G} {C₂ : PointedCone R H} {z : G otimes[R] H} : z in maxTensorProduct (R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PointedCone.dual_le_dual`：∀ {R : Type u_1} [inst : CommSemiring R] [inst
_1 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid M] [i…

--- 原说明 ---
`maxTensorProduct` is monotone.
-/
theorem maxTensorProduct_mono (h₁ : C₁ ≤ C₁') (h₂ : C₂ ≤ C₂') :
    maxTensorProduct C₁ C₂ ≤ maxTensorProduct C₁' C₂' :=
  fun _ hz => mem_maxTensorProduct.mpr fun φ hφ ψ hψ =>
    mem_maxTensorProduct.mp hz φ (dual_le_dual h₁ hφ) ψ (dual_le_dual h₂ hψ)

variable {G' H' : Type*} [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- `minTensorProduct` is functorial: the image of a minimal tensor product under
`TensorProduct.map f g` is contained in the minimal tensor product of the images. -/
/-
**PointedCone.minTensorProduct_map_le** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：minTensorProduct_map_le (f : G ->ₗ[R] G') (g : H ->ₗ[R] H') (C₁ : PointedC
one R G) (C₂ : PointedCone R H) : (minTensorProduct C₁ C₂).map (TensorProduct.ma
p f g) <= minTensorProduct (C₁.map f) (C₂.map g)
参数：f : G ->ₗ[R] G'；g : H ->ₗ[R] H'；C₁ : PointedCone R G；C₂ : PointedCone R H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.map_span_le`：map_span_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ
₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) : map f (span R s) <= N ↔ forall m in 
s, f m in N
· 使用定理 `PointedCone.tmul_mem_minTensorProduct`：tmul_mem_minTensorProduct {x y} {
C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x in C₁) (hy : y in C₂) : x o
timesₜ[R] y in minTensorPro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.map_tmul`：map_tmul (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N
₂) (m : M) (n : N) : map f g (m otimesₜ n) = f m otimesₜ g n

--- 原说明 ---
`minTensorProduct` is functorial: the image of a minimal tensor product under
`TensorProduct.map f g` is contained in the minimal tensor product of the images
.
-/
theorem minTensorProduct_map_le (f : G →ₗ[R] G') (g : H →ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (minTensorProduct C₁ C₂).map (TensorProduct.map f g) ≤
      minTensorProduct (C₁.map f) (C₂.map g) :=
  (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, y, hy, h⟩ ↦
    h ▸ map_tmul f g x y ▸ tmul_mem_minTensorProduct ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- `maxTensorProduct` is functorial: the image of a maximal tensor product under
`TensorProduct.map f g` is contained in the maximal tensor product of the images. -/
/-
**PointedCone.maxTensorProduct_map_le** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：maxTensorProduct_map_le (f : G ->ₗ[R] G') (g : H ->ₗ[R] H') (C₁ : PointedC
one R G) (C₂ : PointedCone R H) : (maxTensorProduct C₁ C₂).map (TensorProduct.ma
p f g) <= maxTensorProduct (C₁.map f) (C₂.map g)
参数：f : G ->ₗ[R] G'；g : H ->ₗ[R] H'；C₁ : PointedCone R G；C₂ : PointedCone R H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
`maxTensorProduct` is functorial: the image of a maximal tensor product under
`TensorProduct.map f g` is contained in the maximal tensor product of the images
.
-/
theorem maxTensorProduct_map_le (f : G →ₗ[R] G') (g : H →ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (maxTensorProduct C₁ C₂).map (TensorProduct.map f g) ≤
      maxTensorProduct (C₁.map f) (C₂.map g) := by
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, mem_maxTensorProduct] at hw ⊢
  intro φ hφ ψ hψ
  have h_eq : ((dualDistrib R G' H') (φ ⊗ₜ[R] ψ)).comp (TensorProduct.map f g) =
      ((dualDistrib R G H) ((φ.comp f) ⊗ₜ[R] (ψ.comp g))) :=
    TensorProduct.ext' fun x y ↦ by simp [map_tmul]
  convert! hw (φ.comp f) (fun x hx ↦ hφ ⟨x, hx, rfl⟩) (ψ.comp g) (fun y hy ↦ hψ ⟨y, hy, rfl⟩)
  exact DFunLike.congr_fun h_eq w

end PointedCone

