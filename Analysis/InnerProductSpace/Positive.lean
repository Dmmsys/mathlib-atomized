/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Trace

/-!
# Positive operators

In this file we define when an operator in a Hilbert space is positive. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `LinearMap.IsPositive` : a linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.
* `ContinuousLinearMap.IsPositive` : a continuous linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.

## Main statements

* `ContinuousLinearMap.IsPositive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `ContinuousLinearMap.isPositive_iff_complex` : in a ***complex*** Hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/

@[expose] public section

open InnerProductSpace RCLike LinearMap ContinuousLinearMap

open scoped InnerProduct ComplexConjugate ComplexOrder

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-- A linear operator `T` on a Hilbert space is **positive** if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
/-
**LinearMap.IsPositive** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsPositive (T : E ->ₗ[𝕜] E) : Prop
参数：T : E ->ₗ[𝕜] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear operator `T` on a Hilbert space is **positive** if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.
-/
def IsPositive (T : E →ₗ[𝕜] E) : Prop :=
  IsSymmetric T ∧ ∀ x, 0 ≤ re ⟪T x, x⟫
/-
**LinearMap.IsPositive.isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPositi
ve`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → T.IsS
ymmetric
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsPositive.isSymmetric {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSymmetric T := hT.1
/-
**LinearMap.IsPositive.re_inner_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ RCLike.re (inner 𝕜 (T x) x)
参数：x : E；inner 𝕜 (T x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsPositive.re_inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪T x, x⟫ :=
  hT.2 x
/-
**LinearMap.IsPositive.re_inner_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ RCLike.re (inner 𝕜 x (T x))
参数：x : E；inner 𝕜 x (T x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.re_inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace
 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `inner_re_symm`：inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫
-/
theorem IsPositive.re_inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪x, T x⟫ :=
  inner_re_symm (𝕜 := 𝕜) _ x ▸ hT.re_inner_nonneg_left x

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

/-
**LinearMap.isPositive_iff_complex** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_iff_complex (T : E' ->ₗ[Complex] E') : IsPositive T ↔ forall x,
 (re ⟪T x, x⟫_Complex : Complex) = ⟪T x, x⟫_Complex ∧ 0 <= re ⟪T x, x⟫_Complex
参数：T : E' ->ₗ[Complex] E'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPositive_iff_complex (T : E' →ₗ[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp_rw [IsPositive, forall_and, isSymmetric_iff_inner_map_self_real,
    conj_eq_iff_re, re_to_complex, Complex.coe_algebraMap]

end Complex

/-
**LinearMap.IsPositive.isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPosi
tive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {T :
 E →ₗ[𝕜] E}, T.IsPositive → IsSelfAdjoint T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.isSymmetric_iff_isSelfAdjoint`：isSymmetric_iff_isSelfAdjoint (
A : E ->ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
-/
theorem IsPositive.isSelfAdjoint [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := (isSymmetric_iff_isSelfAdjoint _).mp hT.isSymmetric
/-
**LinearMap.IsPositive.adjoint_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPositiv
e`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {T :
 E →ₗ[𝕜] E}, T.IsPositive → LinearMap.adjoint T = T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.isSelfAdjoint`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]  
 [inst_3 : FiniteDimensi…
-/
theorem IsPositive.adjoint_eq [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    T.adjoint = T := hT.isSelfAdjoint
/-
**LinearMap.isPositive_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_iff (T : E ->ₗ[𝕜] E) : IsPositive T ↔ IsSymmetric T ∧ forall x,
 0 <= ⟪T x, x⟫
参数：T : E ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RCLike.ofReal_nonneg`：ofReal_nonneg {x : Real} : 0 <= (x : K) ↔ 0 <= x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsSymmetric.coe_re_inner_apply_self`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPositive_iff (T : E →ₗ[𝕜] E) :
    IsPositive T ↔ IsSymmetric T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [hT]
/-
**LinearMap.IsPositive.inner_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Is
Positive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ inner 𝕜 (T x) x
参数：x : E；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.isPositive_iff`：isPositive_iff (T : E ->ₗ[𝕜] E) : IsPositive T
 ↔ IsSymmetric T ∧ forall x, 0 <= ⟪T x, x⟫
-/
theorem IsPositive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) : 0 ≤ ⟪T x, x⟫ :=
  (T.isPositive_iff.mp hT).right x
/-
**LinearMap.IsPositive.inner_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ inner 𝕜 x (T x)
参数：x : E；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_2} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 
E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
-/
theorem IsPositive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ :=
  hT.isSymmetric _ _ ▸ hT.inner_nonneg_left x

@[simp]
/-
**LinearMap.isPositive_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_zero : IsPositive (0 : E ->ₗ[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   Li
nearMap.IsSymmet…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isPositive_zero : IsPositive (0 : E →ₗ[𝕜] E) := ⟨.zero, by simp⟩

@[simp]
/-
**LinearMap.isPositive_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_one : IsPositive (1 : E ->ₗ[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.id`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike
 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   Line
arMap.id.IsSym…
· 使用定理 `inner_self_nonneg`：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫
-/
theorem isPositive_one : IsPositive (1 : E →ₗ[𝕜] E) := ⟨.id, fun _ => inner_self_nonneg⟩

@[simp]
/-
**LinearMap.isPositive_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_id : IsPositive (id : E ->ₗ[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isPositive_one`：isPositive_one : IsPositive (1 : E ->ₗ[𝕜] E)
-/
theorem isPositive_id : IsPositive (id : E →ₗ[𝕜] E) := isPositive_one

@[simp]
/-
**LinearMap.isPositive_natCast** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_natCast {n : Nat} : IsPositive (n : E ->ₗ[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.natCast`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : R
CLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   
(n : ℕ), (↑n).IsSym…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.natCast_re`：natCast_re (n : Nat) : re (n : K) = n
· 使用定理 `inner_self_im`：inner_self_im (x : E) : im ⟪x, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `inner_self_nonneg`：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem isPositive_natCast {n : ℕ} : IsPositive (n : E →ₗ[𝕜] E) := by
  refine ⟨IsSymmetric.natCast n, fun x => ?_⟩
  simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, map_natCast,
    mul_re, natCast_re, inner_self_im, mul_zero, sub_zero]
  positivity [inner_self_nonneg (x := x) (𝕜 := 𝕜)]

@[simp]
/-
**LinearMap.isPositive_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_ofNat {n : Nat} [n.AtLeastTwo] : IsPositive (ofNat(n) : E ->ₗ[𝕜
] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isPositive_natCast`：isPositive_natCast {n : Nat} : IsPositive 
(n : E ->ₗ[𝕜] E)
-/
theorem isPositive_ofNat {n : ℕ} [n.AtLeastTwo] : IsPositive (ofNat(n) : E →ₗ[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
/-
**LinearMap.IsPositive.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S : E →ₗ[𝕜] E}, T.IsPositive → S.I
sPositive → (T + S).IsPositive
参数：T + S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.add`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S
 : E →ₗ[𝕜] E}, …
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.add_apply`：add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) 
x = f x + g x
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearMap.IsPositive.re_inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace
 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
-/
theorem IsPositive.add {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive := by
  refine ⟨hT.isSymmetric.add hS.isSymmetric, fun x => ?_⟩
  rw [add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)
/-
**LinearMap.isPositive_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPositive_sum {ι : Type*} {T : ι -> (E ->ₗ[𝕜] E)} (s : Finset ι) (hT : fo
rall i in s, (T i).IsPositive) : (∑ i in s, T i).IsPositive
参数：E ->ₗ[𝕜] E；s : Finset ι；hT : forall i in s, (T i).IsPositive。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isSymmetric_sum`：isSymmetric_sum {ι : Type*} {T : ι -> (E ->ₗ[
𝕜] E)} (s : Finset ι) (hT : forall i in s, (T i).IsSymmetric) : (∑ i in s, T i).
IsSymmetric
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearMap.IsPositive.re_inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace
 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
-/
theorem isPositive_sum {ι : Type*} {T : ι → (E →ₗ[𝕜] E)} (s : Finset ι)
    (hT : ∀ i ∈ s, (T i).IsPositive) : (∑ i ∈ s, T i).IsPositive := by
  refine ⟨isSymmetric_sum s fun _ hi ↦ (hT _ hi).isSymmetric, fun _ ↦ ?_⟩
  simpa [sum_inner] using Finset.sum_nonneg fun _ hi ↦ (hT _ hi).re_inner_nonneg_left _
/-
**LinearMap.IsPositive.ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPositi
ve`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → (T ≠ 
0 ↔ ∃ x, 0 < inner 𝕜 (T x) x)
参数：T ≠ 0 ↔ ∃ x, 0 < inner 𝕜 (T x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymmetric.inner_map_self_eq_zero`：∀ {𝕜 : Type u_1} {E : Type
 u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSy…
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearMap.IsPositive.inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_2} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 
E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsPositive.ne_zero_iff {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    T ≠ 0 ↔ ∃ x, 0 < inner 𝕜 (T x) x := by
  simp [← hT.isSymmetric.inner_map_self_eq_zero, lt_iff_le_and_ne', hT.inner_nonneg_left]

@[aesop safe apply]
/-
**LinearMap.IsPositive.smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPos
itive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → ∀ {c 
: 𝕜}, 0 ≤ c → (c • T).IsPositive
参数：c • T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.IsSymmetric.smul`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {c 
: 𝕜}, (starRingE…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.conj_eq_iff_im`：conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RCLike.re_nonneg_of_nonneg`：re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjo
int x) : 0 <= re x ↔ 0 <= x
· 使用定理 `LinearMap.IsPositive.re_inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace
 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
-/
theorem IsPositive.smul_of_nonneg {T : E →ₗ[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).IsPositive := by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  refine ⟨hT.left.smul hc', fun x => ?_⟩
  rw [smul_apply, inner_smul_left, hc', mul_re, conj_eq_iff_im.mp hc', zero_mul, sub_zero]
  exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)
/-
**LinearMap.IsPositive.isPositive_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.
IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPositive → T ≠ 0
 → ∀ {α : 𝕜}, (α • T).IsPositive ↔ 0 ≤ α
参数：α • T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.IsPositive.ne_zero_iff`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `LinearMap.IsPositive.inner_nonneg_right`：∀ {𝕜 : Type u_1} {E : Type u_2}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜
 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `le_of_smul_le_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ 
: α} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [in
st_3 : Zero β] [SMulP…
· 使用定理 `MulPosReflectLE.toSMulPosReflectLE`：∀ {α : Type u_1} [inst : Zero α] [in
st_1 : Mul α] [inst_2 : Preorder α] [MulPosReflectLE α], SMulPosReflectLE α α
· 使用引理 `RCLike.instMulPosReflectLE`：instMulPosReflectLE : MulPosReflectLE K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LinearMap.IsPositive.smul_of_nonneg`：∀ {𝕜 : Type u_1} {E : Type u_2} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  {T : E →ₗ[𝕜] E}, T.IsPo…
-/
theorem IsPositive.isPositive_smul_iff {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (hT' : T ≠ 0) {α : 𝕜} :
    (α • T).IsPositive ↔ 0 ≤ α := by
  refine ⟨fun h ↦ ?_, hT.smul_of_nonneg⟩
  obtain ⟨x, hx⟩ := by simpa only [hT.1 _] using hT.ne_zero_iff.mp hT'
  have := by simpa [inner_smul_right] using h.inner_nonneg_right x
  exact le_of_smul_le_smul_of_pos_right (by simpa) hx
/-
**LinearMap.IsPositive.nonneg_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {T :
 E →ₗ[𝕜] E} {n : ℕ} (hT : T.IsPositive) (hn : Module.finrank 𝕜 E = n)   (i : Fin
 n), 0 ≤ ⋯.eigenvalues hn i
参数：hT : T.IsPositive；hn : Module.finrank 𝕜 E = n；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsSymmetric.apply_eigenvectorBasis`：apply_eigenvectorBasis (hT
 : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : T (hT.eigenvectorB
asis hn i) = (hT.eigenvalues hn i …
· 使用定理 `inner_smul_real_left`：inner_smul_real_left (x y : E) (r : Real) : ⟪(r : 
𝕜) • x, y⟫ = r • ⟪x, y⟫
· 使用定理 `RCLike.smul_re`：smul_re (r : Real) (z : K) : re (r • z) = r * re z
· 使用定理 `inner_self_eq_norm_sq`：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^
 2
· 使用引理 `OrthonormalBasis.norm_eq_one`：norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (
i : ι) : ‖b i‖ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsPositive.nonneg_eigenvalues [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} {n : ℕ} (hT : T.IsPositive)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 ≤ hT.isSymmetric.eigenvalues hn i := by
  simpa only [hT.isSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
      using hT.right (hT.isSymmetric.eigenvectorBasis hn i)

section PartialOrder

/-- The (Loewner) partial order on linear maps on a Hilbert space determined by `f ≤ g`
if and only if `g - f` is a positive linear map (in the sense of `LinearMap.IsPositive`). -/
/-
**LinearMap.instLoewnerPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：instLoewnerPartialOrder : PartialOrder (E ->ₗ[𝕜] E) where le f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (Loewner) partial order on linear maps on a Hilbert space determined by `f ≤
 g`
if and only if `g - f` is a positive linear map (in the sense of `LinearMap.IsPo
sitive`).
-/
instance instLoewnerPartialOrder : PartialOrder (E →ₗ[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero, ← h₂.isSymmetric.inner_map_self_eq_zero]
    intro x
    have hba2 := h₁.2 x
    rw [← neg_le_neg_iff, ← map_neg, ← inner_neg_left, ← neg_apply, neg_sub, neg_zero] at hba2
    rw [← h₂.isSymmetric.coe_re_inner_apply_self, RCLike.ofReal_eq_zero]
    exact le_antisymm hba2 (h₂.2 _)
/-
**LinearMap.le_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：le_def (f g : E ->ₗ[𝕜] E) : f <= g ↔ (g - f).IsPositive
参数：f g : E ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def (f g : E →ₗ[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl
/-
**LinearMap.nonneg_iff_isPositive** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：nonneg_iff_isPositive (f : E ->ₗ[𝕜] E) : 0 <= f ↔ f.IsPositive
参数：f : E ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `LinearMap.le_def`：le_def (f g : E ->ₗ[𝕜] E) : f <= g ↔ (g - f).IsPositiv
e
-/
lemma nonneg_iff_isPositive (f : E →ₗ[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid (E →ₗ[𝕜] E) where add_le_add_left a b hab c := by simpa [le_def]

end PartialOrder

/-- An idempotent linear map is positive iff it is symmetric. -/
/-
**LinearMap.IsIdempotentElem.isPositive_iff_isSymmetric** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.IsIdempotentElem`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdempotentElem T →
 (T.IsPositive ↔ T.IsSymmetric)
参数：T.IsPositive ↔ T.IsSymmetric。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `inner_self_nonneg`：inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫

--- 原说明 ---
An idempotent linear map is positive iff it is symmetric.
-/
theorem IsIdempotentElem.isPositive_iff_isSymmetric {T : E →ₗ[𝕜] E} (hT : IsIdempotentElem T) :
    T.IsPositive ↔ T.IsSymmetric := by
  refine ⟨fun h => h.isSymmetric, fun h => ⟨h, fun x => ?_⟩⟩
  rw [← hT.eq, Module.End.mul_apply, h]
  exact inner_self_nonneg
/-
**LinearMap.isPositive_linearIsometryEquiv_conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：isPositive_linearIsometryEquiv_conj_iff {T : E ->ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F) 
: IsPositive (f.toLinearMap ∘ₗ T ∘ₗ f.symm.toLinearMap) ↔ IsPositive T
参数：f : E ≃ₗᵢ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearIsometryEquiv.inner_map_eq_flip`：LinearIsometryEquiv.inner_map_eq_
flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') : ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
-/
theorem isPositive_linearIsometryEquiv_conj_iff {T : E →ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F) :
    IsPositive (f.toLinearMap ∘ₗ T ∘ₗ f.symm.toLinearMap) ↔ IsPositive T := by
  simp_rw [IsPositive, isSymmetric_linearIsometryEquiv_conj_iff, and_congr_right_iff,
    LinearIsometryEquiv.toLinearEquiv_symm, coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    Function.comp_apply, LinearIsometryEquiv.inner_map_eq_flip]
  exact fun _ => ⟨fun h x => by simpa using h (f x), fun h x => h _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- `A.toEuclideanLin` is positive if and only if `A` is positive semi-definite. -/
/-
**LinearMap._root_.Matrix.isPositive_toEuclideanLin_iff** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.toEuclideanLin` is positive if and only if `A` is positive semi-definite.
-/
@[simp] theorem _root_.Matrix.isPositive_toEuclideanLin_iff {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} : A.toEuclideanLin.IsPositive ↔ A.PosSemidef := by
  simp_rw [LinearMap.IsPositive, Matrix.isSymmetric_toEuclideanLin_iff, inner_re_symm,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    dotProduct_comm (A.mulVec _), Matrix.posSemidef_iff_dotProduct_mulVec, and_congr_right_iff,
    RCLike.nonneg_iff (K := 𝕜)]
  refine fun hA ↦ (EuclideanSpace.equiv n 𝕜).forall_congr' fun x ↦ ?_
  simp [hA.im_star_dotProduct_mulVec_self]

/-- `A.toMatrix` is positive semi-definite if and only if `A` is positive. -/
/-
**LinearMap.posSemidef_toMatrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_4} [inst_3 : Fintype ι] [
inst_4 : DecidableEq ι] {A : E →ₗ[𝕜] E} (b : OrthonormalBasis ι 𝕜 E),   ((Linear
Map.toMatrix b.toBasis b.toBasis) A).PosSemidef ↔ A.IsPositive
参数：b : OrthonormalBasis ι 𝕜 E；(LinearMap.toMatrix b.toBasis b.toBasis) A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isPositive_toEuclideanLin_iff`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜]
 {n : Type u_4} [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n n 𝕜}
,   (Matrix.toEuclideanLin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `LinearEquiv.arrowCongr.congr_simp`：∀ {R₁ : Type u_9} {R₂ : Type u_10} {R
₁' : Type u_12} {R₂' : Type u_13} {M₁ : Type u_17} {M₂ : Type u_18}   {M₁' : Typ
e u_20} {M₂' : Type u_2…
· 使用定理 `OrthonormalBasis.coe_toBasis_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `Matrix.toLin'_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n 
→ R) →ₗ[R] m …
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `WithLp.linearEquiv_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type u_4) 
[inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (a 
: WithLp p V),…
· 使用定理 `WithLp.addEquiv_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCommGro
up V] (self : WithLp p V), (WithLp.addEquiv p V) self = self.ofLp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.isPositive_linearIsometryEquiv_conj_iff`：isPositive_linearIsom
etryEquiv_conj_iff {T : E ->ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F) : IsPositive (f.toLinearMap
 ∘ₗ T ∘ₗ f.symm.toLinearMap) ↔ IsPositi…

--- 原说明 ---
`A.toMatrix` is positive semi-definite if and only if `A` is positive.
-/
@[simp] theorem posSemidef_toMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : E →ₗ[𝕜] E} (b : OrthonormalBasis ι 𝕜 E) :
    (A.toMatrix b.toBasis b.toBasis).PosSemidef ↔ A.IsPositive := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  convert! isPositive_linearIsometryEquiv_conj_iff b.repr
  ext
  simp [LinearMap.toMatrix]

/-- A symmetric projection is positive. -/
@[aesop 10% apply, grind →]
/-
**LinearMap.IsSymmetricProjection.isPositive** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.IsSymmetricProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {p : E →ₗ[𝕜] E}, p.IsSymmetricProject
ion → p.IsPositive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.IsIdempotentElem.isPositive_iff_isSymmetric`：∀ {𝕜 : Type u_1} 
{E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : Inner
ProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdem…
· 使用定理 `LinearMap.IsSymmetricProjection.isIdempotentElem`：∀ {𝕜 : Type u_1} {E : 
Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `LinearMap.IsSymmetricProjection.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type 
u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…

--- 原说明 ---
A symmetric projection is positive.
-/
theorem IsSymmetricProjection.isPositive {p : E →ₗ[𝕜] E} (hp : p.IsSymmetricProjection) :
    p.IsPositive :=
  hp.isIdempotentElem.isPositive_iff_isSymmetric.mpr hp.isSymmetric
/-
**LinearMap.IsSymmetricProjection.le_iff_range_le_range** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.IsSymmetricProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {p q : E →ₗ[𝕜] E}, p.IsSymmetricProje
ction → q.IsSymmetricProjection → (p ≤ q ↔ p.range ≤ q.range)
参数：p ≤ q ↔ p.range ≤ q.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymmetricProjection.isIdempotentElem`：∀ {𝕜 : Type u_1} {E : 
Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `LinearMap.IsSymmetricProjection.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type 
u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `inner_self_eq_norm_sq`：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^
 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.isSymmetricProjection_iff_eq_coe_starProjection`：∀ {𝕜 : Type u
_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : I
nnerProductSpace 𝕜 E]   {p : E →ₗ[𝕜] E}, p.IsSy…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.range_projection`：range_projection (hpq : IsCompl p q) : range
 (p.projection q hpq) = p
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_iff_norm_starProjection`：mem_iff_norm_starProjection (U : 
Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) : v in U ↔ ‖U.starProjection 
v‖ = ‖v‖
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.norm_starProjection_apply_le`：norm_starProjection_apply_le (v 
: E) : ‖K.starProjection v‖ <= ‖v‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearMap.IsIdempotentElem.mem_range_iff`：∀ {S : Type u_5} [inst : Semir
ing S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   
{p : M →ₗ[S] M}, IsIdempotentE…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `LinearMap.IsSymmetricProjection.isPositive`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {p : E →ₗ[𝕜] E}, p.IsSy…
· 使用定理 `LinearMap.IsSymmetricProjection.sub_of_range_le_range`：∀ {𝕜 : Type u_1} 
{E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : Inner
ProductSpace 𝕜 E]   {p q : E →ₗ[𝕜] E},   p.…
-/
theorem IsSymmetricProjection.le_iff_range_le_range {p q : E →ₗ[𝕜] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) : p ≤ q ↔ range p ≤ range q := by
  refine ⟨fun ⟨h1, h2⟩ a ha ↦ ?_, fun hpq ↦ (hp.sub_of_range_le_range hq hpq).isPositive⟩
  specialize h2 a
  have hh {T : E →ₗ[𝕜] E} (hT : T.IsSymmetricProjection) : RCLike.re ⟪T a, a⟫_𝕜 = ‖T a‖ ^ 2 := by
    conv_lhs => rw [← hT.isIdempotentElem]
    rw [Module.End.mul_apply, hT.isSymmetric]
    exact inner_self_eq_norm_sq _
  simp_rw [sub_apply, inner_sub_left, map_sub, hh hq, hh hp,
    hp.isIdempotentElem.mem_range_iff.mp ha, sub_nonneg, sq_le_sq, abs_norm] at h2
  obtain ⟨U, _, rfl⟩ := isSymmetricProjection_iff_eq_coe_starProjection.mp hq
  simpa [Submodule.toLinearMap_starProjection_eq_isComplProjection] using
    U.mem_iff_norm_starProjection _ |>.mpr <| le_antisymm (U.norm_starProjection_apply_le a) h2
/-
**LinearMap.IsPositive.trace_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPosit
ive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {f : E →ₗ[𝕜] E}, f.IsPositive → 0 ≤ (
LinearMap.trace 𝕜 E) f
参数：LinearMap.trace 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LinearMap.traceAux_eq`：traceAux_eq : traceAux R b = traceAux R c
· 使用引理 `Matrix.PosSemidef.trace_nonneg`：trace_nonneg [AddLeftMono R] {A : Matrix
 n n R} (hA : A.PosSemidef) : 0 <= A.trace
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.posSemidef_toMatrix_iff`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst
 : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   
{ι : Type u_4} [inst_3 …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem IsPositive.trace_nonneg {f : E →ₗ[𝕜] E} (hf : f.IsPositive) : 0 ≤ f.trace 𝕜 E := by
  unfold trace
  split_ifs with h
  · have : FiniteDimensional 𝕜 E := Module.Finite.of_basis h.choose_spec.some
    simp_rw [traceAux_eq 𝕜 _ (stdOrthonormalBasis 𝕜 E).toBasis]
    exact posSemidef_toMatrix_iff (stdOrthonormalBasis 𝕜 E) |>.mpr hf |>.trace_nonneg
  · simp

variable (𝕜 E) in
/-- `LinearMap.trace` as a positive linear map. -/
/-
**LinearMap.tracePositiveLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：tracePositiveLinearMap : (E ->ₗ[𝕜] E) ->ₚ[𝕜] 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instIsOrderedAddMonoidId`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E], 
  IsOrderedAddMonoid (E …
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _

--- 原说明 ---
`LinearMap.trace` as a positive linear map.
-/
noncomputable def tracePositiveLinearMap : (E →ₗ[𝕜] E) →ₚ[𝕜] 𝕜 :=
  .mk₀ (LinearMap.trace 𝕜 E) fun x h ↦ sub_zero x ▸ h.trace_nonneg
/-
**LinearMap.toLinearMap_tracePositiveLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E],   (LinearMap.tracePositiveLinearMap 𝕜 
E).toLinearMap = LinearMap.trace 𝕜 E
参数：LinearMap.tracePositiveLinearMap 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_tracePositiveLinearMap :
    (tracePositiveLinearMap 𝕜 E).toLinearMap = trace 𝕜 E := rfl
/-
**LinearMap.tracePositiveLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : E →ₗ[𝕜] E), (LinearMap.tracePosi
tiveLinearMap 𝕜 E) x = (LinearMap.trace 𝕜 E) x
参数：x : E →ₗ[𝕜] E；LinearMap.tracePositiveLinearMap 𝕜 E；LinearMap.trace 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tracePositiveLinearMap_apply (x) : tracePositiveLinearMap 𝕜 E x = x.trace 𝕜 E := rfl

end LinearMap

namespace ContinuousLinearMap

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is symmetric
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
/-
**ContinuousLinearMap.IsPositive** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：IsPositive (T : E ->L[𝕜] E) : Prop
参数：T : E ->L[𝕜] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is
 symmetric
  and `∀ x, 0 ≤ re ⟪T x, x⟫`.
-/
def IsPositive (T : E →L[𝕜] E) : Prop :=
  T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x
/-
**ContinuousLinearMap.isPositive_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isPositive_def {T : E ->L[𝕜] E} : T.IsPositive ↔ T.IsSymmetric ∧ forall x,
 0 <= T.reApplyInnerSelf x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPositive_def {T : E →L[𝕜] E} :
    T.IsPositive ↔ T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x := Iff.rfl

/-- In a complete space, a continuous linear endomorphism `T` is **positive** if it is
symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
/-
**ContinuousLinearMap.isPositive_def'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：isPositive_def' [CompleteSpace E] {T : E ->L[𝕜] E} : T.IsPositive ↔ IsSelf
Adjoint T ∧ forall x, 0 <= T.reApplyInnerSelf x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
In a complete space, a continuous linear endomorphism `T` is **positive** if it 
is
symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`.
-/
theorem isPositive_def' [CompleteSpace E] {T : E →L[𝕜] E} :
    T.IsPositive ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x := by
  simp [IsPositive, isSelfAdjoint_iff_isSymmetric, LinearMap.IsSymmetric]
/-
**ContinuousLinearMap.IsPositive.isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → (↑T).
IsSymmetric
参数：↑T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsPositive.isSymmetric {T : E →L[𝕜] E} (hT : T.IsPositive) :
    T.IsSymmetric := hT.1
/-
**ContinuousLinearMap.IsPositive.isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E] {T : E →L[
𝕜] E}, T.IsPositive → IsSelfAdjoint T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.isSelfAdjoint`：∀ {𝕜 : Type u_1} {E : Type u_2} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  [inst_3 : CompleteSpace…
· 使用定理 `ContinuousLinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
-/
theorem IsPositive.isSelfAdjoint [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := hT.isSymmetric.isSelfAdjoint
/-
**ContinuousLinearMap.IsPositive.inner_left_eq_inner_right** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → ∀ (x 
y : E), inner 𝕜 (T x) y = inner 𝕜 x (T y)
参数：x y : E；T x；T y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
-/
theorem IsPositive.inner_left_eq_inner_right {T : E →L[𝕜] E} (hT : IsPositive T) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ := hT.isSymmetric _ _
/-
**ContinuousLinearMap.IsPositive.re_inner_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ RCLike.re (inner 𝕜 (T x) x)
参数：x : E；inner 𝕜 (T x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsPositive.re_inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪T x, x⟫ := hT.2 x
/-
**ContinuousLinearMap._root_.LinearMap.isPositive_toContinuousLinearMap_iff** 是 
Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.isPositive_toContinuousLinearMap_iff
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    T.toContinuousLinearMap.IsPositive ↔ T.IsPositive := Iff.rfl
/-
**ContinuousLinearMap.isPositive_toLinearMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：isPositive_toLinearMap_iff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive 
↔ T.IsPositive
参数：T : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isPositive_toLinearMap_iff (T : E →L[𝕜] E) :
    (T : E →ₗ[𝕜] E).IsPositive ↔ T.IsPositive := Iff.rfl

alias ⟨_, IsPositive.toLinearMap⟩ := isPositive_toLinearMap_iff
/-
**ContinuousLinearMap.IsPositive.re_inner_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ RCLike.re (inner 𝕜 x (T x))
参数：x : E；inner 𝕜 x (T x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.re_inner_nonneg_right`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `ContinuousLinearMap.IsPositive.toLinearMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   (T : E →L[𝕜] E), T.IsPo…
-/
theorem IsPositive.re_inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪x, T x⟫ := hT.toLinearMap.re_inner_nonneg_right x

/-- An operator is positive iff it is symmetric and `0 ≤ ⟪T x, x⟫`.

For the version with `IsSelfAdjoint` instead of `IsSymmetric`, see
`ContinuousLinearMap.isPositive_iff'`. -/
/-
**ContinuousLinearMap.isPositive_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isPositive_iff (T : E ->L[𝕜] E) : IsPositive T ↔ T.IsSymmetric ∧ forall x,
 0 <= ⟪T x, x⟫
参数：T : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isPositive_iff`：isPositive_iff (T : E ->ₗ[𝕜] E) : IsPositive T
 ↔ IsSymmetric T ∧ forall x, 0 <= ⟪T x, x⟫

--- 原说明 ---
An operator is positive iff it is symmetric and `0 ≤ ⟪T x, x⟫`.

For the version with `IsSelfAdjoint` instead of `IsSymmetric`, see
`ContinuousLinearMap.isPositive_iff'`.
-/
theorem isPositive_iff (T : E →L[𝕜] E) :
    IsPositive T ↔ T.IsSymmetric ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := LinearMap.isPositive_iff _

/-- An operator is positive iff it is self-adjoint and `0 ≤ ⟪T x, x⟫`.

For the version with `IsSymmetric` instead of `IsSelfAdjoint`, see
`ContinuousLinearMap.isPositive_iff`. -/
/-
**ContinuousLinearMap.isPositive_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：isPositive_iff' [CompleteSpace E] (T : E ->L[𝕜] E) : IsPositive T ↔ IsSelf
Adjoint T ∧ forall x, 0 <= ⟪T x, x⟫
参数：T : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An operator is positive iff it is self-adjoint and `0 ≤ ⟪T x, x⟫`.

For the version with `IsSymmetric` instead of `IsSelfAdjoint`, see
`ContinuousLinearMap.isPositive_iff`.
-/
theorem isPositive_iff' [CompleteSpace E] (T : E →L[𝕜] E) :
    IsPositive T ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp [isSelfAdjoint_iff_isSymmetric, isPositive_iff]
/-
**ContinuousLinearMap.IsPositive.inner_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ inner 𝕜 (T x) x
参数：x : E；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.inner_nonneg_left`：∀ {𝕜 : Type u_1} {E : Type u_2} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 
E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `ContinuousLinearMap.IsPositive.toLinearMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   (T : E →L[𝕜] E), T.IsPo…
-/
theorem IsPositive.inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪T x, x⟫ := hT.toLinearMap.inner_nonneg_left x
/-
**ContinuousLinearMap.IsPositive.inner_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → ∀ (x 
: E), 0 ≤ inner 𝕜 x (T x)
参数：x : E；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.inner_nonneg_right`：∀ {𝕜 : Type u_1} {E : Type u_2}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜
 E]   {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `ContinuousLinearMap.IsPositive.toLinearMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   (T : E →L[𝕜] E), T.IsPo…
-/
theorem IsPositive.inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ := hT.toLinearMap.inner_nonneg_right x

@[simp]
/-
**ContinuousLinearMap.isPositive_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：isPositive_zero : IsPositive (0 : E ->L[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isPositive_zero`：isPositive_zero : IsPositive (0 : E ->ₗ[𝕜] E)
-/
theorem isPositive_zero : IsPositive (0 : E →L[𝕜] E) := LinearMap.isPositive_zero

@[simp]
/-
**ContinuousLinearMap.isPositive_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：isPositive_id : IsPositive (.id 𝕜 E : E ->L[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isPositive_id`：isPositive_id : IsPositive (id : E ->ₗ[𝕜] E)
-/
theorem isPositive_id : IsPositive (.id 𝕜 E : E →L[𝕜] E) := LinearMap.isPositive_id

@[simp]
/-
**ContinuousLinearMap.isPositive_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isPositive_one : IsPositive (1 : E ->L[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isPositive_one`：isPositive_one : IsPositive (1 : E ->ₗ[𝕜] E)
-/
theorem isPositive_one : IsPositive (1 : E →L[𝕜] E) := LinearMap.isPositive_one

@[simp]
/-
**ContinuousLinearMap.isPositive_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：isPositive_natCast {n : Nat} : IsPositive (n : E ->L[𝕜] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContinuousLinearMap.isPositive_toLinearMap_iff`：isPositive_toLinearMap_i
ff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive
· 使用定理 `LinearMap.isPositive_natCast`：isPositive_natCast {n : Nat} : IsPositive 
(n : E ->ₗ[𝕜] E)
-/
theorem isPositive_natCast {n : ℕ} : IsPositive (n : E →L[𝕜] E) :=
  (isPositive_toLinearMap_iff _).mp LinearMap.isPositive_natCast

@[simp]
/-
**ContinuousLinearMap.isPositive_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：isPositive_ofNat {n : Nat} [n.AtLeastTwo] : IsPositive (ofNat(n) : E ->L[𝕜
] E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isPositive_natCast`：isPositive_natCast {n : Nat} : I
sPositive (n : E ->L[𝕜] E)
-/
theorem isPositive_ofNat {n : ℕ} [n.AtLeastTwo] : IsPositive (ofNat(n) : E →L[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
/-
**ContinuousLinearMap.IsPositive.add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S : E →L[𝕜] E}, T.IsPositive → S.I
sPositive → (T + S).IsPositive
参数：T + S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContinuousLinearMap.isPositive_toLinearMap_iff`：isPositive_toLinearMap_i
ff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive
· 使用定理 `LinearMap.IsPositive.add`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike
 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S : E 
→ₗ[𝕜] E}, T.Is…
· 使用定理 `ContinuousLinearMap.IsPositive.toLinearMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   (T : E →L[𝕜] E), T.IsPo…
-/
theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive :=
  (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.add hS.toLinearMap)
/-
**ContinuousLinearMap.isPositive_sum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isPositive_sum {ι : Type*} {T : ι -> (E ->L[𝕜] E)} (s : Finset ι) (hT : fo
rall i in s, (T i).IsPositive) : (∑ i in s, T i).IsPositive
参数：E ->L[𝕜] E；s : Finset ι；hT : forall i in s, (T i).IsPositive。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContinuousLinearMap.isPositive_toLinearMap_iff`：isPositive_toLinearMap_i
ff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toLinearMap_sum`：toLinearMap_sum {ι : Type*} (t : Fi
nset ι) (f : ι -> M₁ ->SL[σ₁₂] M₂) : ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ ->ₛₗ
[σ₁₂] M₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearMap.isPositive_sum`：isPositive_sum {ι : Type*} {T : ι -> (E ->ₗ[𝕜]
 E)} (s : Finset ι) (hT : forall i in s, (T i).IsPositive) : (∑ i in s, T i).IsP
ositive
-/
theorem isPositive_sum {ι : Type*} {T : ι → (E →L[𝕜] E)} (s : Finset ι)
    (hT : ∀ i ∈ s, (T i).IsPositive) : (∑ i ∈ s, T i).IsPositive :=
  (isPositive_toLinearMap_iff _).mp <| by simp [LinearMap.isPositive_sum s hT]

@[aesop safe apply]
/-
**ContinuousLinearMap.IsPositive.smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPositive → ∀ {c 
: 𝕜}, 0 ≤ c → (c • T).IsPositive
参数：c • T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `ContinuousLinearMap.isPositive_toLinearMap_iff`：isPositive_toLinearMap_i
ff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive
· 使用定理 `LinearMap.IsPositive.smul_of_nonneg`：∀ {𝕜 : Type u_1} {E : Type u_2} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  {T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `ContinuousLinearMap.IsPositive.toLinearMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   (T : E →L[𝕜] E), T.IsPo…
-/
theorem IsPositive.smul_of_nonneg {T : E →L[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).IsPositive :=
  (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.smul_of_nonneg hc)

@[aesop safe apply]
/-
**ContinuousLinearMap.IsPositive.conj_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_3 : InnerProductS
pace 𝕜 E] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : CompleteSpace E] [inst_6 
: CompleteSpace F] {T : E →L[𝕜] E},   T.IsPositive → ∀ (S : E →L[𝕜] F), (S ∘SL T
 ∘SL ContinuousLinearMap.adjoint S).IsPositive
参数：S : E →L[𝕜] F；S ∘SL T ∘SL ContinuousLinearMap.adjoint S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `ContinuousLinearMap.isPositive_def'`：isPositive_def' [CompleteSpace E] {
T : E ->L[𝕜] E} : T.IsPositive ↔ IsSelfAdjoint T ∧ forall x, 0 <= T.reApplyInner
Self x
· 使用定理 `IsSelfAdjoint.conj_adjoint`：conj_adjoint {T : E ->L[𝕜] E} (hT : IsSelfAd
joint T) (S : E ->L[𝕜] F) : IsSelfAdjoint (S ∘L T ∘L S.adjoint)
· 使用定理 `ContinuousLinearMap.IsPositive.isSelfAdjoint`：∀ {𝕜 : Type u_1} {E : Type
 u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   [inst_3 : CompleteSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.reApplyInnerSelf.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductS
pace 𝕜 E]   (T : E →L[𝕜] E) (x …
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用定理 `ContinuousLinearMap.IsPositive.re_inner_nonneg_left`：∀ {𝕜 : Type u_1} {E
 : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerPr
oductSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
-/
theorem IsPositive.conj_adjoint [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] E}
    (hT : T.IsPositive) (S : E →L[𝕜] F) : (S ∘L T ∘L S†).IsPositive := by
  refine isPositive_def'.mpr ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf, comp_apply, ← adjoint_inner_right]
  exact hT.re_inner_nonneg_left _
/-
**ContinuousLinearMap.isPositive_self_comp_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：isPositive_self_comp_adjoint [CompleteSpace E] [CompleteSpace F] (S : E ->
L[𝕜] F) : (S ∘L S†).IsPositive
参数：S : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsPositive.conj_adjoint`：∀ {𝕜 : Type u_1} {E : Type 
u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedAddCommGroup F] [inst_3 :…
· 使用定理 `ContinuousLinearMap.isPositive_one`：isPositive_one : IsPositive (1 : E -
>L[𝕜] E)
-/
theorem isPositive_self_comp_adjoint [CompleteSpace E] [CompleteSpace F] (S : E →L[𝕜] F) :
    (S ∘L S†).IsPositive := by
  simpa using! isPositive_one.conj_adjoint S

@[aesop safe apply]
/-
**ContinuousLinearMap.IsPositive.adjoint_conj** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_3 : InnerProductS
pace 𝕜 E] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : CompleteSpace E] [inst_6 
: CompleteSpace F] {T : E →L[𝕜] E},   T.IsPositive → ∀ (S : F →L[𝕜] E), (Continu
ousLinearMap.adjoint S ∘SL T ∘SL S).IsPositive
参数：S : F →L[𝕜] E；ContinuousLinearMap.adjoint S ∘SL T ∘SL S。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用定理 `ContinuousLinearMap.IsPositive.conj_adjoint`：∀ {𝕜 : Type u_1} {E : Type 
u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedAddCommGroup F] [inst_3 :…
-/
theorem IsPositive.adjoint_conj [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] E}
    (hT : T.IsPositive) (S : F →L[𝕜] E) : (S† ∘L T ∘L S).IsPositive := by
  convert! hT.conj_adjoint (S†)
  rw [adjoint_adjoint]
/-
**ContinuousLinearMap.isPositive_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：isPositive_adjoint_comp_self [CompleteSpace E] [CompleteSpace F] (S : E ->
L[𝕜] F) : (S† ∘L S).IsPositive
参数：S : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.IsPositive.adjoint_conj`：∀ {𝕜 : Type u_1} {E : Type 
u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedAddCommGroup F] [inst_3 :…
· 使用定理 `ContinuousLinearMap.isPositive_one`：isPositive_one : IsPositive (1 : E -
>L[𝕜] E)
-/
theorem isPositive_adjoint_comp_self [CompleteSpace E] [CompleteSpace F] (S : E →L[𝕜] F) :
    (S† ∘L S).IsPositive := by
  simpa using! isPositive_one.adjoint_conj S

section LinearMap
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

@[aesop safe apply]
/-
**ContinuousLinearMap._root_.LinearMap.IsPositive.conj_adjoint** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.IsPositive.conj_adjoint {T : E →ₗ[𝕜] E}
    (hT : T.IsPositive) (S : E →ₗ[𝕜] F) : (S ∘ₗ T ∘ₗ S.adjoint).IsPositive := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa [← isPositive_toContinuousLinearMap_iff] using!
    ((T.isPositive_toContinuousLinearMap_iff.mpr hT).conj_adjoint S.toContinuousLinearMap)
/-
**ContinuousLinearMap._root_.LinearMap.isPositive_self_comp_adjoint** 是 Mathlib 
中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.isPositive_self_comp_adjoint (S : E →ₗ[𝕜] F) :
    (S ∘ₗ S.adjoint).IsPositive := by
  simpa using! LinearMap.isPositive_one.conj_adjoint S

@[aesop safe apply]
/-
**ContinuousLinearMap._root_.LinearMap.IsPositive.adjoint_conj** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.IsPositive.adjoint_conj {T : E →ₗ[𝕜] E}
    (hT : T.IsPositive) (S : F →ₗ[𝕜] E) : (S.adjoint ∘ₗ T ∘ₗ S).IsPositive := by
  convert! hT.conj_adjoint S.adjoint
  rw [LinearMap.adjoint_adjoint]
/-
**ContinuousLinearMap._root_.LinearMap.isPositive_adjoint_comp_self** 是 Mathlib 
中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.isPositive_adjoint_comp_self (S : E →ₗ[𝕜] F) :
    (S.adjoint ∘ₗ S).IsPositive := by
  simpa using! LinearMap.isPositive_one.adjoint_conj S

end LinearMap

/-
**ContinuousLinearMap.IsPositive.conj_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (U : Submodule 𝕜 E) {T : E →L[𝕜] E}, 
  T.IsPositive → ∀ [inst_3 : U.HasOrthogonalProjection], (U.starProjection ∘SL T
 ∘SL U.starProjection).IsPositive
参数：U : Submodule 𝕜 E；U.starProjection ∘SL T ∘SL U.starProjection。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.starProjection_isSymmetric`：starProjection_isSymmetric [K.HasO
rthogonalProjection] : (K.starProjection : E ->ₗ[𝕜] E).IsSymmetric
· 使用定理 `ContinuousLinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousLinearMap.IsPositive.inner_nonneg_right`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsPositive.conj_starProjection (U : Submodule 𝕜 E) {T : E →L[𝕜] E} (hT : T.IsPositive)
    [U.HasOrthogonalProjection] :
    (U.starProjection ∘L T ∘L U.starProjection).IsPositive := by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [← coe_coe, U.starProjection_isSymmetric _, hT.isSymmetric _,
    U.starProjection_isSymmetric _, ← U.starProjection_isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]
/-
**ContinuousLinearMap.IsPositive.orthogonalProjectionOnto_comp** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E},   T.IsPositive →    
 ∀ (U : Submodule 𝕜 E) [inst_3 : U.HasOrthogonalProjection],       (U.orthogonal
ProjectionOnto ∘SL T ∘SL U.subtypeL).IsPositive
参数：U : Submodule 𝕜 E；U.orthogonalProjectionOnto ∘SL T ∘SL U.subtypeL。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right`：inner_orthogon
alProjectionOnto_eq_of_mem_right [K.HasOrthogonalProjection] (u : K) (v : E) : ⟪
K.orthogonalProjectionOnto v, u⟫ = ⟪v, u⟫
· 使用定理 `Submodule.subtypeL_apply`：subtypeL_apply (p : Submodule R M) (x : p) : p
.subtypeL x = x
· 使用定理 `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`：inner_orthogona
lProjectionOnto_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) : ⟪u,
 K.orthogonalProjectionOnto v⟫ = ⟪(u : E), v⟫
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousLinearMap.IsPositive.inner_nonneg_right`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsPositive.orthogonalProjectionOnto_comp {T : E →L[𝕜] E} (hT : T.IsPositive)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL).IsPositive := by
  simp only [isPositive_iff, IsSymmetric, toLinearMap_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, comp_apply]
  simp_rw [U.inner_orthogonalProjectionOnto_eq_of_mem_right, Submodule.subtypeL_apply,
    U.inner_orthogonalProjectionOnto_eq_of_mem_left, ← coe_coe, hT.isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

@[deprecated (since := "2026-05-05")] alias IsPositive.orthogonalProjection_comp :=
  IsPositive.orthogonalProjectionOnto_comp

open scoped NNReal
/-
**ContinuousLinearMap.antilipschitz_of_forall_le_inner_map** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：antilipschitz_of_forall_le_inner_map {H : Type*} [NormedAddCommGroup H] [I
nnerProductSpace 𝕜 H] (f : H ->L[𝕜] H) {c : Real>=0} (hc : 0 < c) (h : forall x,
 ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖) : AntilipschitzWith c⁻¹ f
参数：f : H ->L[𝕜] H；hc : 0 < c；h : forall x, ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.antilipschitz_of_bound`：antilipschitz_of_bound (f : 
E ->SL[σ] F) {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖) : AntilipschitzWith 
K f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_inv`：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用引理 `RCLike.instMulPosReflectLE`：instMulPosReflectLE : MulPosReflectLE K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RCLike.toPosMulReflectLT`：toPosMulReflectLT : PosMulReflectLT K where el
im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
（共 33 条，此处仅展示前 30 条）
-/
lemma antilipschitz_of_forall_le_inner_map {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (f : H →L[𝕜] H) {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : AntilipschitzWith c⁻¹ f := by
  refine f.antilipschitz_of_bound (K := c⁻¹) fun x ↦ ?_
  rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀ (by exact_mod_cast hc)]
  simp_rw [sq, mul_assoc] at h
  by_cases hx0 : x = 0
  · simp [hx0]
  · apply (map_le_map_iff <| OrderIso.mulLeft₀ ‖x‖ (norm_pos_iff.mpr hx0)).mp
    exact (h x).trans <| (norm_inner_le_norm _ _).trans <| (mul_comm _ _).le
/-
**ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：isUnit_of_forall_le_norm_inner_map [CompleteSpace E] (f : E ->L[𝕜] E) {c :
 Real>=0} (hc : 0 < c) (h : forall x, ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖) : IsUnit f
参数：f : E ->L[𝕜] E；hc : 0 < c；h : forall x, ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.isUnit_iff_bijective`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] [CompleteSpa…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用引理 `ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz`：bijecti
ve_iff_dense_range_and_antilipschitz (f : E ->SL[σ] F) : Bijective f ↔ f.range.t
opologicalClosure = ⊤ ∧ exists c, AntilipschitzWith c…
· 使用引理 `ContinuousLinearMap.antilipschitz_of_forall_le_inner_map`：antilipschitz_
of_forall_le_inner_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H
] (f : H ->L[𝕜] H) {c : Real>=0} (hc : 0 < c) …
· 使用定理 `Submodule.topologicalClosure_eq_top_iff`：topologicalClosure_eq_top_iff [
CompleteSpace E] : K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
lemma isUnit_of_forall_le_norm_inner_map [CompleteSpace E] (f : E →L[𝕜] E) {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : IsUnit f := by
  rw [isUnit_iff_bijective, bijective_iff_dense_range_and_antilipschitz]
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

section Complex
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

/-
**ContinuousLinearMap.isPositive_iff_complex** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：isPositive_iff_complex (T : E' ->L[Complex] E') : IsPositive T ↔ forall x,
 (re ⟪T x, x⟫_Complex : Complex) = ⟪T x, x⟫_Complex ∧ 0 <= re ⟪T x, x⟫_Complex
参数：T : E' ->L[Complex] E'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPositive_iff_complex (T : E' →L[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp [← isPositive_toLinearMap_iff, LinearMap.isPositive_iff_complex]

end Complex

section PartialOrder

/-- The (Loewner) partial order on continuous linear maps on a Hilbert space determined by
`f ≤ g` if and only if `g - f` is a positive linear map (in the sense of
`ContinuousLinearMap.IsPositive`). With this partial order, the continuous linear maps form a
`StarOrderedRing`. -/
/-
**ContinuousLinearMap.instLoewnerPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：instLoewnerPartialOrder : PartialOrder (E ->L[𝕜] E) where le f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (Loewner) partial order on continuous linear maps on a Hilbert space determi
ned by
`f ≤ g` if and only if `g - f` is a positive linear map (in the sense of
`ContinuousLinearMap.IsPositive`). With this partial order, the continuous linea
r maps form a
`StarOrderedRing`.
-/
instance instLoewnerPartialOrder : PartialOrder (E →L[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm _ _ h₁ h₂ := coe_inj.mp (le_antisymm h₁.toLinearMap h₂.toLinearMap)
/-
**ContinuousLinearMap.le_def** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：le_def (f g : E ->L[𝕜] E) : f <= g ↔ (g - f).IsPositive
参数：f g : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def (f g : E →L[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl
/-
**ContinuousLinearMap.coe_le_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：coe_le_coe_iff (f g : E ->L[𝕜] E) : (f : E ->ₗ[𝕜] E) <= g ↔ f <= g
参数：f g : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.isPositive_toLinearMap_iff`：isPositive_toLinearMap_i
ff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma coe_le_coe_iff (f g : E →L[𝕜] E) :
    (f : E →ₗ[𝕜] E) ≤ g ↔ f ≤ g :=
  isPositive_toLinearMap_iff (g - f)
/-
**ContinuousLinearMap.nonneg_iff_isPositive** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：nonneg_iff_isPositive (f : E ->L[𝕜] E) : 0 <= f ↔ f.IsPositive
参数：f : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `ContinuousLinearMap.le_def`：le_def (f g : E ->L[𝕜] E) : f <= g ↔ (g - f)
.IsPositive
-/
lemma nonneg_iff_isPositive (f : E →L[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

/-- An idempotent operator is positive if and only if it is self-adjoint. -/
@[grind →]
/-
**ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint** 是 Mathlib 
中的一个定理，位于命名空间 `ContinuousLinearMap.IsIdempotentElem`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E] {p : E →L[
𝕜] E}, IsIdempotentElem p → (p.IsPositive ↔ IsSelfAdjoint p)
参数：p.IsPositive ↔ IsSelfAdjoint p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.isPositive_toLinearMap_iff`：isPositive_toLinearMap_i
ff (T : E ->L[𝕜] E) : (T : E ->ₗ[𝕜] E).IsPositive ↔ T.IsPositive
· 使用定理 `LinearMap.IsIdempotentElem.isPositive_iff_isSymmetric`：∀ {𝕜 : Type u_1} 
{E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : Inner
ProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdem…
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   [inst_3 : CompleteSpace…

--- 原说明 ---
An idempotent operator is positive if and only if it is self-adjoint.
-/
theorem IsIdempotentElem.isPositive_iff_isSelfAdjoint [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : p.IsPositive ↔ IsSelfAdjoint p := by
  rw [← isPositive_toLinearMap_iff, IsIdempotentElem.isPositive_iff_isSymmetric hp.toLinearMap]
  exact isSelfAdjoint_iff_isSymmetric.symm

/-- A star projection operator is positive.

The proof of this will soon be simplified to `IsStarProjection.nonneg` when we
have `StarOrderedRing (E →L[𝕜] E)`. -/
@[aesop 10% apply, grind →]
/-
**ContinuousLinearMap.IsPositive.of_isStarProjection** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E] {p : E →L[
𝕜] E}, IsStarProjection p → p.IsPositive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint`：∀ {𝕜 
: Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [in
st_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace…
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p

--- 原说明 ---
A star projection operator is positive.

The proof of this will soon be simplified to `IsStarProjection.nonneg` when we
have `StarOrderedRing (E →L[𝕜] E)`.
-/
theorem IsPositive.of_isStarProjection [CompleteSpace E] {p : E →L[𝕜] E}
    (hp : IsStarProjection p) : p.IsPositive :=
  hp.isIdempotentElem.isPositive_iff_isSelfAdjoint.mpr hp.isSelfAdjoint

/-- For an idempotent operator `p`, TFAE:
* `(range p)ᗮ = ker p`
* `p` is normal
* `p` is self-adjoint
* `p` is positive -/
/-
**ContinuousLinearMap.IsIdempotentElem.TFAE** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap.IsIdempotentElem`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E] {p : E →L[
𝕜] E},   IsIdempotentElem p → [(↑p).rangeᗮ = (↑p).ker, IsStarNormal p, IsSelfAdj
oint p, p.IsPositive].TFAE
参数：↑p；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`：∀ {
𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [
inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3…
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint`：∀ {𝕜 
: Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [in
st_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace…
· 使用定理 `LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range`：∀ {𝕜 : Type
 u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 :
 InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdem…
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   [inst_3 : CompleteSpace…
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
For an idempotent operator `p`, TFAE:
* `(range p)ᗮ = ker p`
* `p` is normal
* `p` is self-adjoint
* `p` is positive
-/
theorem IsIdempotentElem.TFAE [CompleteSpace E] {p : E →L[𝕜] E} (hp : IsIdempotentElem p) :
    [p.rangeᗮ = p.ker,
      IsStarNormal p,
      IsSelfAdjoint p,
      p.IsPositive].TFAE := by
  tfae_have 2 ↔ 3 := hp.isSelfAdjoint_iff_isStarNormal.symm
  tfae_have 3 ↔ 4 := hp.isPositive_iff_isSelfAdjoint.symm
  tfae_have 3 ↔ 1 := p.isSelfAdjoint_iff_isSymmetric.eq ▸
    (LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hp.toLinearMap)
  tfae_finish

end ContinuousLinearMap

/-- `U.starProjection ≤ V.starProjection` iff `U ≤ V`. -/
/-
**Submodule.starProjection_le_starProjection_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.starProjection_le_starProjection_iff {U V : Submodule 𝕜 E} [U.Ha
sOrthogonalProjection] [V.HasOrthogonalProjection] : U.starProjection <= V.starP
rojection ↔ U <= V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetricProjection.le_iff_range_le_range`：∀ {𝕜 : Type u_1} 
{E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : Inner
ProductSpace 𝕜 E]   {p q : E →ₗ[𝕜] E}, p.Is…
· 使用定理 `Submodule.isSymmetricProjection_starProjection`：isSymmetricProjection_st
arProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : U.starProjection.
IsSymmetricProjection
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.range_projection`：range_projection (hpq : IsCompl p q) : range
 (p.projection q hpq) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`U.starProjection ≤ V.starProjection` iff `U ≤ V`.
-/
theorem Submodule.starProjection_le_starProjection_iff {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection ≤ V.starProjection ↔ U ≤ V := by
  simp_rw [← coe_le_coe_iff, isSymmetricProjection_starProjection _
      |>.le_iff_range_le_range <| isSymmetricProjection_starProjection _,
    toLinearMap_starProjection_eq_isComplProjection, range_projection]

/-- `U.starProjection = V.starProjection` iff `U = V`. -/
/-
**Submodule.starProjection_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.starProjection_inj {U V : Submodule 𝕜 E} [U.HasOrthogonalProject
ion] [V.HasOrthogonalProjection] : U.starProjection = V.starProjection ↔ U = V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`U.starProjection = V.starProjection` iff `U = V`.
-/
theorem Submodule.starProjection_inj {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection = V.starProjection ↔ U = V := by
  simp only [le_antisymm_iff, ← starProjection_le_starProjection_iff]
/-
**LinearMap.IsPositive.toLinearMap_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.IsPositive.toLinearMap_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsPositive) 
: T.symm.IsPositive
参数：hT : T.IsPositive。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.toLinearMap_symm`：LinearMap.IsSymmetric.toLinearMa
p_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric) : .symm T.symm.IsSymmetric
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
-/
theorem LinearMap.IsPositive.toLinearMap_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsPositive) :
    T.symm.IsPositive := by
  refine ⟨hT.isSymmetric.toLinearMap_symm, fun x ↦ ?_⟩
  have := by simpa using hT.2 (T.symm.toLinearMap x)
  rwa [← T.symm.coe_toLinearMap, ← hT.isSymmetric.toLinearMap_symm] at this
/-
**LinearEquiv.isPositive_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E ≃ₗ[𝕜] E}, (↑T.symm).IsPositive
 ↔ (↑T).IsPositive
参数：↑T.symm；↑T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPositive.toLinearMap_symm`：LinearMap.IsPositive.toLinearMap_
symm {T : E ≃ₗ[𝕜] E} (hT : T.IsPositive) : T.symm.IsPositive
-/
@[simp] theorem LinearEquiv.isPositive_symm_iff {T : E ≃ₗ[𝕜] E} :
    T.symm.IsPositive ↔ T.IsPositive := ⟨.toLinearMap_symm, .toLinearMap_symm⟩
/-
**InnerProductSpace.isPositive_rankOne_self** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : E), (((InnerProductSpace.rankOne
 𝕜) x) x).IsPositive
参数：x : E；((InnerProductSpace.rankOne 𝕜) x) x。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma InnerProductSpace.isPositive_rankOne_self (x : E) :
    (rankOne 𝕜 x x).IsPositive := by
  simp_rw [ContinuousLinearMap.isPositive_iff, isSymmetric_rankOne_self, rankOne_apply,
    inner_smul_left, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_nonneg]
  simp

/-- In finite-dimensional spaces, a continuous linear map is positive iff it is equal to the sum
of rank-one positive operators. -/
/-
**ContinuousLinearMap.isPositive_iff_eq_sum_rankOne** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContinuousLinearMap.isPositive_iff_eq_sum_rankOne [FiniteDimensional 𝕜 E] 
{T : E ->L[𝕜] E} : T.IsPositive ↔ exists (m : Nat) (u : Fin m -> E), T = ∑ i : F
in m, rankOne 𝕜 (u i) (u i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →L[𝕜] E}, T.IsPo…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LinearMap.IsPositive.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {
T : E →ₗ[𝕜] E}, T.IsPo…
· 使用定理 `ContinuousLinearMap.IsPositive.toLinearMap`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   (T : E →L[𝕜] E), T.IsPo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `LinearMap.IsPositive.nonneg_eigenvalues`：∀ {𝕜 : Type u_1} {E : Type u_2}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜
 E]   [inst_3 : FiniteDimensi…
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `LinearMap.IsSymmetric.apply_eigenvectorBasis`：apply_eigenvectorBasis (hT
 : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : T (hT.eigenvectorB
asis hn i) = (hT.eigenvalues hn i …
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
In finite-dimensional spaces, a continuous linear map is positive iff it is equa
l to the sum
of rank-one positive operators.
-/
theorem ContinuousLinearMap.isPositive_iff_eq_sum_rankOne [FiniteDimensional 𝕜 E] {T : E →L[𝕜] E} :
    T.IsPositive ↔ ∃ (m : ℕ) (u : Fin m → E), T = ∑ i : Fin m, rankOne 𝕜 (u i) (u i) := by
  refine ⟨fun hT ↦ ?_, fun ⟨m, u, hT⟩ ↦ hT ▸ isPositive_sum _ fun _ _ ↦ isPositive_rankOne_self _⟩
  let a (i : Fin (Module.finrank 𝕜 E)) : E :=
    ((hT.isSymmetric.eigenvalues rfl i).sqrt : 𝕜) • hT.isSymmetric.eigenvectorBasis rfl i
  refine ⟨Module.finrank 𝕜 E, a, ext fun _ ↦ ?_⟩
  simp_rw [_root_.sum_apply, rankOne_apply, a, inner_smul_left, smul_smul, mul_assoc, conj_ofReal,
    mul_comm (⟪_, _⟫_𝕜), ← mul_assoc, ← ofReal_mul,
    ← Real.sqrt_mul (hT.toLinearMap.nonneg_eigenvalues rfl _),
    Real.sqrt_mul_self (hT.toLinearMap.nonneg_eigenvalues rfl _), mul_comm _ (⟪_, _⟫_𝕜),
    ← smul_eq_mul, smul_assoc, ← hT.isSymmetric.apply_eigenvectorBasis, ← map_smul, ← map_sum,
    ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr, coe_coe]
/-
**Matrix.posSemidef_iff_eq_sum_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.posSemidef_iff_eq_sum_vecMulVec {n : Type*} [Finite n] {M : Matrix 
n n 𝕜} : M.PosSemidef ↔ exists (m : Nat) (v : Fin m -> (n -> 𝕜)), M = ∑ i, vecMu
lVec (v i) (star (v i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isPositive_toEuclideanLin_iff`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜]
 {n : Type u_4} [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n n 𝕜}
,   (Matrix.toEuclideanLin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LinearMap.isPositive_toContinuousLinearMap_iff`：∀ {𝕜 : Type u_1} {E : Ty
pe u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduct
Space 𝕜 E]   [inst_3 : FiniteDimensi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`：ContinuousLinearMap.i
sPositive_iff_eq_sum_rankOne [FiniteDimensional 𝕜 E] {T : E ->L[𝕜] E} : T.IsPosi
tive ↔ exists (m : Nat) (u : Fin m -> E…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.toLinearMap_sum`：toLinearMap_sum {ι : Type*} (t : Fi
nset ι) (f : ι -> M₁ ->SL[σ₁₂] M₂) : ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ ->ₛₗ
[σ₁₂] M₂)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `InnerProductSpace.symm_toEuclideanLin_rankOne`：InnerProductSpace.symm_to
EuclideanLin_rankOne {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Decidab
leEq n] (x : EuclideanSpace 𝕜 m) (y…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem Matrix.posSemidef_iff_eq_sum_vecMulVec {n : Type*} [Finite n] {M : Matrix n n 𝕜} :
    M.PosSemidef ↔ ∃ (m : ℕ) (v : Fin m → (n → 𝕜)), M = ∑ i, vecMulVec (v i) (star (v i)) := by
  classical
  have := Fintype.ofFinite n
  rw [← isPositive_toEuclideanLin_iff, ← isPositive_toContinuousLinearMap_iff,
    isPositive_iff_eq_sum_rankOne]
  simp_rw [eq_comm, ← LinearEquiv.symm_apply_eq, coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_sum, map_sum, symm_toEuclideanLin_rankOne, eq_comm]
  exact ⟨fun ⟨m, u, hu⟩ ↦ ⟨m, fun i ↦ (u i).ofLp, hu⟩,
    fun ⟨m, u, hu⟩ ↦ ⟨m, fun i ↦ WithLp.toLp 2 (u i), hu⟩⟩
