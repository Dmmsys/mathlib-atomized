/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `IsSelfAdjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `LinearMap.IsSymmetric`: a (not necessarily bounded) operator on an inner product space is
  symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `IsSymmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/

@[expose] public section


open RCLike

open ComplexConjugate

section Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-! ### Symmetric operators -/


/-- A (not necessarily bounded) operator on an inner product space is symmetric, if for all
`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/
/-
**LinearMap.IsSymmetric** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsSymmetric (T : E ->ₗ[𝕜] E) : Prop
参数：T : E ->ₗ[𝕜] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (not necessarily bounded) operator on an inner product space is symmetric, if 
for all
`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`.
-/
def IsSymmetric (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫

section Real

/-- An operator `T` on an inner product space is symmetric if and only if it is
`LinearMap.IsSelfAdjoint` with respect to the sesquilinear form given by the inner product. -/
/-
**LinearMap.isSymmetric_iff_sesqForm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymmetric_iff_sesqForm (T : E ->ₗ[𝕜] E) : T.IsSymmetric ↔ LinearMap.IsSe
lfAdjoint (R
参数：T : E ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An operator `T` on an inner product space is symmetric if and only if it is
`LinearMap.IsSelfAdjoint` with respect to the sesquilinear form given by the inn
er product.
-/
theorem isSymmetric_iff_sesqForm (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ LinearMap.IsSelfAdjoint (R := 𝕜) (M := E) (LinearMap.flip (innerₛₗ 𝕜)) T :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

end Real

/-
**LinearMap.IsSymmetric.conj_inner_sym** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSy
mmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ (x y : E), (starRingEnd 𝕜) (inner 𝕜 (T x) y) = inner 𝕜 (T y) x
参数：x y : E；starRingEnd 𝕜；inner 𝕜 (T x) y；T y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
-/
theorem IsSymmetric.conj_inner_sym {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E) :
    conj ⟪T x, y⟫ = ⟪T y, x⟫ := by rw [hT x y, inner_conj_symm]

@[simp]
/-
**LinearMap.IsSymmetric.apply_clm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetr
ic`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, (↑T).IsSymmetric
 → ∀ (x y : E), inner 𝕜 (T x) y = inner 𝕜 x (T y)
参数：↑T；x y : E；T x；T y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSymmetric.apply_clm {T : E →L[𝕜] E} (hT : IsSymmetric (T : E →ₗ[𝕜] E)) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ :=
  hT x y

@[simp]
/-
**LinearMap.IsSymmetric.zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   LinearMap.IsSymmetric 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
-/
protected theorem IsSymmetric.zero : (0 : E →ₗ[𝕜] E).IsSymmetric := fun x y =>
  (inner_zero_right x : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left y : ⟪0, y⟫ = 0)
/-
**LinearMap.IsSymmetric.id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   LinearMap.id.IsSymmetric
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma IsSymmetric.id : (.id : E →ₗ[𝕜] E).IsSymmetric := fun _ _ ↦ rfl
/-
**LinearMap.IsSymmetric.one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   LinearMap.IsSymmetric 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma IsSymmetric.one : (1 : E →ₗ[𝕜] E).IsSymmetric := fun _ _ ↦ rfl

@[aesop safe apply]
/-
**LinearMap.IsSymmetric.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S : E →ₗ[𝕜] E}, T.IsSymmetric 
→ S.IsSymmetric → (T + S).IsSymmetric
参数：T + S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.add_apply`：add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) 
x = f x + g x
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
-/
theorem IsSymmetric.add {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T + S).IsSymmetric := by
  intro x y
  rw [add_apply, inner_add_left, hT x y, hS x y, ← inner_add_right, add_apply]
/-
**LinearMap.isSymmetric_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymmetric_sum {ι : Type*} {T : ι -> (E ->ₗ[𝕜] E)} (s : Finset ι) (hT : f
orall i in s, (T i).IsSymmetric) : (∑ i in s, T i).IsSymmetric
参数：E ->ₗ[𝕜] E；s : Finset ι；hT : forall i in s, (T i).IsSymmetric。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem isSymmetric_sum {ι : Type*} {T : ι → (E →ₗ[𝕜] E)} (s : Finset ι)
    (hT : ∀ i ∈ s, (T i).IsSymmetric) : (∑ i ∈ s, T i).IsSymmetric := fun _ _ ↦ by
  simpa [sum_inner, inner_sum] using Finset.sum_congr rfl fun _ hi ↦ hT _ hi _ _

@[aesop safe apply]
/-
**LinearMap.IsSymmetric.sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S : E →ₗ[𝕜] E}, T.IsSymmetric 
→ S.IsSymmetric → (T - S).IsSymmetric
参数：T - S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
-/
theorem IsSymmetric.sub {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T - S).IsSymmetric := by
  intro x y
  rw [sub_apply, inner_sub_left, hT x y, hS x y, ← inner_sub_right, sub_apply]

@[aesop safe apply]
/-
**LinearMap.IsSymmetric.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {c : 𝕜}, (starRingEnd 𝕜) c = c → 
∀ {T : E →ₗ[𝕜] E}, T.IsSymmetric → (c • T).IsSymmetric
参数：starRingEnd 𝕜；c • T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSymmetric.smul {c : 𝕜} (hc : conj c = c) {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    c • T |>.IsSymmetric := by
  intro x y
  simp only [smul_apply, inner_smul_left, hc, hT x y, inner_smul_right]
/-
**LinearMap.IsSymmetric.natCast** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (n : ℕ), (↑n).IsSymmetric
参数：n : ℕ；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSymmetric.natCast (n : ℕ) : IsSymmetric (n : E →ₗ[𝕜] E) := fun x y => by
  simp [← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, inner_smul_right]
/-
**LinearMap.IsSymmetric.intCast** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric
`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (n : ℤ), (↑n).IsSymmetric
参数：n : ℤ；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSymmetric.intCast (n : ℤ) : IsSymmetric (n : E →ₗ[𝕜] E) := fun x y => by
  simp [← Int.cast_smul_eq_zsmul 𝕜, inner_smul_left, inner_smul_right]

@[aesop 30% apply]
/-
**LinearMap.IsSymmetric.mul_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSy
mmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {S T : E →ₗ[𝕜] E}, S.IsSymmetric 
→ T.IsSymmetric → Commute S T → (S * T).IsSymmetric
参数：S * T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
-/
lemma IsSymmetric.mul_of_commute {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hST : Commute S T) : (S * T).IsSymmetric :=
  fun _ _ ↦ by rw [Module.End.mul_apply, hS, hT, hST, Module.End.mul_apply]

@[aesop safe apply]
/-
**LinearMap.IsSymmetric.pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ (n : ℕ), (T ^ n).IsSymmetric
参数：n : ℕ；T ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Module.End.iterate_succ`：iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (
f' ^ n) f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.IsSymmetric.mul_of_commute`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {S T : E →ₗ[𝕜] E}, …
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma IsSymmetric.pow {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (n : ℕ) : (T ^ n).IsSymmetric := by
  refine Nat.le_induction (by simp [Module.End.one_eq_id]) (fun k _ ih ↦ ?_) n n.zero_le
  rw [Module.End.iterate_succ, ← Module.End.mul_eq_comp]
  exact ih.mul_of_commute hT <| .pow_left rfl k

/-- For a symmetric operator `T`, the function `fun x ↦ ⟪T x, x⟫` is real-valued. -/
@[simp]
/-
**LinearMap.IsSymmetric.coe_reApplyInnerSelf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E}, (↑T).IsSymmetric
 → ∀ (x : E), ↑(T.reApplyInnerSelf x) = inner 𝕜 (T x) x
参数：↑T；x : E；T.reApplyInnerSelf x；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.conj_eq_iff_real`：conj_eq_iff_real {z : K} : conj z = z ↔ exists 
r : Real, z = (r : K)
· 使用定理 `LinearMap.IsSymmetric.conj_inner_sym`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a symmetric operator `T`, the function `fun x ↦ ⟪T x, x⟫` is real-valued.
-/
theorem IsSymmetric.coe_reApplyInnerSelf_apply {T : E →L[𝕜] E} (hT : IsSymmetric (T : E →ₗ[𝕜] E))
    (x : E) : (T.reApplyInnerSelf x : 𝕜) = ⟪T x, x⟫ := by
  rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ⟪T x, x⟫ = r
  · simp [hr, T.reApplyInnerSelf_apply]
  rw [← conj_eq_iff_real]
  exact hT.conj_inner_sym x x

/-- If a symmetric operator preserves a submodule, its restriction to that submodule is
symmetric. -/
/-
**LinearMap.IsSymmetric.restrict_invariant** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.
IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ {V : Submodule 𝕜 E} (hV : ∀ v ∈ V, T v ∈ V), (T.restrict hV).IsSymmetric
参数：hV : ∀ v ∈ V, T v ∈ V；T.restrict hV。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a symmetric operator preserves a submodule, its restriction to that submodule
 is
symmetric.
-/
theorem IsSymmetric.restrict_invariant {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) {V : Submodule 𝕜 E}
    (hV : ∀ v ∈ V, T v ∈ V) : IsSymmetric (T.restrict hV) := fun v w => hT v w
/-
**LinearMap.IsSymmetric.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsS
ymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
(↑ℝ T).IsSymmetric
参数：↑ℝ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.restrictScalars`：IsScalarTower.restrictScalars [Module S M
] : letI
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSymmetric.restrictScalars {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    haveI := IsScalarTower.restrictScalars ℝ 𝕜 E
    (T.restrictScalars ℝ).IsSymmetric :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrictScalars ℝ]

@[simp]
/-
**LinearMap.IsSymmetric.im_inner_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ (x : E), RCLike.im (inner 𝕜 (T x) x) = 0
参数：x : E；inner 𝕜 (T x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.conj_eq_iff_im`：conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0
· 使用定理 `LinearMap.IsSymmetric.conj_inner_sym`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
-/
theorem IsSymmetric.im_inner_apply_self {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    im ⟪T x, x⟫ = 0 :=
  conj_eq_iff_im.mp <| hT.conj_inner_sym x x

@[simp]
/-
**LinearMap.IsSymmetric.im_inner_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ (x : E), RCLike.im (inner 𝕜 x (T x)) = 0
参数：x : E；inner 𝕜 x (T x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymmetric.im_inner_apply_self`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductS
pace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSymmetric.im_inner_self_apply {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    im ⟪x, T x⟫ = 0 := by
  simp [← hT x x, hT]

@[simp]
/-
**LinearMap.IsSymmetric.coe_re_inner_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ (x : E), ↑(RCLike.re (inner 𝕜 (T x) x)) = inner 𝕜 (T x) x
参数：x : E；RCLike.re (inner 𝕜 (T x) x)；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.conj_eq_iff_re`：conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) 
= z
· 使用定理 `LinearMap.IsSymmetric.conj_inner_sym`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
-/
theorem IsSymmetric.coe_re_inner_apply_self {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    re ⟪T x, x⟫ = ⟪T x, x⟫ :=
  conj_eq_iff_re.mp <| hT.conj_inner_sym x x

@[simp]
/-
**LinearMap.IsSymmetric.coe_re_inner_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → 
∀ (x : E), ↑(RCLike.re (inner 𝕜 x (T x))) = inner 𝕜 x (T x)
参数：x : E；RCLike.re (inner 𝕜 x (T x))；T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymmetric.coe_re_inner_apply_self`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSymmetric.coe_re_inner_self_apply {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    re ⟪x, T x⟫ = ⟪x, T x⟫ := by
  simp [← hT x x, hT]

/-- A symmetric projection is a symmetric idempotent. -/
@[mk_iff]
/-
**LinearMap.IsSymmetricProjection** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     [inst : RCLike 𝕜] → [inst_1 : Semi
normedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → (E →ₗ[𝕜] E) → Prop
参数：E →ₗ[𝕜] E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A symmetric projection is a symmetric idempotent.
-/
structure IsSymmetricProjection (T : E →ₗ[𝕜] E) : Prop where
  isIdempotentElem : IsIdempotentElem T
  isSymmetric : T.IsSymmetric

section Complex

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

attribute [local simp] map_ofNat in -- use `ofNat` simp theorem with bad keys
open scoped InnerProductSpace in
/-- A linear operator on a complex inner product space is symmetric precisely when
`⟪T v, v⟫_ℂ` is real for all v. -/
/-
**LinearMap.isSymmetric_iff_inner_map_self_real** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：isSymmetric_iff_inner_map_self_real (T : V ->ₗ[Complex] V) : IsSymmetric T
 ↔ forall v : V, conj ⟪T v, v⟫_Complex = ⟪T v, v⟫_Complex
参数：T : V ->ₗ[Complex] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.conj_inner_sym`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `inner_map_polarization`：inner_map_polarization (T : V ->ₗ[Complex] V) (x
 y : V) : ⟪T y, x⟫_Complex = (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_Co
mplex + Comp…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `star_div₀`：star_div₀ [CommGroupWithZero R] [StarMul R] (x y : R) : star 
(x / y) = star x / star y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `inner_map_polarization'`：inner_map_polarization' (T : V ->ₗ[Complex] V) 
(x y : V) : ⟪T x, y⟫_Complex = (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_
Complex - Com…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
A linear operator on a complex inner product space is symmetric precisely when
`⟪T v, v⟫_ℂ` is real for all v.
-/
theorem isSymmetric_iff_inner_map_self_real (T : V →ₗ[ℂ] V) :
    IsSymmetric T ↔ ∀ v : V, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ := by
  constructor
  · intro hT v
    apply IsSymmetric.conj_inner_sym hT
  · intro h x y
    rw [← inner_conj_symm x (T y)]
    rw [inner_map_polarization T x y]
    simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
    simp only [← starRingEnd_apply]
    rw [h (x + y), h (x - y), h (x + Complex.I • y), h (x - Complex.I • y)]
    simp only [Complex.conj_I]
    rw [inner_map_polarization']
    norm_num
    ring

end Complex

set_option backward.isDefEq.respectTransparency false in
/-- Polarization identity for symmetric linear maps.
See `inner_map_polarization` for the complex version without the symmetric assumption. -/
/-
**LinearMap.IsSymmetric.inner_map_polarization** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E},   T.IsSymmetric 
→     ∀ (x y : E),       inner 𝕜 (T x) y =         (inner 𝕜 (T (x + y)) (x + y) 
- inner 𝕜 (T (x - y)) (x - y) -               RCLike.I * inner 𝕜 (T (x + RCLike.
I • y)) (x + RCLike.I • y) +             RCLike.I * inner 𝕜 (T (x - RCLike.I • y
)) (x - RCLike.I • y)) /           4
参数：x y : E；T x；inner 𝕜 (T (x + y)) (x + y) - inner 𝕜 (T (x - y)) (x - y) -      
         RCLike.I * inner 𝕜 (T (x + RCLike.I • y)) (x + RCLike.I • y) +         
    RCLike.I * inner 𝕜 (T (x - RCLike.I • y)) (x - RCLike.I • y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RCLike.I_mul_I_ax`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K], RC
Like.I = 0 ∨ RCLike.I * RCLike.I = -1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RCLike.conj_eq_iff_re`：conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) 
= z
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
Polarization identity for symmetric linear maps.
See `inner_map_polarization` for the complex version without the symmetric assum
ption.
-/
theorem IsSymmetric.inner_map_polarization {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x y : E) :
    ⟪T x, y⟫ =
      (⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ - I * ⟪T (x + (I : 𝕜) • y), x + (I : 𝕜) • y⟫ +
          I * ⟪T (x - (I : 𝕜) • y), x - (I : 𝕜) • y⟫) /
        4 := by
  rcases @I_mul_I_ax 𝕜 _ with (h | h)
  · simp_rw [h, zero_mul, sub_zero, add_zero, map_add, map_sub, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, hT x, ← inner_conj_symm x (T y)]
    suffices (re ⟪T y, x⟫ : 𝕜) = ⟪T y, x⟫ by
      rw [conj_eq_iff_re.mpr this]
      ring
    rw [← re_add_im ⟪T y, x⟫]
    simp_rw [h, mul_zero, add_zero]
    norm_cast
  · simp_rw [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      map_smul, inner_smul_left, inner_smul_right, RCLike.conj_I, mul_add, mul_sub, sub_sub,
      ← mul_assoc, mul_neg, h, neg_neg, one_mul, neg_one_mul]
    ring
/-
**LinearMap.isSymmetric_linearIsometryEquiv_conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap`。
形式化陈述：isSymmetric_linearIsometryEquiv_conj_iff {F : Type*} [SeminormedAddCommGro
up F] [InnerProductSpace 𝕜 F] (T : E ->ₗ[𝕜] E) (f : E ≃ₗᵢ[𝕜] F) : (f.toLinearMap
 ∘ₗ T ∘ₗ f.symm.toLinearMap).IsSymmetric ↔ T.IsSymmetric
参数：T : E ->ₗ[𝕜] E；f : E ≃ₗᵢ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `LinearIsometryEquiv.inner_map_eq_flip`：LinearIsometryEquiv.inner_map_eq_
flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') : ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSymmetric_linearIsometryEquiv_conj_iff {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (T : E →ₗ[𝕜] E) (f : E ≃ₗᵢ[𝕜] F) :
    (f.toLinearMap ∘ₗ T ∘ₗ f.symm.toLinearMap).IsSymmetric ↔ T.IsSymmetric := by
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩
  · simpa [LinearIsometryEquiv.inner_map_eq_flip] using h (f x) (f y)
  · simp [LinearIsometryEquiv.inner_map_eq_flip, h _ (f.symm y)]

end LinearMap

/-
**InnerProductSpace.isSymmetric_rankOne_self** 是 Mathlib 中的一个定理，位于命名空间 `InnerPro
ductSpace`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (x : E), (↑(((InnerProductSpace.r
ankOne 𝕜) x) x)).IsSymmetric
参数：x : E；↑(((InnerProductSpace.rankOne 𝕜) x) x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem InnerProductSpace.isSymmetric_rankOne_self (x : E) :
    (rankOne 𝕜 x x).IsSymmetric := fun _ _ ↦ by simp [inner_smul_left, inner_smul_right, mul_comm]

open ContinuousLinearMap in
/-
**InnerProductSpace.isSymmetricProjection_rankOne_self** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：InnerProductSpace.isSymmetricProjection_rankOne_self {x : E} (hx : ‖x‖ = 1
) : (rankOne 𝕜 x x).IsSymmetricProjection where isSymmetric
参数：hx : ‖x‖ = 1。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …
· 使用定理 `InnerProductSpace.isIdempotentElem_rankOne_self`：isIdempotentElem_rankOn
e_self {x : F} (hx : ‖x‖ = 1) : IsIdempotentElem (rankOne 𝕜 x x)
· 使用定理 `InnerProductSpace.isSymmetric_rankOne_self`：∀ {𝕜 : Type u_1} {E : Type u
_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProduct
Space 𝕜 E]   (x : E), (↑(((Inner…
-/
theorem InnerProductSpace.isSymmetricProjection_rankOne_self {x : E} (hx : ‖x‖ = 1) :
    (rankOne 𝕜 x x).IsSymmetricProjection where
  isSymmetric := isSymmetric_rankOne_self x
  isIdempotentElem := isIdempotentElem_rankOne_self hx |>.toLinearMap
/-
**LinearMap.IsSymmetric.toLinearMap_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.IsSymmetric.toLinearMap_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric
) : .symm T.symm.IsSymmetric
参数：hT : T.IsSymmetric。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem LinearMap.IsSymmetric.toLinearMap_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.symm.IsSymmetric := fun x y ↦ by simpa using hT (T.symm x) (T.symm y) |>.symm
/-
**LinearEquiv.isSymmetric_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E ≃ₗ[𝕜] E}, (↑T.symm).IsSymm
etric ↔ (↑T).IsSymmetric
参数：↑T.symm；↑T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.toLinearMap_symm`：LinearMap.IsSymmetric.toLinearMa
p_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric) : .symm T.symm.IsSymmetric
-/
@[simp] theorem LinearEquiv.isSymmetric_symm_iff {T : E ≃ₗ[𝕜] E} :
    T.symm.IsSymmetric ↔ T.IsSymmetric := ⟨.toLinearMap_symm, .toLinearMap_symm⟩

end Seminormed

section Normed

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-- The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a complete space,
  then it is automatically continuous. -/
/-
**LinearMap.IsSymmetric.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmet
ric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [CompleteSpace E] {T : E →ₗ[𝕜] E}, T.
IsSymmetric → Continuous ⇑T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_seq_closed_graph`：LinearMap.continuous_of_seq_cl
osed_graph (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (
g ∘ u) atTop (𝓝 y) -> y = g x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.inner`：Filter.Tendsto.inner {f g : α -> E} {l : Filter α}
 {x y : E} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t =>
 ⟪f t, g t…
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a com
plete space,
  then it is automatically continuous.
-/
theorem IsSymmetric.continuous [CompleteSpace E] {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) :
    Continuous T := by
  -- We prove it by using the closed graph theorem
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu => ?_
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜]
  have hlhs : ∀ k : ℕ, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ := by
    intro k
    rw [← T.map_sub, hT]
  refine tendsto_nhds_unique ((hTu.sub_const _).inner tendsto_const_nhds) ?_
  simp_rw [Function.comp_apply, hlhs]
  rw [← inner_zero_left (T (y - T x))]
  refine Filter.Tendsto.inner ?_ tendsto_const_nhds
  rw [← sub_self x]
  exact hu.sub_const _

/-- A symmetric linear map `T` is zero if and only if `⟪T x, x⟫_ℝ = 0` for all `x`.
See `inner_map_self_eq_zero` for the complex version without the symmetric assumption. -/
/-
**LinearMap.IsSymmetric.inner_map_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → ((∀ 
(x : E), inner 𝕜 (T x) x = 0) ↔ T = 0)
参数：(∀ (x : E), inner 𝕜 (T x) x = 0) ↔ T = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.IsSymmetric.inner_map_polarization`：∀ {𝕜 : Type u_1} {E : Type
 u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProdu
ctSpace 𝕜 E]   {T : E →ₗ[𝕜] E},   …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A symmetric linear map `T` is zero if and only if `⟪T x, x⟫_ℝ = 0` for all `x`.
See `inner_map_self_eq_zero` for the complex version without the symmetric assum
ption.
-/
theorem IsSymmetric.inner_map_self_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    (∀ x, ⟪T x, x⟫ = 0) ↔ T = 0 := by
  simp_rw [LinearMap.ext_iff, zero_apply]
  refine ⟨fun h x => ?_, fun h => by simp_rw [h, inner_zero_left, forall_const]⟩
  rw [← @inner_self_eq_zero 𝕜, hT.inner_map_polarization]
  simp_rw [h _]
  ring
/-
**LinearMap.ker_le_ker_of_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_le_ker_of_range {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymm
etric) (h : range S <= range T) : ker T <= ker S
参数：hS : S.IsSymmetric；hT : T.IsSymmetric；h : range S <= range T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
-/
theorem ker_le_ker_of_range {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (h : range S ≤ range T) : ker T ≤ ker S := by
  intro v hv
  rw [mem_ker] at hv ⊢
  obtain ⟨y, hy⟩ : ∃ y, T y = S (S v) := by simpa using @h (S (S v))
  rw [← inner_self_eq_zero (𝕜 := 𝕜), ← hS, ← hy, hT, hv, inner_zero_right]

open Submodule in
/-- A linear projection onto `U` along its complement `V` is symmetric if
and only if `U` and `V` are pairwise orthogonal. -/
/-
**LinearMap._root_.Submodule.isSymmetric_projection_iff** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear projection onto `U` along its complement `V` is symmetric if
and only if `U` and `V` are pairwise orthogonal.
-/
theorem _root_.Submodule.isSymmetric_projection_iff
    {U V : Submodule 𝕜 E} (hUV : IsCompl U V) :
    (U.projection V hUV).IsSymmetric ↔ U ⟂ V := by
  rw [projection]
  refine ⟨fun h u hu v hv => ?_, fun h x y => ?_⟩
  · rw [← Subtype.coe_mk u hu, ← Subtype.coe_mk v hv,
      ← Submodule.projectionOnto_apply_left hUV ⟨u, hu⟩, ← U.subtype_apply, ← comp_apply,
      ← h, comp_apply, Submodule.projectionOnto_apply_right hUV ⟨v, hv⟩,
      map_zero, inner_zero_left]
  · nth_rw 2 [← projection_add_projection_eq_self hUV x]
    nth_rw 1 [← projection_add_projection_eq_self hUV y]
    rw [isOrtho_iff_inner_eq] at h
    simp [inner_add_right, inner_add_left, h, inner_eq_zero_symm]

@[deprecated (since := "2026-05-05")] alias _root_.Submodule.IsCompl.projection_isSymmetric_iff :=
  _root_.Submodule.isSymmetric_projection_iff

open Submodule in
/-
**LinearMap._root_.Submodule.isSymmetricProjection_projection_iff** 是 Mathlib 中的
一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.isSymmetricProjection_projection_iff
    {U V : Submodule 𝕜 E} (hUV : IsCompl U V) :
    (U.projection V hUV).IsSymmetricProjection ↔ U ⟂ V := by
  simp [isSymmetricProjection_iff, isSymmetric_projection_iff, isIdempotentElem_projection]

@[deprecated (since := "2026-05-05")] alias
  _root_.Submodule.IsCompl.projection_isSymmetricProjection_iff :=
  _root_.Submodule.isSymmetricProjection_projection_iff

alias ⟨_, _root_.Submodule.isSymmetricProjection_projection_of_isOrtho⟩ :=
  _root_.Submodule.isSymmetricProjection_projection_iff

@[deprecated (since := "2026-05-05")] alias
  _root_.Submodule.IsCompl.projection_isSymmetricProjection_of_isOrtho :=
  _root_.Submodule.isSymmetricProjection_projection_of_isOrtho

open Submodule LinearMap in
/-- An idempotent operator is symmetric if and only if its range is
pairwise orthogonal to its kernel. -/
/-
**LinearMap.IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap.IsIdempotentElem`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdempotentElem T →
 (T.IsSymmetric ↔ T.range ⟂ T.ker)
参数：T.IsSymmetric ↔ T.range ⟂ T.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsProj.isCompl`：isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : Is
Compl p (ker f)
· 使用定理 `LinearMap.IsIdempotentElem.isProj_range`：∀ {S : Type u_5} [inst : Semiri
ng S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M]   (
f : M →ₗ[S] M), IsIdempotentE…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.isSymmetric_projection_iff`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   {U V : Submodule 𝕜 E} (…
· 使用定理 `LinearMap.IsIdempotentElem.isCompl`：∀ {R : Type u_1} [inst : Ring R] {E 
: Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {f : E →ₗ[R] 
E},   IsIdempotentElem f…
· 使用定理 `LinearMap.IsIdempotentElem.eq_projection`：∀ {R : Type u_1} [inst : Ring 
R] {E : Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E] {T : E 
→ₗ[R] E}   (hT : IsIdempotentE…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An idempotent operator is symmetric if and only if its range is
pairwise orthogonal to its kernel.
-/
theorem IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker {T : E →ₗ[𝕜] E}
    (hT : IsIdempotentElem T) : T.IsSymmetric ↔ (LinearMap.range T) ⟂ (LinearMap.ker T) := by
  rw [← isSymmetric_projection_iff hT.isProj_range.isCompl, ← hT.eq_projection]
/-
**LinearMap.IsSymmetric.orthogonal_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Is
Symmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSymmetric → T.ra
ngeᗮ = T.ker
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsSymmetric.orthogonal_range {T : E →ₗ[𝕜] E} (hT : LinearMap.IsSymmetric T) :
    (LinearMap.range T)ᗮ = LinearMap.ker T := by
  ext x
  constructor
  · simpa [Submodule.mem_orthogonal, hT _ x] using ext_inner_left 𝕜 (x := T x) (y := 0)
  · simp_all [Submodule.mem_orthogonal, hT _ x]

open Submodule LinearMap in
/-
**LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap.IsIdempotentElem`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdempotentElem T →
 (T.IsSymmetric ↔ T.rangeᗮ = T.ker)
参数：T.IsSymmetric ↔ T.rangeᗮ = T.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.orthogonal_range`：∀ {𝕜 : Type u_1} {E : Type u_2} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 
E]   {T : E →ₗ[𝕜] E}, T.IsSy…
· 使用定理 `Submodule.isOrtho_orthogonal_right`：isOrtho_orthogonal_right (U : Submod
ule 𝕜 E) : U ⟂ Uᗮ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`：∀ {𝕜 : Typ
e u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 
: InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdem…
-/
theorem IsIdempotentElem.isSymmetric_iff_orthogonal_range {T : E →ₗ[𝕜] E}
    (h : IsIdempotentElem T) : T.IsSymmetric ↔ (LinearMap.range T)ᗮ = (LinearMap.ker T) :=
  ⟨fun hT => hT.orthogonal_range, fun hT =>
    h.isSymmetric_iff_isOrtho_range_ker.eq ▸ hT.symm ▸ isOrtho_orthogonal_right _⟩

open LinearMap in
/-- Symmetric projections are equal iff their range are. -/
/-
**LinearMap.IsSymmetricProjection.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sSymmetricProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {S T : E →ₗ[𝕜] E}, S.IsSymmetricProje
ction → T.IsSymmetricProjection → (S = T ↔ S.range = T.range)
参数：S = T ↔ S.range = T.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsIdempotentElem.ext_iff`：∀ {R : Type u_1} [inst : Ring R] {E 
: Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   {p q : E →ₗ
[R] E}, IsIdempotentElem…
· 使用定理 `LinearMap.IsSymmetricProjection.isIdempotentElem`：∀ {𝕜 : Type u_1} {E : 
Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range`：∀ {𝕜 : Type
 u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 :
 InnerProductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, IsIdem…
· 使用定理 `LinearMap.IsSymmetricProjection.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type 
u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Symmetric projections are equal iff their range are.
-/
theorem IsSymmetricProjection.ext_iff {S T : E →ₗ[𝕜] E}
    (hS : S.IsSymmetricProjection) (hT : T.IsSymmetricProjection) :
    S = T ↔ LinearMap.range S = LinearMap.range T := by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  rw [hS.isIdempotentElem.ext_iff hT.isIdempotentElem,
    ← hT.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hT.isSymmetric,
    ← hS.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hS.isSymmetric]
  simp [h]

alias ⟨_, IsSymmetricProjection.ext⟩ := IsSymmetricProjection.ext_iff

open LinearMap in
/-
**LinearMap.IsSymmetricProjection.sub_of_range_le_range** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.IsSymmetricProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {p q : E →ₗ[𝕜] E},   p.IsSymmetricPro
jection → q.IsSymmetricProjection → p.range ≤ q.range → (q - p).IsSymmetricProje
ction
参数：q - p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.sub`：sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsId
empotentElem a) (hb : IsIdempotentElem b) (hab : a * b = a) (hba : b * a = a) : 
IsIdempote…
· 使用定理 `LinearMap.IsSymmetricProjection.isIdempotentElem`：∀ {𝕜 : Type u_1} {E : 
Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymmetricProjection.isSymmetric`：∀ {𝕜 : Type u_1} {E : Type 
u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsIdempotentElem.comp_eq_right_iff`：∀ {S : Type u_5} [inst : S
emiring S] {M : Type u_6} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module S M
]   {q : M →ₗ[S] M},   IsIdempoten…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.IsSymmetric.sub`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T S
 : E →ₗ[𝕜] E}, …
-/
theorem IsSymmetricProjection.sub_of_range_le_range {p q : E →ₗ[𝕜] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) (hqp : range p ≤ range q) :
    (q - p).IsSymmetricProjection := by
  rw [← hq.isIdempotentElem.comp_eq_right_iff] at hqp
  refine ⟨hp.isIdempotentElem.sub hq.isIdempotentElem (LinearMap.ext fun x => ext_inner_left 𝕜
    fun y => ?_) hqp, hq.isSymmetric.sub hp.isSymmetric⟩
  simp_rw [Module.End.mul_apply, ← hp.isSymmetric _, ← hq.isSymmetric _, ← comp_apply, hqp]
/-
**LinearMap.IsSymmetric.isSymmetric_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {f : E →ₗ[𝕜] E}, f.IsSymmetric → f ≠ 
0 → ∀ {α : 𝕜}, (α • f).IsSymmetric ↔ IsSelfAdjoint α
参数：α • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ext_iff_inner_left`：ext_iff_inner_left {x y : E} : x = y ↔ forall v, ⟪v,
 x⟫ = ⟪v, y⟫
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `LinearMap.IsSymmetric.smul`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {c 
: 𝕜}, (starRingE…
-/
theorem IsSymmetric.isSymmetric_smul_iff {f : E →ₗ[𝕜] E} (hf : f.IsSymmetric) (hf' : f ≠ 0)
    {α : 𝕜} : (α • f).IsSymmetric ↔ IsSelfAdjoint α := by
  refine ⟨fun h ↦ ?_, hf.smul⟩
  simp only [ne_eq, LinearMap.ext_iff, zero_apply, ext_iff_inner_left 𝕜 (E := E),
    inner_zero_right] at hf'
  simpa [IsSymmetric, inner_smul_left, inner_smul_right, hf _ _, forall_or_left,
    (forall_comm.eq ▸ hf')] using! h

end LinearMap

end Normed

