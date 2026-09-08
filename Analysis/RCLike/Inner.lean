/-
Copyright (c) 2023 Yaël Dilies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dilies
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# L2 inner product of finite sequences

This file defines the weighted L2 inner product of functions `f g : ι → R` where `ι` is a fintype as
`∑ i, conj (f i) * g i`. This convention (conjugation on the left) matches the inner product coming
from `RCLike.innerProductSpace`.

## TODO

* Build a non-instance `InnerProductSpace` from `wInner`.
* `cWeight` is a poor name. Can we find better? It doesn't hugely matter for typing, since it's
  hidden behind the `⟪f, g⟫ₙ_[𝕝]` notation, but it does show up in lemma names
  `⟪f, g⟫_[𝕝, cWeight]` is called `wInner_cWeight`. Maybe we should introduce some naming
  convention, similarly to `MeasureTheory.average`?
-/

public section

open Finset Function WithLp
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

variable {ι κ 𝕜 : Type*} {E : ι → Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜]

section Pi
variable [∀ i, SeminormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] {w : ι → ℝ}

/-- Weighted inner product giving rise to the L2 norm, denoted as `⟪g, f⟫_[𝕜, w]`. -/
/-
**RCLike.wInner** 是 Mathlib 中的一个定义，位于命名空间 `RCLike`。
形式化陈述：wInner (w : ι -> Real) (f g : forall i, E i) : 𝕜
参数：w : ι -> Real；f g : forall i, E i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weighted inner product giving rise to the L2 norm, denoted as `⟪g, f⟫_[𝕜, w]`.
-/
def wInner (w : ι → ℝ) (f g : ∀ i, E i) : 𝕜 := ∑ i, w i • ⟪f i, g i⟫_𝕜

/-- The weight function making `wInner` into the compact inner product. -/
/-
**RCLike.cWeight** 是 Mathlib 中的一个缩写定义，位于命名空间 `RCLike`。
形式化陈述：cWeight : ι -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight function making `wInner` into the compact inner product.
-/
noncomputable abbrev cWeight : ι → ℝ := Function.const _ (Fintype.card ι)⁻¹

@[inherit_doc wInner] notation3 "⟪" f ", " g "⟫_[" 𝕝 ", " w "]" => wInner (𝕜 := 𝕝) w f g

/-- Discrete inner product giving rise to the discrete L2 norm. -/
notation3 "⟪" f ", " g "⟫_[" 𝕝 "]" => ⟪f, g⟫_[𝕝, 1]

/-- Compact inner product giving rise to the compact L2 norm. -/
notation3 "⟪" f ", " g "⟫ₙ_[" 𝕝 "]" => ⟪f, g⟫_[𝕝, cWeight]

/-
**RCLike.wInner_cWeight_eq_smul_wInner_one** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_cWeight_eq_smul_wInner_one (f g : forall i, E i) : ⟪f, g⟫ₙ_[𝕜] = (F
intype.card ι : Rat>=0)⁻¹ • ⟪f, g⟫_[𝕜]
参数：f g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_inv`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p : ℚ≥0), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_cWeight_eq_smul_wInner_one (f g : ∀ i, E i) :
    ⟪f, g⟫ₙ_[𝕜] = (Fintype.card ι : ℚ≥0)⁻¹ • ⟪f, g⟫_[𝕜] := by
  simp [wInner, smul_sum, ← NNRat.cast_smul_eq_nnqsmul ℝ]
/-
**RCLike.conj_wInner_symm** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_4} [inst : Fintype ι] [ins
t_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_3 : (i
 : ι) → InnerProductSpace 𝕜 (E i)] (w : ι → ℝ)   (f g : (i : ι) → E i), (starRin
gEnd 𝕜) ⟪f, g⟫_[𝕜, w] = ⟪g, f⟫_[𝕜, w]
参数：i : ι；E i；i : ι；E i；w : ι → ℝ；f g : (i : ι) → E i；starRingEnd 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `RCLike.conj_smul`：conj_smul (r : Real) (z : K) : conj (r • z) = r • conj
 z
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conj_wInner_symm (w : ι → ℝ) (f g : ∀ i, E i) :
    conj ⟪f, g⟫_[𝕜, w] = ⟪g, f⟫_[𝕜, w] := by
  simp [wInner, map_sum, inner_conj_symm, rclike_simps]
/-
**RCLike.wInner_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_4} [inst : Fintype ι] [ins
t_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_3 : (i
 : ι) → InnerProductSpace 𝕜 (E i)] (w : ι → ℝ)   (g : (i : ι) → E i), ⟪0, g⟫_[𝕜,
 w] = 0
参数：i : ι；E i；i : ι；E i；w : ι → ℝ；g : (i : ι) → E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_zero_left (w : ι → ℝ) (g : ∀ i, E i) : ⟪0, g⟫_[𝕜, w] = 0 := by simp [wInner]
/-
**RCLike.wInner_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_4} [inst : Fintype ι] [ins
t_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_3 : (i
 : ι) → InnerProductSpace 𝕜 (E i)] (w : ι → ℝ)   (f : (i : ι) → E i), ⟪f, 0⟫_[𝕜,
 w] = 0
参数：i : ι；E i；i : ι；E i；w : ι → ℝ；f : (i : ι) → E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_zero_right (w : ι → ℝ) (f : ∀ i, E i) : ⟪f, 0⟫_[𝕜, w] = 0 := by simp [wInner]
/-
**RCLike.wInner_add_left** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_add_left (w : ι -> Real) (f₁ f₂ g : forall i, E i) : ⟪f₁ + f₂, g⟫_[
𝕜, w] = ⟪f₁, g⟫_[𝕜, w] + ⟪f₂, g⟫_[𝕜, w]
参数：w : ι -> Real；f₁ f₂ g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_add_left (w : ι → ℝ) (f₁ f₂ g : ∀ i, E i) :
    ⟪f₁ + f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] + ⟪f₂, g⟫_[𝕜, w] := by
  simp [wInner, inner_add_left, smul_add, sum_add_distrib]
/-
**RCLike.wInner_add_right** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_add_right (w : ι -> Real) (f g₁ g₂ : forall i, E i) : ⟪f, g₁ + g₂⟫_
[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] + ⟪f, g₂⟫_[𝕜, w]
参数：w : ι -> Real；f g₁ g₂ : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_add_right (w : ι → ℝ) (f g₁ g₂ : ∀ i, E i) :
    ⟪f, g₁ + g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] + ⟪f, g₂⟫_[𝕜, w] := by
  simp [wInner, inner_add_right, smul_add, sum_add_distrib]
/-
**RCLike.wInner_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_4} [inst : Fintype ι] [ins
t_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_3 : (i
 : ι) → InnerProductSpace 𝕜 (E i)] (w : ι → ℝ)   (f g : (i : ι) → E i), ⟪-f, g⟫_
[𝕜, w] = -⟪f, g⟫_[𝕜, w]
参数：i : ι；E i；i : ι；E i；w : ι → ℝ；f g : (i : ι) → E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_neg_left (w : ι → ℝ) (f g : ∀ i, E i) : ⟪-f, g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w] := by
  simp [wInner]
/-
**RCLike.wInner_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_4} [inst : Fintype ι] [ins
t_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_3 : (i
 : ι) → InnerProductSpace 𝕜 (E i)] (w : ι → ℝ)   (f g : (i : ι) → E i), ⟪f, -g⟫_
[𝕜, w] = -⟪f, g⟫_[𝕜, w]
参数：i : ι；E i；i : ι；E i；w : ι → ℝ；f g : (i : ι) → E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_neg_right (w : ι → ℝ) (f g : ∀ i, E i) : ⟪f, -g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w] := by
  simp [wInner]
/-
**RCLike.wInner_sub_left** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_sub_left (w : ι -> Real) (f₁ f₂ g : forall i, E i) : ⟪f₁ - f₂, g⟫_[
𝕜, w] = ⟪f₁, g⟫_[𝕜, w] - ⟪f₂, g⟫_[𝕜, w]
参数：w : ι -> Real；f₁ f₂ g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `RCLike.wInner_add_left`：wInner_add_left (w : ι -> Real) (f₁ f₂ g : foral
l i, E i) : ⟪f₁ + f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] + ⟪f₂, g⟫_[𝕜, w]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.wInner_neg_left`：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_
4} [inst : Fintype ι] [inst_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCom
mGroup (E i)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_sub_left (w : ι → ℝ) (f₁ f₂ g : ∀ i, E i) :
    ⟪f₁ - f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] - ⟪f₂, g⟫_[𝕜, w] := by
  simp_rw [sub_eq_add_neg, wInner_add_left, wInner_neg_left]
/-
**RCLike.wInner_sub_right** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_sub_right (w : ι -> Real) (f g₁ g₂ : forall i, E i) : ⟪f, g₁ - g₂⟫_
[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] - ⟪f, g₂⟫_[𝕜, w]
参数：w : ι -> Real；f g₁ g₂ : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.wInner_add_right`：wInner_add_right (w : ι -> Real) (f g₁ g₂ : for
all i, E i) : ⟪f, g₁ + g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] + ⟪f, g₂⟫_[𝕜, w]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.wInner_neg_right`：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u
_4} [inst : Fintype ι] [inst_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCo
mmGroup (E i)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_sub_right (w : ι → ℝ) (f g₁ g₂ : ∀ i, E i) :
    ⟪f, g₁ - g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] - ⟪f, g₂⟫_[𝕜, w] := by
  simp_rw [sub_eq_add_neg, wInner_add_right, wInner_neg_right]
/-
**RCLike.wInner_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u_4} [inst : Fintype ι] [ins
t_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_3 : (i
 : ι) → InnerProductSpace 𝕜 (E i)] [IsEmpty ι]   (w : ι → ℝ) (f g : (i : ι) → E 
i), ⟪f, g⟫_[𝕜, w] = 0
参数：i : ι；E i；i : ι；E i；w : ι → ℝ；f g : (i : ι) → E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `RCLike.wInner_zero_left`：∀ {ι : Type u_1} {𝕜 : Type u_3} {E : ι → Type u
_4} [inst : Fintype ι] [inst_1 : RCLike 𝕜]   [inst_2 : (i : ι) → SeminormedAddCo
mmGroup (E i)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_of_isEmpty [IsEmpty ι] (w : ι → ℝ) (f g : ∀ i, E i) : ⟪f, g⟫_[𝕜, w] = 0 := by
  simp [Subsingleton.elim f 0]
/-
**RCLike.wInner_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_smul_left {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [
StarModule 𝕝 𝕜] [SMulCommClass Real 𝕝 𝕜] [forall i, Module 𝕝 (E i)] [forall i, I
sScalarTower 𝕝 𝕜 (E i)] (c : 𝕝) (w : ι -> Real) (f g : forall i, E i) : ⟪c • f, 
g⟫_[𝕜, w] = star c • ⟪f, g⟫_[𝕜, w]
参数：E i；E i；c : 𝕝；w : ι -> Real；f g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `inner_smul_left_eq_star_smul`：inner_smul_left_eq_star_smul (x y : E) (r 
: 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_smul_left {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
    [SMulCommClass ℝ 𝕝 𝕜] [∀ i, Module 𝕝 (E i)] [∀ i, IsScalarTower 𝕝 𝕜 (E i)] (c : 𝕝)
    (w : ι → ℝ) (f g : ∀ i, E i) : ⟪c • f, g⟫_[𝕜, w] = star c • ⟪f, g⟫_[𝕜, w] := by
  simp_rw [wInner, Pi.smul_apply, inner_smul_left_eq_star_smul, starRingEnd_apply, smul_sum,
    smul_comm (w _)]
/-
**RCLike.wInner_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_smul_right {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] 
[StarModule 𝕝 𝕜] [forall i, Module 𝕝 (E i)] [forall i, IsScalarTower 𝕝 𝕜 (E i)] 
(c : 𝕝) (w : ι -> Real) (f g : forall i, E i) : ⟪f, c • g⟫_[𝕜, w] = c • ⟪f, g⟫_[
𝕜, w]
参数：E i；E i；c : 𝕝；w : ι -> Real；f g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `inner_smul_right_eq_smul`：inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪
x, r • y⟫ = r • ⟪x, y⟫
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_smul_right {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
    [∀ i, Module 𝕝 (E i)] [∀ i, IsScalarTower 𝕝 𝕜 (E i)] (c : 𝕝)
    (w : ι → ℝ) (f g : ∀ i, E i) : ⟪f, c • g⟫_[𝕜, w] = c • ⟪f, g⟫_[𝕜, w] := by
  simp_rw [wInner, Pi.smul_apply, inner_smul_right_eq_smul, smul_sum, smul_comm c]
/-
**RCLike.mul_wInner_left** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：mul_wInner_left (c : 𝕜) (w : ι -> Real) (f g : forall i, E i) : c * ⟪f, g⟫
_[𝕜, w] = ⟪star c • f, g⟫_[𝕜, w]
参数：c : 𝕜；w : ι -> Real；f g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.wInner_smul_left`：wInner_smul_left {𝕝 : Type*} [CommSemiring 𝕝] [
StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜] [SMulCommClass Real 𝕝 𝕜] [forall i, M
odule 𝕝 (E i)…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
lemma mul_wInner_left (c : 𝕜) (w : ι → ℝ) (f g : ∀ i, E i) :
    c * ⟪f, g⟫_[𝕜, w] = ⟪star c • f, g⟫_[𝕜, w] := by rw [wInner_smul_left, star_star, smul_eq_mul]
/-
**RCLike.wInner_one_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_one_eq_sum (f g : forall i, E i) : ⟪f, g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜
参数：f g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_one_eq_sum (f g : ∀ i, E i) : ⟪f, g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜 := by simp [wInner]
/-
**RCLike.wInner_cWeight_eq_expect** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_cWeight_eq_expect (f g : forall i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, 
g i⟫_𝕜
参数：f g : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_inv`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p : ℚ≥0), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_cWeight_eq_expect (f g : ∀ i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜 := by
  simp [wInner, expect, smul_sum, ← NNRat.cast_smul_eq_nnqsmul ℝ]

end Pi

section Function
variable {w : ι → ℝ} {f g : ι → 𝕜}

/-
**RCLike.wInner_const_left** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_const_left (a : 𝕜) (f : ι -> 𝕜) : ⟪const _ a, f⟫_[𝕜, w] = (∑ i, w i
 • f i) * conj a
参数：a : 𝕜；f : ι -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫_[𝕜, w] = (∑ i, w i • f i) * conj a := by simp [wInner, const_apply, sum_mul]
/-
**RCLike.wInner_const_right** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_const_right (f : ι -> 𝕜) (a : 𝕜) : ⟪f, const _ a⟫_[𝕜, w] = a * (∑ i
, w i • conj (f i))
参数：f : ι -> 𝕜；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_const_right (f : ι → 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫_[𝕜, w] = a * (∑ i, w i • conj (f i)) := by simp [wInner, const_apply, mul_sum]
/-
**RCLike.wInner_one_const_left** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : Fintype ι] [inst_1 : RCLike 𝕜] (a 
: 𝕜) (f : ι → 𝕜),   ⟪Function.const ι a, f⟫_[𝕜] = (∑ i, f i) * (starRingEnd 𝕜) a
参数：a : 𝕜；f : ι → 𝕜；∑ i, f i；starRingEnd 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.wInner_one_eq_sum`：wInner_one_eq_sum (f g : forall i, E i) : ⟪f, 
g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_one_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫_[𝕜] = (∑ i, f i) * conj a := by simp [wInner_one_eq_sum, sum_mul]
/-
**RCLike.wInner_one_const_right** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : Fintype ι] [inst_1 : RCLike 𝕜] (f 
: ι → 𝕜) (a : 𝕜),   ⟪f, Function.const ι a⟫_[𝕜] = a * ∑ i, (starRingEnd 𝕜) (f i)
参数：f : ι → 𝕜；a : 𝕜；starRingEnd 𝕜；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.wInner_one_eq_sum`：wInner_one_eq_sum (f g : forall i, E i) : ⟪f, 
g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_one_const_right (f : ι → 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫_[𝕜] = a * (∑ i, conj (f i)) := by simp [wInner_one_eq_sum, mul_sum]
/-
**RCLike.wInner_cWeight_const_left** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : Fintype ι] [inst_1 : RCLike 𝕜] (a 
: 𝕜) (f : ι → 𝕜),   ⟪Function.const ι a, f⟫ₙ_[𝕜] = Finset.univ.expect fun i => f
 i * (starRingEnd 𝕜) a
参数：a : 𝕜；f : ι → 𝕜；starRingEnd 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.wInner_cWeight_eq_expect`：wInner_cWeight_eq_expect (f g : forall 
i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_cWeight_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫ₙ_[𝕜] = 𝔼 i, f i * conj a := by simp [wInner_cWeight_eq_expect]
/-
**RCLike.wInner_cWeight_const_right** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : Fintype ι] [inst_1 : RCLike 𝕜] (f 
: ι → 𝕜) (a : 𝕜),   ⟪f, Function.const ι a⟫ₙ_[𝕜] = a * Finset.univ.expect fun i 
=> (starRingEnd 𝕜) (f i)
参数：f : ι → 𝕜；a : 𝕜；starRingEnd 𝕜；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RCLike.wInner_cWeight_eq_expect`：wInner_cWeight_eq_expect (f g : forall 
i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜
· 使用引理 `Finset.mul_expect`：mul_expect [SMulCommClass Rat>=0 M M] (s : Finset ι) 
(f : ι -> M) (a : M) : a * 𝔼 i in s, f i = 𝔼 i in s, a * f i
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma wInner_cWeight_const_right (f : ι → 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫ₙ_[𝕜] = a * (𝔼 i, conj (f i)) := by simp [wInner_cWeight_eq_expect, mul_expect]
/-
**RCLike.wInner_one_eq_inner** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_one_eq_inner (f g : ι -> 𝕜) : ⟪f, g⟫_[𝕜, 1] = ⟪toLp 2 f, toLp 2 g⟫_
𝕜
参数：f g : ι -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_one_eq_inner (f g : ι → 𝕜) :
    ⟪f, g⟫_[𝕜, 1] = ⟪toLp 2 f, toLp 2 g⟫_𝕜 := by
  simp [PiLp.inner_apply, wInner]
/-
**RCLike.inner_eq_wInner_one** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：inner_eq_wInner_one (f g : PiLp 2 fun _i : ι => 𝕜) : ⟪f, g⟫_𝕜 = ⟪ofLp f, o
fLp g⟫_[𝕜, 1]
参数：f g : PiLp 2 fun _i : ι => 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_eq_wInner_one (f g : PiLp 2 fun _i : ι ↦ 𝕜) :
    ⟪f, g⟫_𝕜 = ⟪ofLp f, ofLp g⟫_[𝕜, 1] := by
  simp [PiLp.inner_apply, wInner]
/-
**RCLike.linearIndependent_of_ne_zero_of_wInner_one_eq_zero** 是 Mathlib 中的一个引理，位
于命名空间 `RCLike`。
形式化陈述：linearIndependent_of_ne_zero_of_wInner_one_eq_zero {f : κ -> ι -> 𝕜} (hf :
 forall k, f k != 0) (hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫_[𝕜] = 0) : Lin
earIndependent 𝕜 f
参数：hf : forall k, f k != 0；hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫_[𝕜] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `linearIndependent_of_ne_zero_of_inner_eq_zero`：linearIndependent_of_ne_z
ero_of_inner_eq_zero {ι : Type*} {v : ι -> E} (hz : forall i, v i != 0) (ho : Pa
irwise fun i j => ⟪v i, v j⟫ = 0) :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `WithLp.toLp_eq_zero`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup
 V] {x : V}, WithLp.toLp p x = 0 ↔ x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.wInner_one_eq_inner`：wInner_one_eq_inner (f g : ι -> 𝕜) : ⟪f, g⟫_
[𝕜, 1] = ⟪toLp 2 f, toLp 2 g⟫_𝕜
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `WithLp.toLp_injective`：toLp_injective : Function.Injective (@toLp p V)
-/
lemma linearIndependent_of_ne_zero_of_wInner_one_eq_zero {f : κ → ι → 𝕜} (hf : ∀ k, f k ≠ 0)
    (hinner : Pairwise fun k₁ k₂ ↦ ⟪f k₁, f k₂⟫_[𝕜] = 0) : LinearIndependent 𝕜 f := by
  simp_rw [wInner_one_eq_inner] at hinner
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ hinner
  exacts [(WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm.toLinearMap.linearIndependent_iff_of_injOn
    (toLp_injective 2).injOn |>.1 this, fun i ↦ (toLp_eq_zero 2).ne.2 (hf i)]
/-
**RCLike.linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero** 是 Mathlib 中的一个
引理，位于命名空间 `RCLike`。
形式化陈述：linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero {f : κ -> ι -> 𝕜} (
hf : forall k, f k != 0) (hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫ₙ_[𝕜] = 0) 
: LinearIndependent 𝕜 f
参数：hf : forall k, f k != 0；hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫ₙ_[𝕜] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用引理 `RCLike.linearIndependent_of_ne_zero_of_wInner_one_eq_zero`：linearIndepen
dent_of_ne_zero_of_wInner_one_eq_zero {f : κ -> ι -> 𝕜} (hf : forall k, f k != 0
) (hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用引理 `RCLike.wInner_cWeight_eq_smul_wInner_one`：wInner_cWeight_eq_smul_wInner_
one (f g : forall i, E i) : ⟪f, g⟫ₙ_[𝕜] = (Fintype.card ι : Rat>=0)⁻¹ • ⟪f, g⟫_[
𝕜]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NNRat.cast_inv`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p : ℚ≥0), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero {f : κ → ι → 𝕜} (hf : ∀ k, f k ≠ 0)
    (hinner : Pairwise fun k₁ k₂ ↦ ⟪f k₁, f k₂⟫ₙ_[𝕜] = 0) : LinearIndependent 𝕜 f := by
  cases isEmpty_or_nonempty ι
  · have : IsEmpty κ := ⟨fun k ↦ hf k <| Subsingleton.elim ..⟩
    exact linearIndependent_empty_type
  · exact linearIndependent_of_ne_zero_of_wInner_one_eq_zero hf <| by
      simpa [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul 𝕜] using hinner
/-
**RCLike.wInner_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：wInner_nonneg (hw : 0 <= w) (hf : 0 <= f) (hg : 0 <= g) : 0 <= ⟪f, g⟫_[𝕜, 
w]
参数：hw : 0 <= w；hf : 0 <= f；hg : 0 <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `RCLike.toIsStrictOrderedRing`：toIsStrictOrderedRing : IsStrictOrderedRin
g K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `star_nonneg_iff`：star_nonneg_iff {x : R} : 0 <= star x ↔ 0 <= x
-/
lemma wInner_nonneg (hw : 0 ≤ w) (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜, w] :=
  sum_nonneg fun _ _ ↦ smul_nonneg (hw _) <| mul_nonneg (hg _) (star_nonneg_iff.2 (hf _))
/-
**RCLike.norm_wInner_le** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：norm_wInner_le (hw : 0 <= w) : ‖⟪f, g⟫_[𝕜, w]‖ <= ⟪fun i => ‖f i‖, fun i =
> ‖g i‖⟫_[Real, w]
参数：hw : 0 <= w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_wInner_le (hw : 0 ≤ w) : ‖⟪f, g⟫_[𝕜, w]‖ ≤ ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ, w] :=
  (norm_sum_le ..).trans_eq <| sum_congr rfl fun i _ ↦ by
    simp [Algebra.smul_def, norm_mul, abs_of_nonneg (hw i)]

end Function

section Real
variable {w f g : ι → ℝ}

/-
**RCLike.abs_wInner_le** 是 Mathlib 中的一个引理，位于命名空间 `RCLike`。
形式化陈述：abs_wInner_le (hw : 0 <= w) : |⟪f, g⟫_[Real, w]| <= ⟪|f|, |g|⟫_[Real, w]
参数：hw : 0 <= w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.norm_wInner_le`：norm_wInner_le (hw : 0 <= w) : ‖⟪f, g⟫_[𝕜, w]‖ <=
 ⟪fun i => ‖f i‖, fun i => ‖g i‖⟫_[Real, w]
-/
lemma abs_wInner_le (hw : 0 ≤ w) : |⟪f, g⟫_[ℝ, w]| ≤ ⟪|f|, |g|⟫_[ℝ, w] := by
  simpa using! norm_wInner_le (𝕜 := ℝ) hw

end Real
end RCLike

