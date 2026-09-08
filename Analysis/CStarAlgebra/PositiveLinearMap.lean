/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-! # Positive linear maps in C⋆-algebras

This file develops the API for positive linear maps over C⋆-algebras.

## Main results

* `PositiveLinearMap.exists_norm_apply_le`: positive maps are bounded (and therefore continuous)
  on non-unital C⋆-algebras.

## References

* The proof that positive maps are bounded was taken from
  https://math.stackexchange.com/questions/426487/why-is-every-positive-linear-map-between-c-algebras-bounded
-/

public section

open scoped NNReal

variable {A₁ A₂ B₁ B₂ : Type*}

section CStarAlgebra

namespace PositiveLinearMap

variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]
  [CStarAlgebra B₁] [CStarAlgebra B₂] [PartialOrder B₁] [PartialOrder B₂]
  [StarOrderedRing B₁]

/-
**PositiveLinearMap.apply_le_of_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `Positiv
eLinearMap`。
形式化陈述：apply_le_of_isSelfAdjoint (f : B₁ ->ₚ[Complex] B₂) (x : B₁) (hx : IsSelfAd
joint x) : f x <= f (algebraMap Real B₁ ‖x‖)
参数：f : B₁ ->ₚ[Complex] B₂；x : B₁；hx : IsSelfAdjoint x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `PositiveLinearMap.instOrderHomClass`：∀ {R : Type u_1} {E₁ : Type u_2} {E
₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Partia
lOrder E₁] [inst_3 : AddC…
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
-/
lemma apply_le_of_isSelfAdjoint (f : B₁ →ₚ[ℂ] B₂) (x : B₁) (hx : IsSelfAdjoint x) :
    f x ≤ f (algebraMap ℝ B₁ ‖x‖) := by
  gcongr
  exact IsSelfAdjoint.le_algebraMap_norm_self hx
/-
**PositiveLinearMap.norm_apply_le_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `PositiveL
inearMap`。
形式化陈述：norm_apply_le_of_nonneg [StarOrderedRing B₂] (f : B₁ ->ₚ[Complex] B₂) (x :
 B₁) (hx : 0 <= x) : ‖f x‖ <= ‖f 1‖ * ‖x‖
参数：f : B₁ ->ₚ[Complex] B₂；x : B₁；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用引理 `CStarAlgebra.norm_le_norm_of_nonneg_of_le`：norm_le_norm_of_nonneg_of_le 
{a b : A} (ha : 0 <= a
· 使用定理 `PositiveLinearMap.map_nonneg`：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Typ
e u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder 
E₁] [inst_3 : AddC…
· 使用定理 `Complex.coe_smul`：Complex.coe_smul {E : Type*} [AddCommGroup E] [Module 
Complex E] (x : Real) (y : E) : (x : Complex) • y = x • y
· 使用定理 `LinearMapClass.map_smul`：∀ {R : outParam (Type u_14)} {M : outParam (Typ
e u_15)} {M₂ : outParam (Type u_16)} [inst : Semiring R]   [inst_1 : AddCommMono
id M] [inst_2…
· 使用定理 `PositiveLinearMap.instLinearMapClass`：∀ {R : Type u_1} {E₁ : Type u_2} {
E₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Parti
alOrder E₁] [inst_3 : AddC…
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `PositiveLinearMap.instOrderHomClass`：∀ {R : Type u_1} {E₁ : Type u_2} {E
₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Partia
lOrder E₁] [inst_3 : AddC…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
-/
lemma norm_apply_le_of_nonneg [StarOrderedRing B₂] (f : B₁ →ₚ[ℂ] B₂) (x : B₁) (hx : 0 ≤ x) :
    ‖f x‖ ≤ ‖f 1‖ * ‖x‖ := by
  have h : ‖‖x‖‖ = ‖x‖ := by simp
  rw [mul_comm, ← h, ← norm_smul ‖x‖ (f 1)]
  clear h
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg hx) ?_
  rw [← Complex.coe_smul, ← LinearMapClass.map_smul f]
  gcongr
  rw [← Algebra.algebraMap_eq_smul_one]
  exact IsSelfAdjoint.le_algebraMap_norm_self <| .of_nonneg hx

open Complex Filter in
/--
If `f` is a positive map, then it is bounded (and therefore continuous).
-/
/-
**PositiveLinearMap.exists_norm_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLine
arMap`。
形式化陈述：exists_norm_apply_le (f : A₁ ->ₚ[Complex] A₂) : exists C : Real>=0, forall
 a, ‖f a‖ <= C * ‖a‖
参数：f : A₁ ->ₚ[Complex] A₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `eq_zero_or_norm_pos`：∀ {E : Type u_5} [inst : NormedAddGroup E] (a : E),
 a = 0 ∨ 0 < ‖a‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
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
· 使用定理 `PositiveLinearMap.instLinearMapClass`：∀ {R : Type u_1} {E₁ : Type u_2} {
E₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Parti
alOrder E₁] [inst_3 : AddC…
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 115 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a positive map, then it is bounded (and therefore continuous).
-/
lemma exists_norm_apply_le (f : A₁ →ₚ[ℂ] A₂) : ∃ C : ℝ≥0, ∀ a, ‖f a‖ ≤ C * ‖a‖ := by
  /- It suffices to only consider for positive `a`, by decomposing `a` into positive and negative
     parts of the real and imaginary parts. -/
  suffices h_nonneg : ∃ C : ℝ≥0, ∀ a, 0 ≤ a → ‖f a‖ ≤ C * ‖a‖ by
    obtain ⟨C, hmain⟩ := h_nonneg
    refine ⟨4 * C, fun x ↦ ?_⟩
    obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
    conv_lhs => rw [hy]
    simp only [map_sum, map_smul]
    apply norm_sum_le _ _ |>.trans
    simp only [norm_smul, norm_pow, norm_I, one_pow, one_mul]
    apply Finset.sum_le_sum (g := fun _ ↦ C * ‖x‖) (fun i _ ↦ ?_) |>.trans <| by simp [mul_assoc]
    apply hmain _ (hy_nonneg i) |>.trans
    gcongr
    exact hy_norm i
  -- Let's proceed by contradiction
  by_contra! hcontra
  -- Given `n : ℕ`, we can always choose a positive element of norm one with `2 ^ (2 * n) < ‖f x‖`
  have (n : ℕ) : ∃ x, 0 ≤ x ∧ ‖x‖ = 1 ∧ 2 ^ (2 * n) < ‖f x‖ := by
    obtain ⟨hx₁, hx₂⟩ := Classical.choose_spec (hcontra (2 ^ (2 * n)))
    set x := Classical.choose (hcontra (2 ^ (2 * n)))
    have hx := (eq_zero_or_norm_pos x).resolve_left (fun hx ↦ by simp_all)
    refine ⟨‖x‖⁻¹ • x, smul_nonneg (by positivity) hx₁, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hx.ne']
    · simpa [norm_smul] using (lt_inv_mul_iff₀' hx).mpr hx₂
  -- Let `x n` be a sequence of nonnegative elements such that `‖x n‖ = 1` and `‖f (x n)‖ ≥ 4 ^ n`.
  choose x hx using this
  simp only [forall_and] at hx
  obtain ⟨hx_nonneg, hx_norm, hx⟩ := hx
  -- `∑ n, 2 ^ (-n) • x n` converges
  have x_summable : Summable fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ)) • x n := by
    refine Summable.of_norm ?_
    have : (2 : ℝ)⁻¹ < 1 := by norm_num
    simp [norm_smul, hx_norm, ← inv_pow, this]
  -- There is some `n` such that `‖f (∑' m, 2 ^ (-m) • x m)‖ < 2 ^ n`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖f (∑' (n : ℕ), (2 : ℝ) ^ (-(n : ℤ)) • x n)‖ < (2 : ℝ) ^ n :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two |>.eventually_gt_atTop _
      |>.exists
  -- But `2 ^ n ≤ ‖f (2 ^ (-n) • x n)‖ ≤ ‖f (∑' m, 2 ^ (-m) • x m)‖`, which is a contradiction.
  apply hn.not_ge
  trans ‖f ((2 : ℝ) ^ (-n : ℤ) • x n)‖
  · have := hx n |>.le
    rw [pow_mul', sq] at this
    simpa [norm_smul] using (le_inv_mul_iff₀ (show 0 < (2 : ℝ) ^ n by positivity)).mpr this
  · have (m : ℕ) : 0 ≤ ((2 : ℝ) ^ (-(m : ℤ)) • x m) := smul_nonneg (by positivity) (hx_nonneg m)
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (this n)) ?_
    gcongr
    exact x_summable.le_tsum n fun m _ ↦ this m
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
    ContinuousLinearMapClass F ℂ A₁ A₂ where
  map_continuous f := by
    have hbound : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C * ‖a‖ := by
      obtain ⟨C, h⟩ := exists_norm_apply_le (.ofClass f)
      exact ⟨C, h⟩
    exact (LinearMap.mkContinuousOfExistsBound (f : A₁ →ₗ[ℂ] A₂) hbound).continuous

end PositiveLinearMap

end CStarAlgebra

