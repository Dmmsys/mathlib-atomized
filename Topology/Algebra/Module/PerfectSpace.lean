/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Perfect

/-! # Vector spaces over nontrivially normed fields are perfect spaces -/

public section

open Filter Set
open scoped Topology

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nontrivial E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]

include 𝕜 in
/-
**perfectSpace_of_module** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：perfectSpace_of_module : PerfectSpace E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt_one`：exists_norm_lt_one : exists x : α, 0 < ‖
x‖ ∧ ‖x‖ < 1
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 40 条，此处仅展示前 30 条）
-/
lemma perfectSpace_of_module : PerfectSpace E := by
  refine ⟨fun x hx ↦ ?_⟩
  let ⟨r, hr₀, hr⟩ := NormedField.exists_norm_lt_one 𝕜
  obtain ⟨c, hc⟩ : ∃ (c : E), c ≠ 0 := exists_ne 0
  have A : Tendsto (fun (n : ℕ) ↦ x + r ^ n • c) atTop (𝓝 (x + (0 : 𝕜) • c)) := by
    apply Tendsto.add tendsto_const_nhds
    exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).smul tendsto_const_nhds
  have B : Tendsto (fun (n : ℕ) ↦ x + r ^ n • c) atTop (𝓝[univ \ {x}] x) := by
    simp only [zero_smul, add_zero] at A
    simp [tendsto_nhdsWithin_iff, A, hc, norm_pos_iff.mp hr₀]
  exact accPt_principal_iff_nhdsWithin.mpr ((atTop_neBot.map _).mono B)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PerfectSpace 𝕜 := perfectSpace_of_module 𝕜 𝕜
