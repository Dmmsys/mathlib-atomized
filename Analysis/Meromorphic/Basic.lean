/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Meromorphic functions

Main statements:

* `MeromorphicAt`: definition of meromorphy at a point
* `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`: `f` is meromorphic at `z₀` iff we have
  `f z = (z - z₀) ^ n • g z` on a punctured neighborhood of `z₀`, for some `n : ℤ`
  and `g` analytic at `z₀`.
-/

@[expose] public section

open Filter Metric Set

open scoped Pointwise Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]

/-- Meromorphy of `f` at `x` (more precisely, on a punctured neighbourhood of `x`; the value at
`x` itself is irrelevant). -/
@[fun_prop]
/-
**MeromorphicAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeromorphicAt (f : 𝕜 -> E) (x : 𝕜)
参数：f : 𝕜 -> E；x : 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Meromorphy of `f` at `x` (more precisely, on a punctured neighbourhood of `x`; t
he value at
`x` itself is irrelevant).
-/
def MeromorphicAt (f : 𝕜 → E) (x : 𝕜) :=
  ∃ (n : ℕ), AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x

@[fun_prop]
/-
**AnalyticAt.meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) : Me
romorphicAt f x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma AnalyticAt.meromorphicAt {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    MeromorphicAt f x :=
  ⟨0, by simpa only [pow_zero, one_smul]⟩

/-- Analogue of the principle of isolated zeros for an analytic function: if a function is
meromorphic at `z₀`, then either it is identically zero in a punctured neighborhood of `z₀`, or it
does not vanish there at all. -/
/-
**MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero {f : 𝕜 -> E} {z₀ : 
𝕜} (hf : MeromorphicAt f z₀) : (forallᶠ z in 𝓝[!=] z₀, f z = 0) ∨ (forallᶠ z in 
𝓝[!=] z₀, f z != 0)
参数：hf : MeromorphicAt f z₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`：eventually_eq_zero_
or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ∨ 
forallᶠ z in 𝓝[!=] z₀, f z != 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `smul_ne_zero_iff`：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0

--- 原说明 ---
Analogue of the principle of isolated zeros for an analytic function: if a funct
ion is
meromorphic at `z₀`, then either it is identically zero in a punctured neighborh
ood of `z₀`, or it
does not vanish there at all.
-/
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : MeromorphicAt f z₀) :
    (∀ᶠ z in 𝓝[≠] z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) := by
  obtain ⟨n, h⟩ := hf
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, ← sub_eq_zero] at h₂y
    exact smul_eq_zero_iff_right (pow_ne_zero n h₂y) |>.mp h₁y
  · right
    filter_upwards [h₂, self_mem_nhdsWithin] with y h₁y h₂y
    exact (smul_ne_zero_iff.1 h₁y).2

namespace MeromorphicAt

variable {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'} {G : ι → 𝕜 → E}

@[fun_prop]
/-
**MeromorphicAt.id** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：id (x : 𝕜) : MeromorphicAt id x
参数：x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
-/
lemma id (x : 𝕜) : MeromorphicAt id x := analyticAt_id.meromorphicAt

@[fun_prop, simp]
/-
**MeromorphicAt.const** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) x
参数：e : E；x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
-/
lemma const (e : E) (x : 𝕜) : MeromorphicAt (fun _ ↦ e) x :=
  analyticAt_const.meromorphicAt

variable {x : 𝕜}

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.add** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Mer
omorphicAt (f + g) x
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `Nat.le_max_right`：∀ (a b : ℕ), b ≤ max a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
-/
lemma add {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨max m n, ?_⟩
  have : (fun z ↦ (z - x) ^ max m n • (f + g) z) = fun z ↦ (z - x) ^ (max m n - m) •
      ((z - x) ^ m • f z) + (z - x) ^ (max m n - n) • ((z - x) ^ n • g z) := by
    simp_rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (Nat.le_max_left _ _),
      Nat.sub_add_cancel (Nat.le_max_right _ _), Pi.add_apply, smul_add]
  rw [this]
  exact (((analyticAt_id.sub analyticAt_const).pow _).smul hf).add
    (((analyticAt_id.sub analyticAt_const).pow _).smul hg)

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.smul** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 -> R} {g : 𝕜 -> E} (
hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : MeromorphicAt (f • g) x
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
-/
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
    {f : 𝕜 → R} {g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul hg with z
  rw [Pi.smul_apply', Pi.smul_apply', smul_smul_smul_comm, smul_eq_mul, pow_add]

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.const_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：const_smul [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 𝕜 -> E} (hf : MeromorphicAt 
f x) (c : R) : MeromorphicAt (c • f) x
参数：hf : MeromorphicAt f x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `AnalyticAt.fun_const_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 …
-/
lemma const_smul [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 𝕜 → E} (hf : MeromorphicAt f x) (c : R) :
    MeromorphicAt (c • f) x := by
  rcases hf with ⟨m, hf⟩
  exact ⟨m, by simpa [smul_comm _ c _] using hf.fun_const_smul⟩

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.mul** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Me
romorphicAt (f * g) x
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma mul {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x := by
  simpa using hf.smul hg

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
/-
**MeromorphicAt.prod** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : MeromorphicAt (∏ i in s
, F i) x
参数：hf : forall σ in s, MeromorphicAt (F σ) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用引理 `MeromorphicAt.mul`：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f * g) x
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
Finite products of meromorphic functions are meromorphic.
-/
theorem prod (hf : ∀ σ ∈ s, MeromorphicAt (F σ) x) :
    MeromorphicAt (∏ i ∈ s, F i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop]
/-
**MeromorphicAt.fun_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：fun_prod (h : forall σ in s, MeromorphicAt (F σ) x) : MeromorphicAt (fun z
 => ∏ n in s, F n z) x
参数：h : forall σ in s, MeromorphicAt (F σ) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicAt.prod`：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : M
eromorphicAt (∏ i in s, F i) x

--- 原说明 ---
Finite products of meromorphic functions are meromorphic.
-/
theorem fun_prod (h : ∀ σ ∈ s, MeromorphicAt (F σ) x) :
    MeromorphicAt (fun z ↦ ∏ n ∈ s, F n z) x := by
  convert! prod h (s := s)
  simp

/-- Finprods of meromorphic functions are meromorphic. -/
@[fun_prop]
/-
**MeromorphicAt.finprod** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：finprod {x : 𝕜} (hf : forall i, MeromorphicAt (F i) x) : MeromorphicAt (∏ᶠ
 i, F i) x
参数：hf : forall i, MeromorphicAt (F i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `MeromorphicAt.prod`：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : M
eromorphicAt (∏ i in s, F i) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_of_not_hasFiniteMulSupport`：finprod_of_not_hasFiniteMulSupport {
f : α -> M} (hf : ¬ f.HasFiniteMulSupport) : ∏ᶠ i, f i = 1

--- 原说明 ---
Finprods of meromorphic functions are meromorphic.
-/
theorem finprod {x : 𝕜} (hf : ∀ i, MeromorphicAt (F i) x) :
    MeromorphicAt (∏ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteMulSupport F
  · simpa [finprod_eq_prod F h₂f] using prod (by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₂f ▸ const (1 : 𝕜') x

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
/-
**MeromorphicAt.sum** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：sum (h : forall σ in s, MeromorphicAt (G σ) x) : MeromorphicAt (∑ n in s, 
G n) x
参数：h : forall σ in s, MeromorphicAt (G σ) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `MeromorphicAt.add`：add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f + g) x
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
Finite sums of meromorphic functions are meromorphic.
-/
theorem sum (h : ∀ σ ∈ s, MeromorphicAt (G σ) x) :
    MeromorphicAt (∑ n ∈ s, G n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    apply (h σ (Finset.mem_insert_self σ s)).add
      (hind (fun τ hτ ↦ h τ (Finset.mem_insert_of_mem hτ)))

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
/-
**MeromorphicAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：fun_sum (h : forall σ in s, MeromorphicAt (G σ) x) : MeromorphicAt (fun z 
=> ∑ n in s, G n z) x
参数：h : forall σ in s, MeromorphicAt (G σ) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicAt.sum`：sum (h : forall σ in s, MeromorphicAt (G σ) x) : Mero
morphicAt (∑ n in s, G n) x

--- 原说明 ---
Finite sums of meromorphic functions are meromorphic.
-/
theorem fun_sum (h : ∀ σ ∈ s, MeromorphicAt (G σ) x) :
    MeromorphicAt (fun z ↦ ∑ n ∈ s, G n z) x := by
  convert! sum h (s := s)
  simp

/-- Finsums of meromorphic functions are meromorphic. -/
@[fun_prop]
/-
**MeromorphicAt.finsum** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：finsum (hF : forall i, MeromorphicAt (F i) x) : MeromorphicAt (∑ᶠ i, F i) 
x
参数：hF : forall i, MeromorphicAt (F i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `MeromorphicAt.sum`：sum (h : forall σ in s, MeromorphicAt (G σ) x) : Mero
morphicAt (∑ n in s, G n) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsum_of_not_hasFiniteSupport`：∀ {α : Type u_1} {M : Type u_5} [inst : 
AddCommMonoid M] {f : α → M}, ¬Function.HasFiniteSupport f → ∑ᶠ (i : α), f i = 0

--- 原说明 ---
Finsums of meromorphic functions are meromorphic.
-/
theorem finsum (hF : ∀ i, MeromorphicAt (F i) x) :
    MeromorphicAt (∑ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteSupport F
  · simpa [finsum_eq_sum F h₂f] using sum (by aesop)
  · exact finsum_of_not_hasFiniteSupport h₂f ▸ const (0 : 𝕜') x

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.neg** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x
参数：hf : MeromorphicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
-/
lemma neg {f : 𝕜 → E} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]
/-
**MeromorphicAt.neg_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：neg_iff {f : 𝕜 -> E} : MeromorphicAt (-f) x ↔ MeromorphicAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
-/
lemma neg_iff {f : 𝕜 → E} :
    MeromorphicAt (-f) x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.sub** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：sub {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Mer
omorphicAt (f - g) x
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.add`：add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f + g) x
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
-/
lemma sub {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  convert hf.add hg.neg
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/--
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_add_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 `M
eromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if 
`g` is meromorphic
at `x`.
-/
lemma meromorphicAt_add_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h ↦ by simpa using h.sub hf, fun _ ↦ by fun_prop⟩

/--
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_fun_add_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空
间 `MeromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if 
`g` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_add_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (fun z ↦ f z + g z) x ↔ MeromorphicAt g x :=
  meromorphicAt_add_iff_meromorphicAt₁ hf

/--
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_add_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 `M
eromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if 
`f` is meromorphic
at `x`.
-/
lemma meromorphicAt_add_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt f x := by
  rw [add_comm]
  exact meromorphicAt_add_iff_meromorphicAt₁ hg

/--
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_fun_add_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空
间 `MeromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if 
`f` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_add_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z + g z) x ↔ MeromorphicAt f x :=
  meromorphicAt_add_iff_meromorphicAt₂ hg

/--
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_sub_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 `M
eromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if 
`g` is meromorphic
at `x`.
-/
lemma meromorphicAt_sub_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h ↦ by simpa using h.sub hf, fun _ ↦ by fun_prop⟩

/--
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空
间 `MeromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if 
`g` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_sub_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (fun z ↦ f z - g z) x ↔ MeromorphicAt g x :=
  meromorphicAt_sub_iff_meromorphicAt₁ hf

/--
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_sub_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 `M
eromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if 
`f` is meromorphic
at `x`.
-/
lemma meromorphicAt_sub_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt f x := by
  exact ⟨fun h ↦ by simpa using h.add hg, fun _ ↦ by fun_prop⟩

/--
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
/-
**MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空
间 `MeromorphicAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if 
`f` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_sub_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z - g z) x ↔ MeromorphicAt f x :=
  meromorphicAt_sub_iff_meromorphicAt₂ hg

/-- With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a punctured
neighbourhood of `x` (not on `f x`) -/
/-
**MeromorphicAt.congr** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[!=] x] g) : Me
romorphicAt g x
参数：hf : MeromorphicAt f x；hfg : f =ᶠ[𝓝[!=] x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventuallyEq_nhdsWithin_iff`：eventuallyEq_nhdsWithin_iff {f g : α -> β} 
{s : Set α} {a : α} : f =ᶠ[𝓝[s] a] g ↔ forallᶠ x in 𝓝 a, x in s -> f x = g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a
 punctured
neighbourhood of `x` (not on `f x`)
-/
lemma congr {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x := by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z ↦ z - x) x := by fun_prop
  refine (this.fun_smul hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_iff.mp hn), pow_succ', mul_smul]

/--
If two functions agree on a punctured neighborhood, then one is meromorphic iff the other is so.
-/
/-
**MeromorphicAt.meromorphicAt_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：meromorphicAt_congr {f g : 𝕜 -> E} (h : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f
 x ↔ MeromorphicAt g x
参数：h : f =ᶠ[𝓝[!=] x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If two functions agree on a punctured neighborhood, then one is meromorphic iff 
the other is so.
-/
lemma meromorphicAt_congr {f g : 𝕜 → E} (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

@[simp]
/-
**MeromorphicAt.update_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：update_iff [DecidableEq 𝕜] {f : 𝕜 -> E} {z w : 𝕜} {e : E} : MeromorphicAt 
(Function.update f w e) z ↔ MeromorphicAt f z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.meromorphicAt_congr`：meromorphicAt_congr {f g : 𝕜 -> E} (h
 : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x
· 使用引理 `Function.update_eventuallyEq_nhdsNE`：Function.update_eventuallyEq_nhdsNE
 {α β : Type*} [TopologicalSpace α] [T1Space α] [DecidableEq α] (f : α -> β) (a 
a' : α) (b : β) : Functio…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma update_iff [DecidableEq 𝕜] {f : 𝕜 → E} {z w : 𝕜} {e : E} :
    MeromorphicAt (Function.update f w e) z ↔ MeromorphicAt f z :=
  meromorphicAt_congr (Function.update_eventuallyEq_nhdsNE f w z e)

@[fun_prop]
/-
**MeromorphicAt.update** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：update [DecidableEq 𝕜] {f : 𝕜 -> E} {z} (hf : MeromorphicAt f z) (w e) : M
eromorphicAt (Function.update f w e) z
参数：hf : MeromorphicAt f z；w e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeromorphicAt.update_iff`：update_iff [DecidableEq 𝕜] {f : 𝕜 -> E} {z w :
 𝕜} {e : E} : MeromorphicAt (Function.update f w e) z ↔ MeromorphicAt f z
-/
lemma update [DecidableEq 𝕜] {f : 𝕜 → E} {z} (hf : MeromorphicAt f z) (w e) :
    MeromorphicAt (Function.update f w e) z :=
  update_iff.mpr hf

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.inv** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x
参数：hf : MeromorphicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventuallyEq_nhdsWithin_iff`：eventuallyEq_nhdsWithin_iff {f g : α -> β} 
{s : Set α} {a : α} : f =ᶠ[𝓝[s] a] g ↔ forallᶠ x in 𝓝 a, x in s -> f x = g x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Pi.inv_apply`：inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`：exists_eventuallyEq
_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) : (exists (n : Nat), exists (g : 
𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ …
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `ContinuousAt.eventually_ne`：ContinuousAt.eventually_ne [TopologicalSpace
 Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y} (hg1 : ContinuousAt g x) (hg2 : g x
 != y) : forallᶠ…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
（共 54 条，此处仅展示前 30 条）
-/
lemma inv {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x := by
  rcases hf with ⟨m, hf⟩
  by_cases h_eq : (fun z ↦ (z - x) ^ m • f z) =ᶠ[𝓝 x] 0
  · -- silly case: f locally 0 near x
    refine (MeromorphicAt.const 0 x).congr ?_
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [h_eq] with z hfz hz
    rw [Pi.inv_apply, (smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)).mp hfz,
      inv_zero]
  · -- interesting case: use local formula for `f`
    obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h_eq
    have : AnalyticAt 𝕜 (fun z ↦ (z - x) ^ (m + 1)) x :=
      (analyticAt_id.sub analyticAt_const).pow _
    -- use `m + 1` rather than `m` to damp out any silly issues with the value at `z = x`
    refine ⟨n + 1, (this.fun_smul <| hg_an.inv hg_ne).congr ?_⟩
    filter_upwards [hg_eq, hg_an.continuousAt.eventually_ne hg_ne] with z hfg hg_ne'
    rcases eq_or_ne z x with rfl | hz_ne
    · simp
    · replace hfg := congr_arg (·⁻¹) hfg
      simp only [smul_inv₀] at hfg
      rw [inv_smul_eq_iff₀ (pow_ne_zero m (sub_ne_zero.mpr hz_ne)), smul_comm,
        eq_inv_smul_iff₀ (pow_ne_zero n (sub_ne_zero.mpr hz_ne))] at hfg
      simp [pow_succ', mul_smul, hfg]

@[simp]
/-
**MeromorphicAt.inv_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：inv_iff {f : 𝕜 -> 𝕜'} : MeromorphicAt f⁻¹ x ↔ MeromorphicAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
-/
lemma inv_iff {f : 𝕜 → 𝕜'} :
    MeromorphicAt f⁻¹ x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.div** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：div {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Me
romorphicAt (f / g) x
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.mul`：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f * g) x
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma div {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f / g) x :=
  (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.pow** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：pow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat) : MeromorphicAt (f ^ 
n) x
参数：hf : MeromorphicAt f x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `MeromorphicAt.mul`：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f * g) x
-/
lemma pow {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x := by
  induction n with
  | zero => simpa only [pow_zero] using! MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using! hm.mul hf

@[to_fun (attr := fun_prop)]
/-
**MeromorphicAt.zpow** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicAt`。
形式化陈述：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int) : MeromorphicAt (f ^
 n) x
参数：hf : MeromorphicAt f x；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `MeromorphicAt.pow`：pow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat) 
: MeromorphicAt (f ^ n) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma zpow {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (n : ℤ) : MeromorphicAt (f ^ n) x := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

/-- If a function is meromorphic at a point, then it is continuous at nearby points. -/
/-
**MeromorphicAt.eventually_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt
`。
形式化陈述：eventually_continuousAt {f : 𝕜 -> E} (h : MeromorphicAt f x) : forallᶠ y i
n 𝓝[!=] x, ContinuousAt f y
参数：h : MeromorphicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `AnalyticAt.eventually_continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousAt.inv₀`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : Zero G₀] [in
st_1 : Inv G₀] [inst_2 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   {f : α → G₀}
 {a : α…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousAt.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `ContinuousAt.smul`：ContinuousAt.smul (hf : ContinuousAt f b) (hg : Conti
nuousAt g b) : ContinuousAt (f • g) b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is meromorphic at a point, then it is continuous at nearby points.
-/
theorem eventually_continuousAt {f : 𝕜 → E}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, ContinuousAt f y := by
  obtain ⟨n, h⟩ := h
  have : ∀ᶠ y in 𝓝[≠] x, ContinuousAt (fun z ↦ (z - x) ^ n • f z) y :=
    nhdsWithin_le_nhds h.eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'y
  have : ContinuousAt (fun z ↦ ((z - x) ^ n)⁻¹) y :=
    ContinuousAt.inv₀ (by fun_prop) (by simp [sub_eq_zero, h'y])
  apply (this.smul hy).congr
  filter_upwards [eventually_ne_nhds h'y] with z hz
  simp [smul_smul, hz, sub_eq_zero]

/-- In a complete space, a function which is meromorphic at a point is analytic at all nearby
points. The completeness assumption can be dispensed with if one assumes that `f` is meromorphic
on a set around `x`, see `MeromorphicOn.eventually_analyticAt`. -/
/-
**MeromorphicAt.eventually_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：eventually_analyticAt [CompleteSpace E] {f : 𝕜 -> E} (h : MeromorphicAt f 
x) : forallᶠ y in 𝓝[!=] x, AnalyticAt 𝕜 f y
参数：h : MeromorphicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AnalyticAt.eventually_analyticAt`：AnalyticAt.eventually_analyticAt (h : 
AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_ne_nhds`：eventually_ne_nhds [T1Space X] {a b : X} (h : a != b
) : forallᶠ x in 𝓝 a, x != b
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
In a complete space, a function which is meromorphic at a point is analytic at a
ll nearby
points. The completeness assumption can be dispensed with if one assumes that `f
` is meromorphic
on a set around `x`, see `MeromorphicOn.eventually_analyticAt`.
-/
theorem eventually_analyticAt [CompleteSpace E] {f : 𝕜 → E}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y := by
  obtain ⟨n, h⟩ := h
  apply AnalyticAt.eventually_analyticAt at h
  refine (h.filter_mono ?_).mp ?_
  · simp [nhdsWithin]
  · rw [eventually_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro y hy hf
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    have := ((analyticAt_id (𝕜 := 𝕜).sub analyticAt_const).pow n).inv
      (pow_ne_zero _ (sub_ne_zero_of_ne hy))
    apply (this.smul hf).congr ∘ (eventually_ne_nhds hy).mono
    intro z hz
    simp [smul_smul, hz, sub_eq_zero]
/-
**MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt** 是 Mathlib 中的一个引理，位于命名空间 
`MeromorphicAt`。
形式化陈述：iff_eventuallyEq_zpow_smul_analyticAt {f : 𝕜 -> E} : MeromorphicAt f x ↔ e
xists (n : Int) (g : 𝕜 -> E), AnalyticAt 𝕜 g x ∧ forallᶠ z in 𝓝[!=] x, f z = (z 
- x) ^ n • g z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
（共 35 条，此处仅展示前 30 条）
-/
lemma iff_eventuallyEq_zpow_smul_analyticAt {f : 𝕜 → E} : MeromorphicAt f x ↔
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ ↦ MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpow _).smul hg_an.meromorphicAt

/--
Derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop]
/-
**MeromorphicAt.deriv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 →
 E} {x : 𝕜}, MeromorphicAt f x → MeromorphicAt (deriv f) x
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`：iff_eventuallyEq_zp
ow_smul_analyticAt {f : 𝕜 -> E} : MeromorphicAt f x ↔ exists (n : Int) (g : 𝕜 ->
 E), AnalyticAt 𝕜 g x ∧ forallᶠ z in 𝓝[!=…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `AnalyticAt.eventually_analyticAt`：AnalyticAt.eventually_analyticAt (h : 
AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `deriv_fun_smul`：deriv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : Diffe
rentiableAt 𝕜 f x) : deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x 
• f …
· 使用定理 `DifferentiableAt.zpow`：DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f 
a) (h : f a != 0 ∨ 0 <= m) : DifferentiableAt 𝕜 (fun x => f x ^ m) a
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `deriv_comp_sub_const`：deriv_comp_sub_const : deriv (fun x => f (x - a)) 
x = deriv f (x - a)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_zpow'`：deriv_zpow' (m : Int) : (deriv fun x : 𝕜 => x ^ m) = fun x 
=> (m : 𝕜) * x ^ (m - 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.meromorphicAt_congr`：meromorphicAt_congr {f g : 𝕜 -> E} (h
 : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x
· 使用定理 `Filter.EventuallyEq.nhdsNE_deriv`：Filter.EventuallyEq.nhdsNE_deriv (h : 
f₁ =ᶠ[𝓝[!=] x] f) : deriv f₁ =ᶠ[𝓝[!=] x] deriv f
· 使用定理 `MeromorphicAt.fun_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用定理 `MeromorphicAt.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{R : Type u_…
· 使用定理 `MeromorphicAt.fun_mul`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgeb
ra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Derivatives of meromorphic functions are meromorphic.
-/
protected theorem deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} (h : MeromorphicAt f x) :
    MeromorphicAt (deriv f) x := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at h
  obtain ⟨n, g, h₁g, h₂g⟩ := h
  have : _root_.deriv (fun z ↦ (z - x) ^ n • g z)
      =ᶠ[𝓝[≠] x] fun z ↦ (n * (z - x) ^ (n - 1)) • g z + (z - x) ^ n • _root_.deriv g z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁g.eventually_analyticAt,
      eventually_nhdsWithin_of_forall fun _ a ↦ a] with z₀ h₁ h₂
    rw [deriv_fun_smul (DifferentiableAt.zpow (by fun_prop) (by simp_all [sub_ne_zero_of_ne h₂]))
      (by fun_prop), add_comm, deriv_comp_sub_const (f := (· ^ n))]
    aesop
  rw [MeromorphicAt.meromorphicAt_congr (Filter.EventuallyEq.nhdsNE_deriv h₂g),
    MeromorphicAt.meromorphicAt_congr this]
  fun_prop

/--
Iterated derivatives of meromorphic functions are meromorphic.
-/
/-
**MeromorphicAt.iterated_deriv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [CompleteSpace E] {n : ℕ} 
{f : 𝕜 → E} {x : 𝕜},   MeromorphicAt f x → MeromorphicAt (deriv^[n] f) x
参数：deriv^[n] f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `MeromorphicAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [Co
mpleteSpa…

--- 原说明 ---
Iterated derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop] theorem iterated_deriv [CompleteSpace E] {n : ℕ} {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) :
    MeromorphicAt (_root_.deriv^[n] f) x := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

/-- If `f` is meromorphic at a point, then so is its logarithmic derivative. -/
/-
**MeromorphicAt.logDeriv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {x : 𝕜} [Complet
eSpace 𝕜'] {f : 𝕜 → 𝕜'},   MeromorphicAt f x → MeromorphicAt (logDeriv f) x
参数：logDeriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.div`：div {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f / g) x
· 使用定理 `MeromorphicAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [Co
mpleteSpa…

--- 原说明 ---
If `f` is meromorphic at a point, then so is its logarithmic derivative.
-/
@[fun_prop] theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) :
    MeromorphicAt (logDeriv f) x := hf.deriv.div hf

end MeromorphicAt

section smul_iff

variable {g : 𝕜 → 𝕜} {x : 𝕜}

/-
**meromorphicAt_smul_iff_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicAt_smul_iff_of_ne_zero {f : 𝕜 -> E} (hg : AnalyticAt 𝕜 g x) (hg
' : g x != 0) : MeromorphicAt (g • f) x ↔ MeromorphicAt f x
参数：hg : AnalyticAt 𝕜 g x；hg' : g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma meromorphicAt_smul_iff_of_ne_zero {f : 𝕜 → E} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    MeromorphicAt (g • f) x ↔ MeromorphicAt f x := by
  refine ⟨fun hfg ↦ ?_, hg.meromorphicAt.smul⟩
  refine (hg.inv hg').meromorphicAt.smul hfg |>.congr ?_
  filter_upwards [(hg.continuousAt.mono_left nhdsWithin_le_nhds).eventually_ne hg'] with z hz
  simp [inv_smul_smul₀ hz]
/-
**meromorphicAt_mul_iff_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicAt_mul_iff_of_ne_zero {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg'
 : g x != 0) : MeromorphicAt (g * f) x ↔ MeromorphicAt f x
参数：hg : AnalyticAt 𝕜 g x；hg' : g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `meromorphicAt_smul_iff_of_ne_zero`：meromorphicAt_smul_iff_of_ne_zero {f 
: 𝕜 -> E} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) : MeromorphicAt (g • f) x ↔ M
eromorphicAt f x
-/
lemma meromorphicAt_mul_iff_of_ne_zero {f : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    MeromorphicAt (g * f) x ↔ MeromorphicAt f x :=
  meromorphicAt_smul_iff_of_ne_zero hg hg'

end smul_iff

section composition
/-!
### Composition with an analytic function
-/

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : 𝕜}

/-- The composition of a meromorphic and an analytic function is meromorphic. -/
@[fun_prop]
/-
**MeromorphicAt.comp_analyticAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.comp_analyticAt {f : 𝕜' -> F} {g : 𝕜 -> 𝕜'} (hf : Meromorphi
cAt f (g x)) (hg : AnalyticAt 𝕜 g x) : MeromorphicAt (f ∘ g) x
参数：hf : MeromorphicAt f (g x)；hg : AnalyticAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `WithTop.ne_top_iff_exists`：∀ {α : Type u_1} {x : WithTop α}, x ≠ ⊤ ↔ ∃ a
, ↑a = x
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `AnalyticAt.restrictScalars`：AnalyticAt.restrictScalars (hf : AnalyticAt 
𝕜' f x) : AnalyticAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The composition of a meromorphic and an analytic function is meromorphic.
-/
lemma MeromorphicAt.comp_analyticAt {f : 𝕜' → F} {g : 𝕜 → 𝕜'}
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicAt (f ∘ g) x := by
  obtain ⟨r, hr⟩ := hf
  by_cases hg' : analyticOrderAt (g · - g x) x = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| analyticOrderAt_eq_top.mp hg'] with z hz
    grind
  · -- interesting case: `g z - g x` looks like `(z - x) ^ n` times a non-vanishing function
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hg'
    obtain ⟨h, han, hne, heq⟩ := (hg.fun_sub analyticAt_const).analyticOrderAt_eq_natCast.mp hn.symm
    set j := fun z ↦ (z - g x) ^ r • f z
    have : AnalyticAt 𝕜 (fun i ↦ (h i)⁻¹ ^ r • j (g i)) x :=
      ((han.inv hne).pow r).smul (hr.restrictScalars.comp hg)
    refine ⟨n * r, this.congr ?_⟩
    filter_upwards [heq, han.continuousAt.tendsto.eventually_ne hne] with z hz hzne
    simp only [j, inv_pow, Function.comp_apply, inv_smul_eq_iff₀ (pow_ne_zero r hzne)]
    rw [hz, smul_comm, ← smul_assoc, pow_mul, smul_pow]
/-
**meromorphicAt_comp_iff_of_deriv_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f 
: 𝕜 -> E} {g : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0) : Meromorp
hicAt (f ∘ g) x ↔ MeromorphicAt f (g x)
参数：hg : AnalyticAt 𝕜 g x；hg' : deriv g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.hasStrictDerivAt`：AnalyticAt.hasStrictDerivAt {f : 𝕜 -> F} {x
 : 𝕜} (hf : AnalyticAt 𝕜 f x) : HasStrictDerivAt f (deriv f x) x
· 使用引理 `AnalyticAt.analyticAt_localInverse`：analyticAt_localInverse (hf : Analyt
icAt 𝕜 f x) (hf' : deriv f x != 0) : AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInve
rse _ _ _ hf') (f x)
· 使用定理 `HasStrictFDerivAt.localInverse_apply_image`：localInverse_apply_image (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : hf.localInverse f f' a (f a) = a
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `MeromorphicAt.comp_analyticAt`：MeromorphicAt.comp_analyticAt {f : 𝕜' -> 
F} {g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) : Meromorp
hicAt (f ∘ g) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用引理 `HasStrictDerivAt.eventually_right_inverse`：eventually_right_inverse : fo
rallᶠ x in 𝓝 (f a), f (localInverse f f' a hf hf' x) = x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma meromorphicAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → E}
    {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    MeromorphicAt (f ∘ g) x ↔ MeromorphicAt f (g x) := by
  refine ⟨fun hf ↦ ?_, by fun_prop⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r (g x) := hg.analyticAt_localInverse hg'
  have : r (g x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hf
  refine (hf.comp_analyticAt hra).congr (.filter_mono ?_ nhdsWithin_le_nhds)
  exact EventuallyEq.fun_comp (HasStrictDerivAt.eventually_right_inverse ..) f

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_add_const_iff_meromorphicAt]
/-
**meromorphicAt_comp_add_const_iff_meromorphicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} : Mero
morphicAt (f ∘ (· + c)) x ↔ MeromorphicAt f (x + c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.comp_analyticAt`：MeromorphicAt.comp_analyticAt {f : 𝕜' -> 
F} {g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) : Meromorp
hicAt (f ∘ g) x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`MeromorphicAt` is invariant under translation.
-/
theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· + c)) x ↔ MeromorphicAt f (x + c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = ((f ∘ fun x ↦ x + c) ∘ fun z ↦ z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_sub_const_iff_meromorphicAt]
/-
**meromorphicAt_comp_sub_const_iff_meromorphicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} : Mero
morphicAt (f ∘ (· - c)) x ↔ MeromorphicAt f (x - c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`MeromorphicAt` is invariant under translation.
-/
theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· - c)) x ↔ MeromorphicAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicAt_comp_add_const_iff_meromorphicAt]

end composition


/-- Meromorphy of a function on a set. -/
/-
**MeromorphicOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeromorphicOn (f : 𝕜 -> E) (U : Set 𝕜) : Prop
参数：f : 𝕜 -> E；U : Set 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Meromorphy of a function on a set.
-/
def MeromorphicOn (f : 𝕜 → E) (U : Set 𝕜) : Prop := ∀ x ∈ U, MeromorphicAt f x
/-
**AnalyticOnNhd.meromorphicOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜
 f U) : MeromorphicOn f U
参数：hf : AnalyticOnNhd 𝕜 f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
-/
lemma AnalyticOnNhd.meromorphicOn {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U :=
  fun x hx ↦ (hf x hx).meromorphicAt

namespace MeromorphicOn

variable {s t : 𝕜 → 𝕜'} {f g : 𝕜 → E} {U : Set 𝕜}
  (hs : MeromorphicOn s U) (ht : MeromorphicOn t U)
  (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)

/--
If `f` is meromorphic on `U`, if `g` agrees with `f` on a codiscrete subset of `U` and outside of
`U`, then `g` is also meromorphic on `U`.
-/
/-
**MeromorphicOn.congr_codiscreteWithin_of_eqOn_compl** 是 Mathlib 中的一个定理，位于命名空间 `
MeromorphicOn`。
形式化陈述：congr_codiscreteWithin_of_eqOn_compl (hf : MeromorphicOn f U) (h₁ : f =ᶠ[c
odiscreteWithin U] g) (h₂ : Set.EqOn f g Uᶜ) : MeromorphicOn g U
参数：hf : MeromorphicOn f U；h₁ : f =ᶠ[codiscreteWithin U] g；h₂ : Set.EqOn f g Uᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f` is meromorphic on `U`, if `g` agrees with `f` on a codiscrete subset of `
U` and outside of
`U`, then `g` is also meromorphic on `U`.
-/
theorem congr_codiscreteWithin_of_eqOn_compl (hf : MeromorphicOn f U)
    (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ : Set.EqOn f g Uᶜ) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

/--
If `f` is meromorphic on an open set `U`, if `g` agrees with `f` on a codiscrete subset of `U`, then
`g` is also meromorphic on `U`.
-/
/-
**MeromorphicOn.congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`
。
形式化陈述：congr_codiscreteWithin (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithi
n U] g) (h₂ : IsOpen U) : MeromorphicOn g U
参数：hf : MeromorphicOn f U；h₁ : f =ᶠ[codiscreteWithin U] g；h₂ : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p

--- 原说明 ---
If `f` is meromorphic on an open set `U`, if `g` agrees with `f` on a codiscrete
 subset of `U`, then
`g` is also meromorphic on `U`.
-/
theorem congr_codiscreteWithin (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
  tauto

/--
If two functions differ only on a discrete set of an open, then one is meromorphic iff so is the
other.
-/
/-
**MeromorphicOn._root_.meromorphicOn_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位
于命名空间 `MeromorphicOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two functions differ only on a discrete set of an open, then one is meromorph
ic iff so is the
other.
-/
theorem _root_.meromorphicOn_congr_codiscreteWithin {f g : 𝕜 → E} (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn f U ↔ MeromorphicOn g U :=
  ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩
/-
**MeromorphicOn.id** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：id {U : Set 𝕜} : MeromorphicOn id U
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
-/
lemma id {U : Set 𝕜} : MeromorphicOn id U := fun x _ ↦ .id x
/-
**MeromorphicOn.const** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ => e) U
参数：e : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
-/
lemma const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ ↦ e) U :=
  fun x _ ↦ .const e x

section arithmetic

include hf in
/-
**MeromorphicOn.mono_set** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：mono_set {V : Set 𝕜} (hv : V subseteq U) : MeromorphicOn f V
参数：hv : V subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mono_set {V : Set 𝕜} (hv : V ⊆ U) : MeromorphicOn f V := fun x hx ↦ hf x (hv hx)

include hf hg in
/-
**MeromorphicOn.add** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f g : 𝕜 → E} {U : Set 𝕜},
 MeromorphicOn f U → MeromorphicOn g U → MeromorphicOn (f + g) U
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.add`：add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f + g) x
-/
@[to_fun] lemma add : MeromorphicOn (f + g) U := fun x hx ↦ (hf x hx).add (hg x hx)

include hf hg in
/-
**MeromorphicOn.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f g : 𝕜 → E} {U : Set 𝕜},
 MeromorphicOn f U → MeromorphicOn g U → MeromorphicOn (f - g) U
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.sub`：sub {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f - g) x
-/
@[to_fun] lemma sub : MeromorphicOn (f - g) U := fun x hx ↦ (hf x hx).sub (hg x hx)

include hf in
/-
**MeromorphicOn.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}, M
eromorphicOn f U → MeromorphicOn (-f) U
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
-/
@[to_fun] lemma neg : MeromorphicOn (-f) U := fun x hx ↦ (hf x hx).neg
/-
**MeromorphicOn.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}, M
eromorphicOn (-f) U ↔ MeromorphicOn f U
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeromorphicOn.neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 
𝕜 → E} …
-/
@[simp] lemma neg_iff : MeromorphicOn (-f) U ↔ MeromorphicOn f U :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

@[to_fun]
/-
**MeromorphicOn.smul** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 𝕜 -> R} (hs : Meromorp
hicOn s U) {f : 𝕜 -> E} (hf : MeromorphicOn f U) : MeromorphicOn (s • f) U
参数：hs : MeromorphicOn s U；hf : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
-/
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 𝕜 → R} (hs : MeromorphicOn s U)
    {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    MeromorphicOn (s • f) U :=
  fun x hx ↦ (hs x hx).smul (hf x hx)

include hf in
/-
**MeromorphicOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {R : Type u_4} [inst_3 : N
ormedRing R] [inst_4 : _root_.Module R E] [IsBoundedSMul R E]   {f : 𝕜 → E} {U :
 Set 𝕜}, MeromorphicOn f U → ∀ [SMulCommClass 𝕜 R E] (c : R), MeromorphicOn (c •
 f) U
参数：c : R；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.const_smul`：const_smul [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 
𝕜 -> E} (hf : MeromorphicAt f x) (c : R) : MeromorphicAt (c • f) x
-/
@[to_fun] lemma const_smul [SMulCommClass 𝕜 R E] (c : R) : MeromorphicOn (c • f) U :=
  fun x hx ↦ (hf x hx).const_smul c

include hs ht in
/-
**MeromorphicOn.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {s t : 𝕜 → 𝕜'} {
U : Set 𝕜},   MeromorphicOn s U → MeromorphicOn t U → MeromorphicOn (s * t) U
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.mul`：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f * g) x
-/
@[to_fun] lemma mul : MeromorphicOn (s * t) U := fun x hx ↦ (hs x hx).mul (ht x hx)

/-- Finite products of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.prod** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'} (h : forall
 σ in s, MeromorphicOn (f σ) U) : MeromorphicOn (∏ n in s, f n) U
参数：h : forall σ in s, MeromorphicOn (f σ) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.prod`：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : M
eromorphicAt (∏ i in s, F i) x

--- 原说明 ---
Finite products of meromorphic functions are meromorphic.
-/
lemma prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.prod (h · · z hz)

/-- Finite products of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.fun_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'} (h : fo
rall σ in s, MeromorphicOn (f σ) U) : MeromorphicOn (fun z => ∏ n in s, f n z) U
参数：h : forall σ in s, MeromorphicOn (f σ) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.fun_prod`：fun_prod (h : forall σ in s, MeromorphicAt (F σ)
 x) : MeromorphicAt (fun z => ∏ n in s, F n z) x

--- 原说明 ---
Finite products of meromorphic functions are meromorphic.
-/
lemma fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∏ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_prod (h · · z hz)

/-- Finprods of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.finprod** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：finprod {U : Set 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜'} (h : forall σ, Meromorp
hicOn (f σ) U) : MeromorphicOn (∏ᶠ n, f n) U
参数：h : forall σ, MeromorphicOn (f σ) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.finprod`：finprod {x : 𝕜} (hf : forall i, MeromorphicAt (F 
i) x) : MeromorphicAt (∏ᶠ i, F i) x

--- 原说明 ---
Finprods of meromorphic functions are meromorphic.
-/
lemma finprod {U : Set 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜'} (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ᶠ n, f n) U :=
  fun z hz ↦ MeromorphicAt.finprod (h · z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.sum** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> E} (h : forall σ
 in s, MeromorphicOn (f σ) U) : MeromorphicOn (∑ n in s, f n) U
参数：h : forall σ in s, MeromorphicOn (f σ) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.sum`：sum (h : forall σ in s, MeromorphicAt (G σ) x) : Mero
morphicAt (∑ n in s, G n) x

--- 原说明 ---
Finite sums of meromorphic functions are meromorphic.
-/
lemma sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.sum (h · · z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.fun_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> E} (h : fora
ll σ, MeromorphicOn (f σ) U) : MeromorphicOn (fun z => ∑ n in s, f n z) U
参数：h : forall σ, MeromorphicOn (f σ) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.fun_sum`：fun_sum (h : forall σ in s, MeromorphicAt (G σ) x
) : MeromorphicAt (fun z => ∑ n in s, G n z) x

--- 原说明 ---
Finite sums of meromorphic functions are meromorphic.
-/
lemma fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∑ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_sum (fun σ _ ↦ h σ z hz)

/-- Finsums of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.finsum** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：finsum {U : Set 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜'} (h : forall σ, Meromorph
icOn (f σ) U) : MeromorphicOn (∑ᶠ n, f n) U
参数：h : forall σ, MeromorphicOn (f σ) U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.finsum`：finsum (hF : forall i, MeromorphicAt (F i) x) : Me
romorphicAt (∑ᶠ i, F i) x

--- 原说明 ---
Finsums of meromorphic functions are meromorphic.
-/
lemma finsum {U : Set 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜'} (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ᶠ n, f n) U :=
  fun z hz ↦ MeromorphicAt.finsum (h · z hz)

include hs in
/-
**MeromorphicOn.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {s : 𝕜 → 𝕜'} {U 
: Set 𝕜}, MeromorphicOn s U → MeromorphicOn s⁻¹ U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
-/
@[to_fun] lemma inv : MeromorphicOn s⁻¹ U := fun x hx ↦ (hs x hx).inv
/-
**MeromorphicOn.inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {s : 𝕜 → 𝕜'} {U 
: Set 𝕜}, MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeromorphicOn.inv`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivially
NormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜
 𝕜'] {s…
-/
@[simp] lemma inv_iff : MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in
/-
**MeromorphicOn.div** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {s t : 𝕜 → 𝕜'} {
U : Set 𝕜},   MeromorphicOn s U → MeromorphicOn t U → MeromorphicOn (s / t) U
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.div`：div {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f / g) x
-/
@[to_fun] lemma div : MeromorphicOn (s / t) U := fun x hx ↦ (hs x hx).div (ht x hx)

include hs in
/-
**MeromorphicOn.pow** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {s : 𝕜 → 𝕜'} {U 
: Set 𝕜}, MeromorphicOn s U → ∀ (n : ℕ), MeromorphicOn (s ^ n) U
参数：n : ℕ；s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.pow`：pow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat) 
: MeromorphicAt (f ^ n) x
-/
@[to_fun] lemma pow (n : ℕ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).pow _

include hs in
/-
**MeromorphicOn.zpow** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {s : 𝕜 → 𝕜'} {U 
: Set 𝕜}, MeromorphicOn s U → ∀ (n : ℤ), MeromorphicOn (s ^ n) U
参数：n : ℤ；s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
-/
@[to_fun] lemma zpow (n : ℤ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).zpow _

include hf in
/-- Derivatives of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.deriv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}, M
eromorphicOn f U → ∀ [CompleteSpace E], MeromorphicOn (deriv f) U
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [Co
mpleteSpa…

--- 原说明 ---
Derivatives of meromorphic functions are meromorphic.
-/
protected theorem deriv [CompleteSpace E] : MeromorphicOn (deriv f) U := fun z hz ↦ (hf z hz).deriv

include hf in
/-- Iterated derivatives of meromorphic functions are meromorphic. -/
/-
**MeromorphicOn.iterated_deriv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：iterated_deriv [CompleteSpace E] {n : Nat} : MeromorphicOn (_root_.deriv^[
n] f) U
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.iterated_deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] [CompleteSpa…

--- 原说明 ---
Iterated derivatives of meromorphic functions are meromorphic.
-/
theorem iterated_deriv [CompleteSpace E] {n : ℕ} : MeromorphicOn (_root_.deriv^[n] f) U :=
  fun z hz ↦ (hf z hz).iterated_deriv

/-- If `f` is meromorphic on a set, then so is its logarithmic derivative. -/
/-
**MeromorphicOn.logDeriv** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {U : Set 𝕜} [Com
pleteSpace 𝕜'] {f : 𝕜 → 𝕜'} {hf : MeromorphicOn f U},   MeromorphicOn (logDeriv 
f) U
参数：logDeriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.div`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivially
NormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜
 𝕜'] {s…
· 使用定理 `MeromorphicOn.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f 
: 𝕜 → E} …

--- 原说明 ---
If `f` is meromorphic on a set, then so is its logarithmic derivative.
-/
protected theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'} {hf : MeromorphicOn f U} :
    MeromorphicOn (logDeriv f) U := hf.deriv.div hf
/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_add_const_iff_meromorphicOn]
/-
**MeromorphicOn.meromorphicOn_comp_add_const_iff_meromorphicOn** 是 Mathlib 中的一个定
理，位于命名空间 `MeromorphicOn`。
形式化陈述：meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} : Merom
orphicOn (f ∘ (· + c)) U ↔ MeromorphicOn f (U + {c})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.add_singleton`：∀ {α : Type u_2} [inst : Add α] {s : Set α} {b : α}, 
s + {b} = (fun x => x + b) '' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicAt_comp_add_const_iff_meromorphicAt`：meromorphicAt_comp_add_c
onst_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} : MeromorphicAt (f ∘ (· + c)) x ↔ Me
romorphicAt f (x + c)
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
`MeromorphicOn` is invariant under translation.
-/
theorem meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· + c)) U ↔ MeromorphicOn f (U + {c}) := by
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicAt_comp_add_const_iff_meromorphicAt] using h x h₁x
  · rw [meromorphicAt_comp_add_const_iff_meromorphicAt]
    aesop

/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_sub_const_iff_meromorphicOn]
/-
**MeromorphicOn.meromorphicOn_comp_sub_const_iff_meromorphicOn** 是 Mathlib 中的一个定
理，位于命名空间 `MeromorphicOn`。
形式化陈述：meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} : Merom
orphicOn (f ∘ (· - c)) U ↔ MeromorphicOn f (U - {c})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.neg_singleton`：∀ {α : Type u_2} [inst : InvolutiveNeg α] (a : α), -{
a} = {-a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`MeromorphicOn` is invariant under translation.
-/
theorem meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· - c)) U ↔ MeromorphicOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicOn_ball_fun_comp_sub_const_iff_meromorphicOn_ball]
/-
**MeromorphicOn.meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball** 是 Mat
hlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : Real
} : MeromorphicOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicOn f (ball 0 R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.meromorphicOn_comp_sub_const_iff_meromorphicOn`：meromorphi
cOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} : MeromorphicOn (f ∘ (·
 - c)) U ↔ MeromorphicOn f (U - {c})
· 使用定理 `ball_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (
δ : ℝ) (x y : E), Metric.ball x δ - {y} = Metric.ball (x - y) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`MeromorphicOn` is invariant under translation, special case where the set is a 
ball.
-/
theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicOn f (ball 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, ball_sub_singleton, sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall]
/-
**MeromorphicOn.meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closed
Ball** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall {c : 
𝕜} {R : Real} : MeromorphicOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicOn f (
closedBall 0 R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.meromorphicOn_comp_sub_const_iff_meromorphicOn`：meromorphi
cOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} : MeromorphicOn (f ∘ (·
 - c)) U ↔ MeromorphicOn f (U - {c})
· 使用定理 `closedBall_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGrou
p E] (δ : ℝ) (x y : E),   Metric.closedBall x δ - {y} = Metric.closedBall (x - y
) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`MeromorphicOn` is invariant under translation, special case where the set is a 
closed ball.
-/
theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicOn f (closedBall 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, closedBall_sub_singleton, sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicOn_sphere_fun_comp_sub_const_iff_meromorphicOn_sphere]
/-
**MeromorphicOn.meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere** 是
 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : 
Real} : MeromorphicOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicOn f (sphere 0 R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.meromorphicOn_comp_sub_const_iff_meromorphicOn`：meromorphi
cOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} : MeromorphicOn (f ∘ (·
 - c)) U ↔ MeromorphicOn f (U - {c})
· 使用定理 `sphere_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E]
 (δ : ℝ) (x y : E), Metric.sphere x δ - {y} = Metric.sphere (x - y) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`MeromorphicOn` is invariant under translation, special case where the set is a 
sphere.
-/
theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicOn f (sphere 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, sphere_sub_singleton, sub_self]

end arithmetic

include hf in
/-
**MeromorphicOn.congr** 是 Mathlib 中的一个引理，位于命名空间 `MeromorphicOn`。
形式化陈述：congr (h_eq : Set.EqOn f g U) (hu : IsOpen U) : MeromorphicOn g U
参数：h_eq : Set.EqOn f g U；hu : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma congr (h_eq : Set.EqOn f g U) (hu : IsOpen U) : MeromorphicOn g U := by
  refine fun x hx ↦ (hf x hx).congr (EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  exact eventually_of_mem (hu.mem_nhds hx) h_eq
/-
**MeromorphicOn.eventually_codiscreteWithin_analyticAt** 是 Mathlib 中的一个定理，位于命名空间
 `MeromorphicOn`。
形式化陈述：eventually_codiscreteWithin_analyticAt [CompleteSpace E] (f : 𝕜 -> E) (h :
 MeromorphicOn f U) : forallᶠ (y : 𝕜) in codiscreteWithin U, AnalyticAt 𝕜 f y
参数：f : 𝕜 -> E；h : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用引理 `mem_codiscreteWithin`：mem_codiscreteWithin {S T : Set X} : S in codiscre
teWithin T ↔ forall x in T, Disjoint (𝓝[!=] x) (𝓟 (T \ S))
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `MeromorphicAt.eventually_analyticAt`：eventually_analyticAt [CompleteSpac
e E] {f : 𝕜 -> E} (h : MeromorphicAt f x) : forallᶠ y in 𝓝[!=] x, AnalyticAt 𝕜 f
 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem eventually_codiscreteWithin_analyticAt
    [CompleteSpace E] (f : 𝕜 → E) (h : MeromorphicOn f U) :
    ∀ᶠ (y : 𝕜) in codiscreteWithin U, AnalyticAt 𝕜 f y := by
  rw [eventually_iff, mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  apply Filter.mem_of_superset ((h x hx).eventually_analyticAt)
  intro x hx
  simp [hx]

/--
The singular set of a meromorphic function is countable.
-/
/-
**MeromorphicOn.countable_compl_analyticAt_inter** 是 Mathlib 中的一个定理，位于命名空间 `Mero
morphicOn`。
形式化陈述：countable_compl_analyticAt_inter [SecondCountableTopology 𝕜] [CompleteSpac
e E] (h : MeromorphicOn f U) : ({z | AnalyticAt 𝕜 f z}ᶜ inter U).Countable
参数：h : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLindelof.countable_of_isDiscrete`：IsLindelof.countable_of_isDiscrete (
hs : IsLindelof s) (hs' : IsDiscrete s) : s.Countable
· 使用定理 `HereditarilyLindelofSpace.isLindelof`：HereditarilyLindelofSpace.isLindel
of [HereditarilyLindelofSpace X] (s : Set X) : IsLindelof s
· 使用定理 `SecondCountableTopology.toHereditarilyLindelof`：∀ {X : Type u} [inst : T
opologicalSpace X] [SecondCountableTopology X], HereditarilyLindelofSpace X
· 使用定理 `isDiscrete_of_codiscreteWithin`：isDiscrete_of_codiscreteWithin {U s : Se
t X} (h : sᶜ in Filter.codiscreteWithin U) : IsDiscrete (s inter U)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeromorphicOn.eventually_codiscreteWithin_analyticAt`：eventually_codiscr
eteWithin_analyticAt [CompleteSpace E] (f : 𝕜 -> E) (h : MeromorphicOn f U) : fo
rallᶠ (y : 𝕜) in codiscreteWithin U, Analy…

--- 原说明 ---
The singular set of a meromorphic function is countable.
-/
theorem countable_compl_analyticAt_inter [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | AnalyticAt 𝕜 f z}ᶜ ∩ U).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa using! eventually_codiscreteWithin_analyticAt f h

end MeromorphicOn

/-- Meromorphy of a function on all of 𝕜. -/
@[fun_prop]
/-
**Meromorphic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Meromorphic (f : 𝕜 -> E)
参数：f : 𝕜 -> E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Meromorphy of a function on all of 𝕜.
-/
def Meromorphic (f : 𝕜 → E) := ∀ x, MeromorphicAt f x

/-- A function is meromorphic iff it is meromorphic on Set.univ. -/
@[simp]
/-
**meromorphicOn_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Set.univ ↔ Meromorphic f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
A function is meromorphic iff it is meromorphic on Set.univ.
-/
lemma meromorphicOn_univ {f : 𝕜 → E} : MeromorphicOn f Set.univ ↔ Meromorphic f := by tauto

namespace Meromorphic

variable
  {ι : Type*} {s : Finset ι}
  {f g : 𝕜 → E} {F : ι → 𝕜 → 𝕜'} {G : ι → 𝕜 → E}

@[fun_prop]
/-
**Meromorphic.meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：meromorphicAt {x : 𝕜} (hf : Meromorphic f) : MeromorphicAt f x
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma meromorphicAt {x : 𝕜} (hf : Meromorphic f) : MeromorphicAt f x := hf x
/-
**Meromorphic.meromorphicOn** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f) : MeromorphicOn f s
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma meromorphicOn {s : Set 𝕜} (hf : Meromorphic f) : MeromorphicOn f s := fun x _ ↦ hf x

@[fun_prop]
/-
**Meromorphic.const** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：const (x : E) : Meromorphic fun _ : 𝕜 => x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
-/
lemma const (x : E) : Meromorphic fun _ : 𝕜 ↦ x := fun _ ↦ .const _ _

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.neg** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：neg (hf : Meromorphic f) : Meromorphic (-f)
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
-/
lemma neg (hf : Meromorphic f) : Meromorphic (-f) := fun x ↦ (hf x).neg

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.add** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：add (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphic (f + g)
参数：hf : Meromorphic f；hg : Meromorphic g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.add`：add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f + g) x
-/
lemma add (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f + g) := fun x ↦ (hf x).add (hg x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.sum** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：sum (h : forall σ in s, Meromorphic (G σ)) : Meromorphic (∑ n in s, G n)
参数：h : forall σ in s, Meromorphic (G σ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.sum`：sum (h : forall σ in s, MeromorphicAt (G σ) x) : Mero
morphicAt (∑ n in s, G n) x
-/
theorem sum (h : ∀ σ ∈ s, Meromorphic (G σ)) :
    Meromorphic (∑ n ∈ s, G n) := fun x ↦ MeromorphicAt.sum (h · · x)

@[fun_prop]
/-
**Meromorphic.finsum** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：finsum (h : forall σ, Meromorphic (F σ)) : Meromorphic (∑ᶠ σ, F σ)
参数：h : forall σ, Meromorphic (F σ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.finsum`：finsum (hF : forall i, MeromorphicAt (F i) x) : Me
romorphicAt (∑ᶠ i, F i) x
-/
theorem finsum (h : ∀ σ, Meromorphic (F σ)) :
    Meromorphic (∑ᶠ σ, F σ) := fun x ↦ MeromorphicAt.finsum (h · x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.sub** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：sub (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphic (f - g)
参数：hf : Meromorphic f；hg : Meromorphic g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.sub`：sub {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f - g) x
-/
lemma sub (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f - g) := fun x ↦ (hf x).sub (hg x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.smul** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 -> R} (hf : Meromorp
hic f) (hg : Meromorphic g) : Meromorphic (f • g)
参数：hf : Meromorphic f；hg : Meromorphic g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
-/
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 → R} (hf : Meromorphic f)
    (hg : Meromorphic g) :
    Meromorphic (f • g) := fun x ↦ (hf x).smul (hg x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.const_smul** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：const_smul [SMulCommClass 𝕜 R E] (hf : Meromorphic f) (c : R) : Meromorphi
c (c • f)
参数：hf : Meromorphic f；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.const_smul`：const_smul [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 
𝕜 -> E} (hf : MeromorphicAt f x) (c : R) : MeromorphicAt (c • f) x
-/
lemma const_smul [SMulCommClass 𝕜 R E] (hf : Meromorphic f) (c : R) :
    Meromorphic (c • f) := fun x ↦ (hf x).const_smul c

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.mul** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：mul {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphi
c (f * g)
参数：hf : Meromorphic f；hg : Meromorphic g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.mul`：mul {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f * g) x
-/
lemma mul {f g : 𝕜 → 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f * g) := fun x ↦ (hf x).mul (hg x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.inv** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：inv {f : 𝕜 -> 𝕜'} (hf : Meromorphic f) : Meromorphic f⁻¹
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
-/
lemma inv {f : 𝕜 → 𝕜'} (hf : Meromorphic f) : Meromorphic f⁻¹ := fun x ↦ (hf x).inv

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.prod** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：prod (h : forall σ in s, Meromorphic (F σ)) : Meromorphic (∏ n in s, F n)
参数：h : forall σ in s, Meromorphic (F σ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.prod`：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : M
eromorphicAt (∏ i in s, F i) x
-/
theorem prod (h : ∀ σ ∈ s, Meromorphic (F σ)) :
    Meromorphic (∏ n ∈ s, F n) := fun x ↦ MeromorphicAt.prod (h · · x)

@[fun_prop]
/-
**Meromorphic.finprod** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：finprod (h : forall σ, Meromorphic (F σ)) : Meromorphic (∏ᶠ σ, F σ)
参数：h : forall σ, Meromorphic (F σ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.finprod`：finprod {x : 𝕜} (hf : forall i, MeromorphicAt (F 
i) x) : MeromorphicAt (∏ᶠ i, F i) x
-/
theorem finprod (h : ∀ σ, Meromorphic (F σ)) :
    Meromorphic (∏ᶠ σ, F σ) := fun x ↦ MeromorphicAt.finprod (h · x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.div** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：div {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphi
c (f / g)
参数：hf : Meromorphic f；hg : Meromorphic g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.div`：div {f g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (hg : Me
romorphicAt g x) : MeromorphicAt (f / g) x
-/
lemma div {f g : 𝕜 → 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f / g) := fun x ↦ (hf x).div (hg x)

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.pow** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：pow {f : 𝕜 -> 𝕜'} {n : Nat} (hf : Meromorphic f) : Meromorphic (f ^ n)
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.pow`：pow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat) 
: MeromorphicAt (f ^ n) x
-/
lemma pow {f : 𝕜 → 𝕜'} {n : ℕ} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x ↦ (hf x).pow n

@[to_fun (attr := fun_prop)]
/-
**Meromorphic.zpow** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：zpow {f : 𝕜 -> 𝕜'} {n : Int} (hf : Meromorphic f) : Meromorphic (f ^ n)
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
-/
lemma zpow {f : 𝕜 → 𝕜'} {n : ℤ} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x ↦ (hf x).zpow n

@[fun_prop]
/-
**Meromorphic.deriv** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} [CompleteSpace
 E], Meromorphic f → Meromorphic (deriv f)
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [Co
mpleteSpa…
-/
protected lemma deriv [CompleteSpace E] (hf : Meromorphic f) : Meromorphic (deriv f) :=
  fun x ↦ (hf x).deriv

@[fun_prop]
/-
**Meromorphic.iterated_deriv** 是 Mathlib 中的一个引理，位于命名空间 `Meromorphic`。
形式化陈述：iterated_deriv [CompleteSpace E] {n : Nat} (hf : Meromorphic f) : Meromorp
hic (deriv^[n] f)
参数：hf : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.iterated_deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] [CompleteSpa…
-/
lemma iterated_deriv [CompleteSpace E] {n : ℕ} (hf : Meromorphic f) :
    Meromorphic (deriv^[n] f) := fun x ↦ (hf x).iterated_deriv

/-- If `f` is meromorphic, then so is its logarithmic derivative. -/
/-
**Meromorphic.logDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] [CompleteSpace 𝕜
'] {f : 𝕜 → 𝕜'}, Meromorphic f → Meromorphic (logDeriv f)
参数：logDeriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Meromorphic.div`：div {f g : 𝕜 -> 𝕜'} (hf : Meromorphic f) (hg : Meromorp
hic g) : Meromorphic (f / g)
· 使用定理 `Meromorphic.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 
𝕜 → E} …

--- 原说明 ---
If `f` is meromorphic, then so is its logarithmic derivative.
-/
@[fun_prop] protected theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'} (hf : Meromorphic f) :
    Meromorphic (logDeriv f) := hf.deriv.div hf

/--
If `f` is meromorphic, if `g` agrees with `f` on a codiscrete set, then `g` is also meromorphic.
-/
/-
**Meromorphic.congr_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：congr_codiscrete (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g) : Meromo
rphic g
参数：hf : Meromorphic f；h₁ : f =ᶠ[codiscrete 𝕜] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f
· 使用定理 `MeromorphicOn.congr_codiscreteWithin`：congr_codiscreteWithin (hf : Merom
orphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ : IsOpen U) : MeromorphicOn 
g U
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
If `f` is meromorphic, if `g` agrees with `f` on a codiscrete set, then `g` is a
lso meromorphic.
-/
theorem congr_codiscrete (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic g := by
  rw [← meromorphicOn_univ] at *
  exact hf.congr_codiscreteWithin (eventuallyEq_of_mem h₁ fun ⦃x⦄ a ↦ a) isOpen_univ

/--
If two functions differ only on a discrete set, then one is meromorphic iff so is the other.
-/
/-
**Meromorphic._root_.meromorphic_congr_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 `Mer
omorphic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two functions differ only on a discrete set, then one is meromorphic iff so i
s the other.
-/
theorem _root_.meromorphic_congr_codiscrete (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic f ↔ Meromorphic g :=
  ⟨(·.congr_codiscrete h₁), (·.congr_codiscrete h₁.symm)⟩

/--
The singular set of a meromorphic function is countable.
-/
/-
**Meromorphic.countable_compl_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`
。
形式化陈述：countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E] (
h : Meromorphic f) : {z | AnalyticAt 𝕜 f z}ᶜ.Countable
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `MeromorphicOn.countable_compl_analyticAt_inter`：countable_compl_analytic
At_inter [SecondCountableTopology 𝕜] [CompleteSpace E] (h : MeromorphicOn f U) :
 ({z | AnalyticAt 𝕜 f z}ᶜ inter U).C…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s

--- 原说明 ---
The singular set of a meromorphic function is countable.
-/
theorem countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : Meromorphic f) :
    {z | AnalyticAt 𝕜 f z}ᶜ.Countable := by
  simpa using (h.meromorphicOn (s := univ)).countable_compl_analyticAt_inter

/--
Meromorphic functions are measurable.
-/
/-
**Meromorphic.measurable** 是 Mathlib 中的一个定理，位于命名空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} [inst_3 : Meas
urableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]   [inst_6 : Measurable
Space E] [CompleteSpace E] [BorelSpace E], Meromorphic f → Measurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Meromorphic.countable_compl_analyticAt`：countable_compl_analyticAt [Seco
ndCountableTopology 𝕜] [CompleteSpace E] (h : Meromorphic f) : {z | AnalyticAt 𝕜
 f z}ᶜ.Countable
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `isOpen_analyticAt`：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用引理 `Measurable.of_union_range_cover`：Measurable.of_union_range_cover (hi₁ : 
MeasurableEmbedding i₁) (hi₂ : MeasurableEmbedding i₂) (h : univ subseteq range 
i₁ union range i₂) (h…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `measurable_of_countable`：measurable_of_countable [Countable α] [Measurab
leSingletonClass α] (f : α -> β) : Measurable f

--- 原说明 ---
Meromorphic functions are measurable.
-/
@[fun_prop] theorem measurable [MeasurableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [MeasurableSpace E] [CompleteSpace E] [BorelSpace E] (h : Meromorphic f) :
    Measurable f := by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable := by simpa using h.countable_compl_analyticAt
  have h₁' := h₁.to_subtype
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz ↦ hz.continuousAt.continuousWithinAt
  exact .of_union_range_cover (.subtype_coe h₂.measurableSet) (.subtype_coe h₁.measurableSet)
    (by simp [-mem_compl_iff]) h₃.domRestrict.measurable (measurable_of_countable _)

/-- `Meromorphic` is invariant under translation. -/
/-
**Meromorphic.meromorphic_comp_add_const_iff_meromorphic** 是 Mathlib 中的一个定理，位于命名
空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜}, Merom
orphic (f ∘ fun x => x + c) ↔ Meromorphic f
参数：f ∘ fun x => x + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Meromorphic.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜
 → E),…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.subRight_apply`：∀ {G : Type u_5} [inst : AddGroup G] (a b : G), (E
quiv.subRight a) b = b - a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Meromorphic` is invariant under translation.
-/
@[simp] theorem meromorphic_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· + c)) ↔ Meromorphic f := by
  rw [Meromorphic, Meromorphic, (Equiv.subRight c).surjective.forall]
  simp [meromorphicAt_comp_add_const_iff_meromorphicAt]

/-- `Meromorphic` is invariant under translation. -/
/-
**Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic** 是 Mathlib 中的一个定理，
位于命名空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜}, (Mero
morphic fun z => f (z + c)) ↔ Meromorphic f
参数：Meromorphic fun z => f (z + c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Meromorphic.meromorphic_comp_add_const_iff_meromorphic`：∀ {𝕜 : Type u_1}
 [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup 
E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …

--- 原说明 ---
`Meromorphic` is invariant under translation.
-/
@[simp] theorem meromorphic_fun_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z ↦ f (z + c)) ↔ Meromorphic f :=
  meromorphic_comp_add_const_iff_meromorphic

/-- `Meromorphic` is invariant under translation. -/
/-
**Meromorphic.meromorphic_comp_sub_const_iff_meromorphic** 是 Mathlib 中的一个定理，位于命名
空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜}, Merom
orphic (f ∘ fun x => x - c) ↔ Meromorphic f
参数：f ∘ fun x => x - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Meromorphic.meromorphic_comp_add_const_iff_meromorphic`：∀ {𝕜 : Type u_1}
 [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup 
E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Meromorphic` is invariant under translation.
-/
@[simp] theorem meromorphic_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· - c)) ↔ Meromorphic f := by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]

/-- `Meromorphic` is invariant under translation. -/
/-
**Meromorphic.meromorphic_fun_comp_sub_const_iff_meromorphic** 是 Mathlib 中的一个定理，
位于命名空间 `Meromorphic`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜}, (Mero
morphic fun z => f (z - c)) ↔ Meromorphic f
参数：Meromorphic fun z => f (z - c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Meromorphic.meromorphic_comp_sub_const_iff_meromorphic`：∀ {𝕜 : Type u_1}
 [inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup 
E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …

--- 原说明 ---
`Meromorphic` is invariant under translation.
-/
@[simp] theorem meromorphic_fun_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z ↦ f (z - c)) ↔ Meromorphic f :=
  meromorphic_comp_sub_const_iff_meromorphic

end Meromorphic

