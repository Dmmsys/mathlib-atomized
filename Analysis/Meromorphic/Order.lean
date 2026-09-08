/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Order.WithTop.Untop0

/-!
# Orders of Meromorphic Functions

This file defines the order of a meromorphic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

We characterize the order being `< 0`, or `= 0`, or `> 0`, as the convergence of the function
to infinity, resp. a nonzero constant, resp. zero.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {R : Type*} [NormedRing R] [NoZeroDivisors R]
  [Module R E] [IsBoundedSMul R E] [Module.IsTorsionFree R E]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f f₁ f₂ : 𝕜 → E} {x : 𝕜}

/-!
## Order at a Point: Definition and Characterization
-/

open scoped Classical in
/-- The order of a meromorphic function `f` at `z₀`, as an element of `ℤ ∪ {∞}`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `MeromorphicAt.meromorphicOrderAt_eq_top_iff` and
`MeromorphicAt.meromorphicOrderAt_eq_int_iff` for these equivalences.

If the function is not meromorphic at `x`, we use the junk value `0`. -/
/-
**meromorphicOrderAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：meromorphicOrderAt (f : 𝕜 -> E) (x : 𝕜) : WithTop Int
参数：f : 𝕜 -> E；x : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of a meromorphic function `f` at `z₀`, as an element of `ℤ ∪ {∞}`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀
`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, w
here `g` is analytic
and does not vanish at `z₀`. See `MeromorphicAt.meromorphicOrderAt_eq_top_iff` a
nd
`MeromorphicAt.meromorphicOrderAt_eq_int_iff` for these equivalences.

If the function is not meromorphic at `x`, we use the junk value `0`.
-/
noncomputable def meromorphicOrderAt (f : 𝕜 → E) (x : 𝕜) : WithTop ℤ :=
  if hf : MeromorphicAt f x then
    ((analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x).map (↑· : ℕ → ℤ)) - hf.choose
  else 0

@[simp]
/-
**meromorphicOrderAt_of_not_meromorphicAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_of_not_meromorphicAt (hf : ¬ MeromorphicAt f x) : merom
orphicOrderAt f x = 0
参数：hf : ¬ MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma meromorphicOrderAt_of_not_meromorphicAt (hf : ¬ MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 :=
  dif_neg hf
/-
**meromorphicAt_of_meromorphicOrderAt_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicAt_of_meromorphicOrderAt_ne_zero (hf : meromorphicOrderAt f x !
= 0) : MeromorphicAt f x
参数：hf : meromorphicOrderAt f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_of_not_meromorphicAt`：meromorphicOrderAt_of_not_merom
orphicAt (hf : ¬ MeromorphicAt f x) : meromorphicOrderAt f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma meromorphicAt_of_meromorphicOrderAt_ne_zero (hf : meromorphicOrderAt f x ≠ 0) :
    MeromorphicAt f x := by
  contrapose hf
  simp [hf]

/-- The order of a meromorphic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
/-
**meromorphicOrderAt_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_eq_top_iff : meromorphicOrderAt f x = ⊤ ↔ forallᶠ z in 
𝓝[!=] x, f z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.ne_top_iff_exists`：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m 
= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The order of a meromorphic function `f` at a `z₀` is infinity iff `f` vanishes l
ocally around
`z₀`.
-/
lemma meromorphicOrderAt_eq_top_iff :
    meromorphicOrderAt f x = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  by_cases hf : MeromorphicAt f x; swap
  · simp only [hf, not_false_eq_true, meromorphicOrderAt_of_not_meromorphicAt, WithTop.zero_ne_top,
      false_iff]
    contrapose hf
    exact (MeromorphicAt.const 0 x).congr (EventuallyEq.symm hf)
  simp only [meromorphicOrderAt, hf, ↓reduceDIte, sub_eq_top_iff, ENat.map_eq_top_iff,
    WithTop.natCast_ne_top, or_false]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.natCast_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz, smul_zero]
/-
**eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top : EventuallyConst
 f (𝓝[!=] x) ↔ exists c, meromorphicOrderAt (f · - c) x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top :
    EventuallyConst f (𝓝[≠] x) ↔ ∃ c, meromorphicOrderAt (f · - c) x = ⊤ := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff,
    sub_eq_zero, EventuallyEq]

/-- The order of a meromorphic function `f` at `z₀` equals an integer `n` iff `f` can locally be
written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
/-
**meromorphicOrderAt_eq_int_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_eq_int_iff {n : Int} (hf : MeromorphicAt f x) : meromor
phicOrderAt f x = n ↔ exists g : 𝕜 -> E, AnalyticAt 𝕜 g x ∧ g x != 0 ∧ forallᶠ z
 in 𝓝[!=] x, f z = (z - x) ^ n • g z
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ENat.map_top`：map_top (f : Nat -> α) : map f ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `WithTop.LinearOrderedAddCommGroup.top_sub`：∀ {G : Type u_1} [inst : AddC
ommGroup G] (x : WithTop G), ⊤ - x = ⊤
· 使用引理 `eq_false_intro`：eq_false_intro {a : Prop} (h : ¬a) : a = False
· 使用定理 `WithTop.top_ne_coe`：∀ {α : Type u_1} {a : α}, ⊤ ≠ ↑a
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `AnalyticAt.frequently_eq_iff_eventually_eq`：frequently_eq_iff_eventually
_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : (existsᶠ z in 𝓝[!=] z₀, 
f z = g z) ↔ forallᶠ z in 𝓝 z₀, …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The order of a meromorphic function `f` at `z₀` equals an integer `n` iff `f` ca
n locally be
written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish
 at `z₀`.
-/
lemma meromorphicOrderAt_eq_int_iff {n : ℤ} (hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔
    ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  simp only [meromorphicOrderAt, hf, ↓reduceDIte]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ ↦ hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h, ENat.map_natCast, ← WithTop.coe_natCast, ← coe_sub, WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hf.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    replace hg_eq : ∀ᶠ (z : 𝕜) in 𝓝[≠] x, f z = (z - x) ^ (↑m - ↑hf.choose : ℤ) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h ↦ ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` can locally be
written as `f z = (z - z₀) ^ order • g z`, where `g` is analytic and does not
vanish at `z₀`.
-/
/-
**meromorphicOrderAt_ne_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt f 
z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g 
z₀ != 0 ∧ f =ᶠ[𝓝[!=] z₀] fun z => (z - z₀) ^ ((meromorphicOrderAt f z₀).untop₀) 
• g z
参数：hf : MeromorphicAt f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithTop.coe_untop₀_of_ne_top`：coe_untop₀_of_ne_top {a : WithTop α} (ha :
 a != ⊤) : a.untop₀ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x

--- 原说明 ---
The order of a meromorphic function `f` at `z₀` is finite iff `f` can locally be
written as `f z = (z - z₀) ^ order • g z`, where `g` is analytic and does not
vanish at `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    meromorphicOrderAt f z₀ ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ ((meromorphicOrderAt f z₀).untop₀) • g z :=
  ⟨fun h ↦ (meromorphicOrderAt_eq_int_iff hf).1 (WithTop.coe_untop₀_of_ne_top h).symm,
    fun h ↦ Option.ne_none_iff_exists'.2
      ⟨(meromorphicOrderAt f z₀).untopD 0, (meromorphicOrderAt_eq_int_iff hf).2 h⟩⟩

/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` does not have
any zeros in a sufficiently small neighborhood of `z₀`.
-/
/-
**meromorphicOrderAt_ne_top_iff_eventually_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_ne_top_iff_eventually_ne_zero {f : 𝕜 -> E} (hf : Meromo
rphicAt f x) : meromorphicOrderAt f x != ⊤ ↔ forallᶠ x in 𝓝[!=] x, f x != 0
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `ContinuousAt.ne_iff_eventually_ne`：ContinuousAt.ne_iff_eventually_ne [T2
Space Y] {x : X} {f g : X -> Y} (hf : ContinuousAt f x) (hg : ContinuousAt g x) 
: f x != g x ↔ forallᶠ …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜

--- 原说明 ---
The order of a meromorphic function `f` at `z₀` is finite iff `f` does not have
any zeros in a sufficiently small neighborhood of `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff_eventually_ne_zero {f : 𝕜 → E} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x ≠ ⊤ ↔ ∀ᶠ x in 𝓝[≠] x, f x ≠ 0 := by
  constructor
  · intro h
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    filter_upwards [h₃g, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((h₁g.continuousAt.ne_iff_eventually_ne continuousAt_const).mp h₂g)]
    simp_all [zpow_ne_zero, sub_ne_zero]
  · simp_all [meromorphicOrderAt_eq_top_iff, Eventually.frequently]

/--
A function meromorphic on `U`, with meromorphic order nowhere `⊤`, is nonvanishing away from a
codiscrete subset of `U`.
-/
/-
**MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜
 -> E} (hf : MeromorphicOn f U) (h'f : forall x in U, meromorphicOrderAt f x != 
⊤) : forallᶠ x in codiscreteWithin U, f x != 0
参数：hf : MeromorphicOn f U；h'f : forall x in U, meromorphicOrderAt f x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff_eventually_ne_zero`：meromorphicOrderAt_ne_
top_iff_eventually_ne_zero {f : 𝕜 -> E} (hf : MeromorphicAt f x) : meromorphicOr
derAt f x != ⊤ ↔ forallᶠ x in 𝓝[!=] x,…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False

--- 原说明 ---
A function meromorphic on `U`, with meromorphic order nowhere `⊤`, is nonvanishi
ng away from a
codiscrete subset of `U`.
-/
theorem MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜 → E}
    (hf : MeromorphicOn f U) (h'f : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤) :
    ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  simp_rw [eventually_iff, mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x hx)).1 (h'f x hx)]
    with y hy
  simp [hy]

/-- If the order of a meromorphic function is negative, then this function converges to infinity
at this point. See also the iff version `tendsto_cobounded_iff_meromorphicOrderAt_neg`. -/
/-
**tendsto_cobounded_of_meromorphicOrderAt_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_cobounded_of_meromorphicOrderAt_neg (ho : meromorphicOrderAt f x <
 0) : Tendsto f (𝓝[!=] x) (Bornology.cobounded E)
参数：ho : meromorphicOrderAt f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `meromorphicAt_of_meromorphicOrderAt_ne_zero`：meromorphicAt_of_meromorphi
cOrderAt_ne_zero (hf : meromorphicOrderAt f x != 0) : MeromorphicAt f x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.ne_top_iff_exists`：∀ {α : Type u_1} {x : WithTop α}, x ≠ ⊤ ↔ ∃ a
, ↑a = x
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Filter.Tendsto.atTop_mul_pos`：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If the order of a meromorphic function is negative, then this function converges
 to infinity
at this point. See also the iff version `tendsto_cobounded_iff_meromorphicOrderA
t_neg`.
-/
lemma tendsto_cobounded_of_meromorphicOrderAt_neg (ho : meromorphicOrderAt f x < 0) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded E) := by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne
  simp only [← tendsto_norm_atTop_iff_cobounded]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have m_neg : m < 0 := by simpa [← hm] using ho
  rcases (meromorphicOrderAt_eq_int_iff hf).1 hm.symm with ⟨g, g_an, gx, hg⟩
  have A : Tendsto (fun z ↦ ‖(z - x) ^ m • g z‖) (𝓝[≠] x) atTop := by
    simp only [norm_smul]
    apply Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simp [gx]) _
      g_an.continuousAt.continuousWithinAt.tendsto.norm
    have : Tendsto (fun z ↦ z - x) (𝓝[≠] x) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z ↦ z - x) {x}ᶜ x := by fun_prop
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    exact (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded m_neg)).comp this
  apply A.congr'
  filter_upwards [hg] with z hz using by simp [hz]

/-- If the order of a meromorphic function is zero, then this function converges to a nonzero
limit at this point. See also the iff version `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`. -/
/-
**tendsto_ne_zero_of_meromorphicOrderAt_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_ne_zero_of_meromorphicOrderAt_eq_zero (hf : MeromorphicAt f x) (ho
 : meromorphicOrderAt f x = 0) : exists c != 0, Tendsto f (𝓝[!=] x) (𝓝 c)
参数：hf : MeromorphicAt f x；ho : meromorphicOrderAt f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the order of a meromorphic function is zero, then this function converges to 
a nonzero
limit at this point. See also the iff version `tendsto_ne_zero_iff_meromorphicOr
derAt_eq_zero`.
-/
lemma tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = 0) :
    ∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hg] with y hy using by simp [hy]

/-- If the order of a meromorphic function is positive, then this function converges to zero
at this point. See also the iff version `tendsto_zero_iff_meromorphicOrderAt_pos`. -/
/-
**tendsto_zero_of_meromorphicOrderAt_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_zero_of_meromorphicOrderAt_pos (ho : 0 < meromorphicOrderAt f x) :
 Tendsto f (𝓝[!=] x) (𝓝 0)
参数：ho : 0 < meromorphicOrderAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `meromorphicAt_of_meromorphicOrderAt_ne_zero`：meromorphicAt_of_meromorphi
cOrderAt_ne_zero (hf : meromorphicOrderAt f x != 0) : MeromorphicAt f x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `zero_pow_eq_zero`：zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ 
n != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousAt.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If the order of a meromorphic function is positive, then this function converges
 to zero
at this point. See also the iff version `tendsto_zero_iff_meromorphicOrderAt_pos
`.
-/
lemma tendsto_zero_of_meromorphicOrderAt_pos (ho : 0 < meromorphicOrderAt f x) :
    Tendsto f (𝓝[≠] x) (𝓝 0) := by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne'
  cases h'o : meromorphicOrderAt f x with
  | top =>
    apply tendsto_const_nhds.congr'
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h'o] with y hy using hy.symm
  | coe n =>
    rcases (meromorphicOrderAt_eq_int_iff hf).1 h'o with ⟨g, g_an, gx, hg⟩
    lift n to ℕ using by simpa [h'o] using ho.le
    have : (0 : E) = (x - x) ^ n • g x := by
      have : 0 < n := by simpa [h'o] using ho
      simp [zero_pow_eq_zero.2 this.ne']
    rw [this]
    have : ContinuousAt (fun z ↦ (z - x) ^ n • g z) x := by fun_prop
    apply this.continuousWithinAt.tendsto.congr'
    filter_upwards [hg] with y hy using by simp [hy]

/-- If the order of a meromorphic function is nonnegative, then this function converges
at this point. See also the iff version `tendsto_nhds_iff_meromorphicOrderAt_nonneg`. -/
/-
**tendsto_nhds_of_meromorphicOrderAt_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_nhds_of_meromorphicOrderAt_nonneg (hf : MeromorphicAt f x) (ho : 0
 <= meromorphicOrderAt f x) : exists c, Tendsto f (𝓝[!=] x) (𝓝 c)
参数：hf : MeromorphicAt f x；ho : 0 <= meromorphicOrderAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`：tendsto_ne_zero_of_meromo
rphicOrderAt_eq_zero (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = 0) 
: exists c != 0, Tendsto f (𝓝[!=] x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tendsto_zero_of_meromorphicOrderAt_pos`：tendsto_zero_of_meromorphicOrder
At_pos (ho : 0 < meromorphicOrderAt f x) : Tendsto f (𝓝[!=] x) (𝓝 0)

--- 原说明 ---
If the order of a meromorphic function is nonnegative, then this function conver
ges
at this point. See also the iff version `tendsto_nhds_iff_meromorphicOrderAt_non
neg`.
-/
lemma tendsto_nhds_of_meromorphicOrderAt_nonneg
    (hf : MeromorphicAt f x) (ho : 0 ≤ meromorphicOrderAt f x) :
    ∃ c, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases ho.eq_or_lt with ho | ho
  · rcases tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho.symm with ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · exact ⟨0, tendsto_zero_of_meromorphicOrderAt_pos ho⟩

/-- A meromorphic function converges to infinity iff its order is negative. -/
/-
**tendsto_cobounded_iff_meromorphicOrderAt_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_cobounded_iff_meromorphicOrderAt_neg (hf : MeromorphicAt f x) : Te
ndsto f (𝓝[!=] x) (Bornology.cobounded E) ↔ meromorphicOrderAt f x < 0
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用引理 `tendsto_nhds_of_meromorphicOrderAt_nonneg`：tendsto_nhds_of_meromorphicOr
derAt_nonneg (hf : MeromorphicAt f x) (ho : 0 <= meromorphicOrderAt f x) : exist
s c, Tendsto f (𝓝[!=] x) (𝓝 c)
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…

--- 原说明 ---
A meromorphic function converges to infinity iff its order is negative.
-/
lemma tendsto_cobounded_iff_meromorphicOrderAt_neg (hf : MeromorphicAt f x) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded E) ↔ meromorphicOrderAt f x < 0 := by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_cobounded_of_meromorphicOrderAt_neg]
  · simp only [lt_iff_not_ge, ho, not_true_eq_false, iff_false, ← tendsto_norm_atTop_iff_cobounded]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    exact not_tendsto_atTop_of_tendsto_nhds hc.norm

/-- A meromorphic function converges to a limit iff its order is nonnegative. -/
/-
**tendsto_nhds_iff_meromorphicOrderAt_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf : MeromorphicAt f x) : (exi
sts c, Tendsto f (𝓝[!=] x) (𝓝 c)) ↔ 0 <= meromorphicOrderAt f x
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用引理 `tendsto_cobounded_of_meromorphicOrderAt_neg`：tendsto_cobounded_of_meromo
rphicOrderAt_neg (ho : meromorphicOrderAt f x < 0) : Tendsto f (𝓝[!=] x) (Bornol
ogy.cobounded E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `tendsto_nhds_of_meromorphicOrderAt_nonneg`：tendsto_nhds_of_meromorphicOr
derAt_nonneg (hf : MeromorphicAt f x) (ho : 0 <= meromorphicOrderAt f x) : exist
s c, Tendsto f (𝓝[!=] x) (𝓝 c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A meromorphic function converges to a limit iff its order is nonnegative.
-/
lemma tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf : MeromorphicAt f x) :
    (∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ 0 ≤ meromorphicOrderAt f x := by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp only [← not_lt, ho, not_true_eq_false, iff_false, not_exists]
    intro c hc
    apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · simp [ho, tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho]

/-- A meromorphic function converges to a nonzero limit iff its order is zero. -/
/-
**tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf : MeromorphicAt f x) : 
(exists c != 0, Tendsto f (𝓝[!=] x) (𝓝 c)) ↔ meromorphicOrderAt f x = 0
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`：tendsto_ne_zero_of_meromo
rphicOrderAt_eq_zero (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = 0) 
: exists c != 0, Tendsto f (𝓝[!=] x…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用引理 `tendsto_cobounded_of_meromorphicOrderAt_neg`：tendsto_cobounded_of_meromo
rphicOrderAt_neg (ho : meromorphicOrderAt f x < 0) : Tendsto f (𝓝[!=] x) (Bornol
ogy.cobounded E)
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `tendsto_zero_of_meromorphicOrderAt_pos`：tendsto_zero_of_meromorphicOrder
At_pos (ho : 0 < meromorphicOrderAt f x) : Tendsto f (𝓝[!=] x) (𝓝 0)

--- 原说明 ---
A meromorphic function converges to a nonzero limit iff its order is zero.
-/
lemma tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf : MeromorphicAt f x) :
    (∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ meromorphicOrderAt f x = 0 := by
  rcases eq_or_ne (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho]
  simp only [ne_eq, ho, iff_false, not_exists, not_and]
  intro c c_ne hc
  rcases ho.lt_or_gt with ho | ho
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · apply c_ne
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos ho)

/-- A meromorphic function converges to zero iff its order is positive. -/
/-
**tendsto_zero_iff_meromorphicOrderAt_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_zero_iff_meromorphicOrderAt_pos (hf : MeromorphicAt f x) : (Tendst
o f (𝓝[!=] x) (𝓝 0)) ↔ 0 < meromorphicOrderAt f x
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `tendsto_zero_of_meromorphicOrderAt_pos`：tendsto_zero_of_meromorphicOrder
At_pos (ho : 0 < meromorphicOrderAt f x) : Tendsto f (𝓝[!=] x) (𝓝 0)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`：tendsto_ne_zero_of_meromo
rphicOrderAt_eq_zero (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = 0) 
: exists c != 0, Tendsto f (𝓝[!=] x…
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用引理 `tendsto_cobounded_of_meromorphicOrderAt_neg`：tendsto_cobounded_of_meromo
rphicOrderAt_neg (ho : meromorphicOrderAt f x < 0) : Tendsto f (𝓝[!=] x) (Bornol
ogy.cobounded E)

--- 原说明 ---
A meromorphic function converges to zero iff its order is positive.
-/
lemma tendsto_zero_iff_meromorphicOrderAt_pos (hf : MeromorphicAt f x) :
    (Tendsto f (𝓝[≠] x) (𝓝 0)) ↔ 0 < meromorphicOrderAt f x := by
  rcases lt_or_ge 0 (meromorphicOrderAt f x) with ho | ho
  · simp [ho, tendsto_zero_of_meromorphicOrderAt_pos ho]
  simp only [← not_le, ho, not_true_eq_false, iff_false]
  intro hc
  rcases ho.eq_or_lt with ho | ho
  · obtain ⟨c, c_ne, h'c⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho
    apply c_ne
    exact tendsto_nhds_unique h'c hc
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho

/-- Meromorphic functions that agree in a punctured neighborhood of `z₀` have the same order at
`z₀`. -/
/-
**meromorphicOrderAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicOrderAt f
₁ x = meromorphicOrderAt f₂ x
参数：hf₁₂ : f₁ =ᶠ[𝓝[!=] x] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `meromorphicOrderAt_of_not_meromorphicAt`：meromorphicOrderAt_of_not_merom
orphicAt (hf : ¬ MeromorphicAt f x) : meromorphicOrderAt f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Meromorphic functions that agree in a punctured neighborhood of `z₀` have the sa
me order at
`z₀`.
-/
theorem meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[≠] x] f₂) :
    meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x := by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ MeromorphicAt f₂ x := by
      contrapose hf₁
      exact hf₁.congr hf₁₂.symm
    simp [hf₁, this]
  rw [eq_comm]
  cases h₁f₁ : meromorphicOrderAt f₁ x with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h₁f₁ ⊢
    filter_upwards [hf₁₂, h₁f₁] using by grind
  | coe n =>
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 h₁f₁
    rw [meromorphicOrderAt_eq_int_iff (hf₁.congr hf₁₂)]
    use g, h₁g, h₂g
    filter_upwards [hf₁₂, h₃g] using by grind

/-- Compatibility of notions of `order` for analytic and meromorphic functions. -/
/-
**AnalyticAt.meromorphicOrderAt_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) : meromorphicOrde
rAt f x = (analyticOrderAt f x).map (↑)
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.map_top`：map_top (f : Nat -> α) : map f ⊤ = ⊤
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…

--- 原说明 ---
Compatibility of notions of `order` for analytic and meromorphic functions.
-/
lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x = (analyticOrderAt f x).map (↑) := by
  cases hn : analyticOrderAt f x
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact (analyticOrderAt_eq_top.mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_natCast, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

/--
When seen as meromorphic functions, analytic functions have nonnegative order.
-/
/-
**AnalyticAt.meromorphicOrderAt_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) : 0 <= meromo
rphicOrderAt f x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)

--- 原说明 ---
When seen as meromorphic functions, analytic functions have nonnegative order.
-/
theorem AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) :
    0 ≤ meromorphicOrderAt f x := by
  simp [hf.meromorphicOrderAt_eq]

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
/-
**MeromorphicAt.meromorphicOrderAt_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicOrderAt_nonneg_iff (hf : MeromorphicAt f x) : 0 <
= meromorphicOrderAt f x ↔ exists g : 𝕜 -> E, AnalyticAt 𝕜 g x ∧ f =ᶠ[𝓝[!=] x] g
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.zpow_nonneg`：AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n :
 Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AnalyticAt.meromorphicOrderAt_nonneg`：AnalyticAt.meromorphicOrderAt_nonn
eg (hf : AnalyticAt 𝕜 f x) : 0 <= meromorphicOrderAt f x

--- 原说明 ---
A meromorphic function has non-negative order iff there exists an analytic exten
sion.
-/
theorem MeromorphicAt.meromorphicOrderAt_nonneg_iff
    (hf : MeromorphicAt f x) :
    0 ≤ meromorphicOrderAt f x ↔ ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ f =ᶠ[𝓝[≠] x] g := by
  refine ⟨fun nneg ↦ ?_, fun ⟨g, hg₁, hg₂⟩ ↦ ?_⟩
  · cases h₀ : meromorphicOrderAt f x with
    | top => exact ⟨0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp h₀⟩
    | coe n =>
      obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
      refine ⟨fun z ↦ (z - x) ^ n • g z, ?_, hfg⟩
      exact (AnalyticAt.zpow_nonneg (by fun_prop) (by simpa [h₀] using nneg)).smul hg
  · simp [meromorphicOrderAt_congr hg₂, hg₁.meromorphicOrderAt_nonneg]

/-- If a function is both meromorphic and continuous at a point, then it is analytic there. -/
/-
**MeromorphicAt.analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}, Merom
orphicAt f x → ContinuousAt f x → AnalyticAt 𝕜 f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`：ContinuousAt.eve
ntuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X -> Y} (hf : 
ContinuousAt f x) (hg : ContinuousAt g x) [(…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `tendsto_nhds_iff_meromorphicOrderAt_nonneg`：tendsto_nhds_iff_meromorphic
OrderAt_nonneg (hf : MeromorphicAt f x) : (exists c, Tendsto f (𝓝[!=] x) (𝓝 c)) 
↔ 0 <= meromorphicOrderAt f x
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `ContinuousAt.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is both meromorphic and continuous at a point, then it is analytic
 there.
-/
protected theorem MeromorphicAt.analyticAt {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) (h' : ContinuousAt f x) :
    AnalyticAt 𝕜 f x := by
  cases ho : meromorphicOrderAt f x with
  | top =>
    /- If the order is infinite, then `f` vanishes on a pointed neighborhood of `x`. By continuity,
    it also vanishes at `x`.-/
    have : AnalyticAt 𝕜 (fun _ ↦ (0 : E)) x := analyticAt_const
    apply this.congr
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const h']
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 ho] with y hy using by simp [hy]
  | coe n =>
    /- If the order is finite, then the order has to be nonnegative, as otherwise the norm of `f`
    would tend to infinity at `x`. Then the local expression of `f` coming from its meromorphicity
    shows that it coincides with an analytic function close to `x`, except maybe at `x`. By
    continuity of `f`, the two functions also coincide at `x`. -/
    rcases (meromorphicOrderAt_eq_int_iff h).1 ho with ⟨g, g_an, gx, hg⟩
    have : 0 ≤ meromorphicOrderAt f x := by
      apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg h).1
      exact ⟨f x, h'.continuousWithinAt.tendsto⟩
    lift n to ℕ using by simpa [ho] using this
    have A : ∀ᶠ (z : 𝕜) in 𝓝 x, (z - x) ^ n • g z = f z := by
      apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) h').1
      filter_upwards [hg] with z hz using by simpa using hz.symm
    exact AnalyticAt.congr (by fun_prop) A
/-
**AnalyticAt.of_meromorphicOrderAt_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.of_meromorphicOrderAt_pos {f : 𝕜 -> E} {x : 𝕜} (h : 0 < meromor
phicOrderAt f x) (hf : f x = 0) : AnalyticAt 𝕜 f x
参数：h : 0 < meromorphicOrderAt f x；hf : f x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {f : 𝕜 → E} …
· 使用引理 `meromorphicAt_of_meromorphicOrderAt_ne_zero`：meromorphicAt_of_meromorphi
cOrderAt_ne_zero (hf : meromorphicOrderAt f x != 0) : MeromorphicAt f x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `continuousAt_iff_punctured_nhds`：continuousAt_iff_punctured_nhds [Topolo
gicalSpace β] {f : α -> β} {a : α} : ContinuousAt f a ↔ Tendsto f (𝓝[!=] a) (𝓝 (
f a))
· 使用引理 `tendsto_zero_of_meromorphicOrderAt_pos`：tendsto_zero_of_meromorphicOrder
At_pos (ho : 0 < meromorphicOrderAt f x) : Tendsto f (𝓝[!=] x) (𝓝 0)
-/
lemma AnalyticAt.of_meromorphicOrderAt_pos {f : 𝕜 → E} {x : 𝕜}
    (h : 0 < meromorphicOrderAt f x) (hf : f x = 0) :
    AnalyticAt 𝕜 f x := by
  refine (meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne').analyticAt ?_
  rw [continuousAt_iff_punctured_nhds, hf]
  exact tendsto_zero_of_meromorphicOrderAt_pos h

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
/-
**meromorphicOrderAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Decidable (e = 0)] : meromorphi
cOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 : WithTop Int)
参数：z₀ : 𝕜；e : E；e = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
The order of a constant function is `⊤` if the constant is zero and `0` otherwis
e.
-/
theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Decidable (e = 0)] :
    meromorphicOrderAt (fun _ ↦ e) z₀ = if e = 0 then ⊤ else (0 : WithTop ℤ) := by
  split_ifs with he
  · simp [he, meromorphicOrderAt_eq_top_iff]
  · exact (meromorphicOrderAt_eq_int_iff (.const e z₀)).2 ⟨fun _ ↦ e, by fun_prop, by simpa⟩

@[simp]
/-
**meromorphicOrderAt_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_id : meromorphicOrderAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticOrderAt_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜],
 analyticOrderAt id 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma meromorphicOrderAt_id : meromorphicOrderAt (𝕜 := 𝕜) id 0 = 1 := by
  simp [analyticAt_id.meromorphicOrderAt_eq]

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
/-
**meromorphicOrderAt_const_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_const_intCast (z₀ : 𝕜) (n : Int) [Decidable ((n : 𝕜') =
 0)] : meromorphicOrderAt (n : 𝕜 -> 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : Wi
thTop Int)
参数：z₀ : 𝕜；n : Int；(n : 𝕜') = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicOrderAt_const`：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Dec
idable (e = 0)] : meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 :
 WithTop Int)

--- 原说明 ---
The order of a constant function is `⊤` if the constant is zero and `0` otherwis
e.
-/
theorem meromorphicOrderAt_const_intCast (z₀ : 𝕜) (n : ℤ) [Decidable ((n : 𝕜') = 0)] :
    meromorphicOrderAt (n : 𝕜 → 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop ℤ) :=
  meromorphicOrderAt_const z₀ (n : 𝕜')

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
/-
**meromorphicOrderAt_const_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_const_natCast (z₀ : 𝕜) (n : Nat) [Decidable ((n : 𝕜') =
 0)] : meromorphicOrderAt (n : 𝕜 -> 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : Wi
thTop Int)
参数：z₀ : 𝕜；n : Nat；(n : 𝕜') = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicOrderAt_const`：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Dec
idable (e = 0)] : meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 :
 WithTop Int)

--- 原说明 ---
The order of a constant function is `⊤` if the constant is zero and `0` otherwis
e.
-/
theorem meromorphicOrderAt_const_natCast (z₀ : 𝕜) (n : ℕ) [Decidable ((n : 𝕜') = 0)] :
    meromorphicOrderAt (n : 𝕜 → 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop ℤ) :=
  meromorphicOrderAt_const z₀ (n : 𝕜')

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
/-
**meromorphicOrderAt_const_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_4} [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] (z₀ : 𝕜) (n : ℕ)
 [inst_3 : Decidable (↑n = 0)],   meromorphicOrderAt (OfNat.ofNat n) z₀ = if ↑n 
= 0 then ⊤ else 0
参数：z₀ : 𝕜；n : ℕ；↑n = 0；OfNat.ofNat n。
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
· 使用定理 `Semiring.toGrindSemiring_ofNat`：Semiring.toGrindSemiring_ofNat [Semiring
 α] (n : Nat) : @OfNat.ofNat α n (Lean.Grind.Semiring.ofNat n) = n.cast
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `meromorphicOrderAt_const`：meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Dec
idable (e = 0)] : meromorphicOrderAt (fun _ => e) z₀ = if e = 0 then ⊤ else (0 :
 WithTop Int)

--- 原说明 ---
The order of a constant function is `⊤` if the constant is zero and `0` otherwis
e.
-/
@[simp] theorem meromorphicOrderAt_const_ofNat (z₀ : 𝕜) (n : ℕ) [Decidable ((n : 𝕜') = 0)] :
    meromorphicOrderAt (ofNat(n) : 𝕜 → 𝕜') z₀ = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop ℤ) := by
  convert! meromorphicOrderAt_const z₀ (n : 𝕜')
  simp [Semiring.toGrindSemiring_ofNat 𝕜' n]

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
/-
**meromorphicOrderAt_zpow_id_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {n : ℤ},   mer
omorphicOrderAt ((fun x_1 => x_1 - x) ^ n) x = ↑n
参数：(fun x_1 => x_1 - x) ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The order of `(· - x) ^ n` at `x` is `n`.
-/
@[simp, to_fun] theorem meromorphicOrderAt_zpow_id_sub_const {n : ℤ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
  exact ⟨fun z ↦ 1, by fun_prop, one_ne_zero, by aesop⟩

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
/-
**meromorphicOrderAt_pow_id_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {n : ℕ},   mer
omorphicOrderAt ((fun x_1 => x_1 - x) ^ n) x = ↑n
参数：(fun x_1 => x_1 - x) ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `meromorphicOrderAt_zpow_id_sub_const`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {x : 𝕜} {n : ℤ},   meromorphicOrderAt ((fun x_1 => x_1 - x) ^ 
n) x = ↑n

--- 原说明 ---
The order of `(· - x) ^ n` at `x` is `n`.
-/
@[simp, to_fun] theorem meromorphicOrderAt_pow_id_sub_const {n : ℕ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  convert! meromorphicOrderAt_zpow_id_sub_const
  simp only [zpow_natCast]

/-- The order of `· - x` at `x` is `1`. -/
/-
**meromorphicOrderAt_id_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜}, meromorphicOr
derAt (fun x_1 => x_1 - x) x = 1
参数：fun x_1 => x_1 - x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_one`：coe_one : ((1 : α) : WithTop α) = 1
· 使用定理 `meromorphicOrderAt_zpow_id_sub_const`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {x : 𝕜} {n : ℤ},   meromorphicOrderAt ((fun x_1 => x_1 - x) ^ 
n) x = ↑n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a

--- 原说明 ---
The order of `· - x` at `x` is `1`.
-/
@[simp] theorem meromorphicOrderAt_id_sub_const :
    meromorphicOrderAt (· - x) x = 1 := by
  rw [← WithTop.coe_one, ← meromorphicOrderAt_zpow_id_sub_const (𝕜 := 𝕜), zpow_one]

/-!
## Order at a Point: Behaviour under Ring Operations

We establish additivity of the order under multiplication and taking powers.
-/

/-- The order of a function `f` equals the order of `-f`. -/
/-
**meromorphicOrderAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_neg {f : 𝕜 -> E} : meromorphicOrderAt f x = meromorphic
OrderAt (-f) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_of_not_meromorphicAt`：meromorphicOrderAt_of_not_merom
orphicAt (hf : ¬ MeromorphicAt f x) : meromorphicOrderAt f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The order of a function `f` equals the order of `-f`.
-/
theorem meromorphicOrderAt_neg {f : 𝕜 → E} :
    meromorphicOrderAt f x = meromorphicOrderAt (-f) x := by
  by_cases h₁ : ¬MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · rw [h₂, eq_comm]
    simp_all [meromorphicOrderAt_eq_top_iff]
  lift meromorphicOrderAt f x to ℤ using h₂ with n hn
  rw [eq_comm, meromorphicOrderAt_eq_int_iff (by fun_prop)] at *
  obtain ⟨g, hg⟩ := hn
  use -g
  simp_all

/-- The order of a function `f` equals the order of `-f`. -/
/-
**meromorphicOrderAt_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_fun_neg {f : 𝕜 -> E} : meromorphicOrderAt f x = meromor
phicOrderAt (fun z => -f z) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicOrderAt_neg`：meromorphicOrderAt_neg {f : 𝕜 -> E} : meromorphi
cOrderAt f x = meromorphicOrderAt (-f) x

--- 原说明 ---
The order of a function `f` equals the order of `-f`.
-/
theorem meromorphicOrderAt_fun_neg {f : 𝕜 → E} :
    meromorphicOrderAt f x = meromorphicOrderAt (fun z ↦ -f z) x := meromorphicOrderAt_neg

/-- The order is additive when multiplying scalar-valued and vector-valued meromorphic functions. -/
/-
**meromorphicOrderAt_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {R : Type u_3} [inst_3 : N
ormedRing R] [NoZeroDivisors R] [inst_5 : _root_.Module R E]   [IsBoundedSMul R 
E] [Module.IsTorsionFree R E] {x : 𝕜} [inst_8 : NormedAlgebra 𝕜 R] [IsScalarTowe
r 𝕜 R E] {f : 𝕜 → R}   {g : 𝕜 → E},   MeromorphicAt f x → MeromorphicAt g x → me
romorphicOrderAt (f • g) x = meromorphicOrderAt f x + meromorphicOrderAt g x
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
The order is additive when multiplying scalar-valued and vector-valued meromorph
ic functions.
-/
@[to_fun] theorem meromorphicOrderAt_smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
    {f : 𝕜 → R} {g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f • g) x = meromorphicOrderAt f x + meromorphicOrderAt g x := by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : meromorphicOrderAt f x with
  | top =>
    simp only [top_add, meromorphicOrderAt_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : meromorphicOrderAt g x with
    | top =>
      simp only [add_top, meromorphicOrderAt_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add, meromorphicOrderAt_eq_int_iff (hf.smul hg)]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (meromorphicOrderAt_eq_int_iff hg).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]

/-- The order is additive when multiplying meromorphic functions. -/
/-
**meromorphicOrderAt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_4} [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {x : 𝕜} {f g : 𝕜
 → 𝕜'},   MeromorphicAt f x → MeromorphicAt g x → meromorphicOrderAt (f * g) x =
 meromorphicOrderAt f x + meromorphicOrderAt g x
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicOrderAt_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {R : Type u_…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The order is additive when multiplying meromorphic functions.
-/
@[to_fun] theorem meromorphicOrderAt_mul {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f * g) x = meromorphicOrderAt f x + meromorphicOrderAt g x :=
  meromorphicOrderAt_smul hf hg

/--
The order is additive in products of meromorphic functions.
-/
/-
**meromorphicOrderAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 
𝕜'} (hf : forall i in s, MeromorphicAt (f i) x) : meromorphicOrderAt (∏ i in s, 
f i) x = ∑ i in s, meromorphicOrderAt (f i) x
参数：hf : forall i in s, MeromorphicAt (f i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `meromorphicOrderAt_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `MeromorphicAt.prod`：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : M
eromorphicAt (∏ i in s, F i) x
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
The order is additive in products of meromorphic functions.
-/
theorem meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (∏ i ∈ s, f i) x = ∑ i ∈ s, meromorphicOrderAt (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, ← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (MeromorphicAt.prod (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))]
    congr
    rw [hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]

/--
The order is additive in products of meromorphic functions.
-/
/-
**meromorphicOrderAt_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜
 -> 𝕜'} (hf : forall i in s, MeromorphicAt (f i) x) : meromorphicOrderAt (fun a 
=> ∏ i in s, f i a) x = ∑ i in s, meromorphicOrderAt (f i) x
参数：hf : forall i in s, MeromorphicAt (f i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `meromorphicOrderAt_prod`：meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s 
: Finset ι} {f : ι -> 𝕜 -> 𝕜'} (hf : forall i in s, MeromorphicAt (f i) x) : mer
omorphicOrder…

--- 原说明 ---
The order is additive in products of meromorphic functions.
-/
theorem meromorphicOrderAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (fun a ↦ ∏ i ∈ s, f i a) x = ∑ i ∈ s, meromorphicOrderAt (f i) x := by
  convert! meromorphicOrderAt_prod hf
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of functions that do not vanish locally does not vanish locally.
-/
/-
**meromorphicOrderAt_finprod_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_finprod_ne_top {x : 𝕜} {ι : Type*} {F : ι -> 𝕜 -> 𝕜} (h
₁ : forall c, MeromorphicAt (F c) x) (h₂ : forall c, meromorphicOrderAt (F c) x 
!= ⊤) : meromorphicOrderAt (∏ᶠ c, F c) x != ⊤
参数：h₁ : forall c, MeromorphicAt (F c) x；h₂ : forall c, meromorphicOrderAt (F c) 
x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `meromorphicOrderAt_prod`：meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s 
: Finset ι} {f : ι -> 𝕜 -> 𝕜'} (hf : forall i in s, MeromorphicAt (f i) x) : mer
omorphicOrder…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `finprod_of_not_hasFiniteMulSupport`：finprod_of_not_hasFiniteMulSupport {
f : α -> M} (hf : ¬ f.HasFiniteMulSupport) : ∏ᶠ i, f i = 1
· 使用定理 `meromorphicOrderAt_const_ofNat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : No
rmedAlgebra 𝕜 𝕜'] (z…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A finprod of functions that do not vanish locally does not vanish locally.
-/
lemma meromorphicOrderAt_finprod_ne_top {x : 𝕜} {ι : Type*} {F : ι → 𝕜 → 𝕜}
    (h₁ : ∀ c, MeromorphicAt (F c) x) (h₂ : ∀ c, meromorphicOrderAt (F c) x ≠ ⊤) :
    meromorphicOrderAt (∏ᶠ c, F c) x ≠ ⊤ := by
  classical
  by_cases hF : F.HasFiniteMulSupport
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ ↦ h₁ x)] using fun x _ ↦ h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
/-
**meromorphicOrderAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_4} [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} {x 
: 𝕜},   MeromorphicAt f x → ∀ {n : ℕ}, meromorphicOrderAt (f ^ n) x = ↑n * merom
orphicOrderAt f x
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `meromorphicOrderAt_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.pow`：pow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Nat) 
: MeromorphicAt (f ^ n) x
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The order multiplies by `n` when taking a meromorphic function to its `n`th powe
r.
-/
@[to_fun] theorem meromorphicOrderAt_pow {f : 𝕜 → 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℕ} :
    meromorphicOrderAt (f ^ n) x = n * meromorphicOrderAt f x := by
  induction n
  case zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  case succ n hn =>
    simp only [pow_add, pow_one, meromorphicOrderAt_mul (hf.pow n) hf, hn, Nat.cast_add,
      Nat.cast_one]
    cases meromorphicOrderAt f x
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
/-
**meromorphicOrderAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_4} [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} {x 
: 𝕜},   MeromorphicAt f x → ∀ {n : ℤ}, meromorphicOrderAt (f ^ n) x = ↑n * merom
orphicOrderAt f x
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用引理 `WithTop.coe_untop₀_of_ne_top`：coe_untop₀_of_ne_top {a : WithTop α} (ha :
 a != ⊤) : a.untop₀ = a
· 使用定理 `WithTop.coe_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] (a b : α), ↑(a * b) = ↑a * ↑b
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The order multiplies by `n` when taking a meromorphic function to its `n`th powe
r.
-/
@[to_fun] theorem meromorphicOrderAt_zpow {f : 𝕜 → 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℤ} :
    meromorphicOrderAt (f ^ n) x = n * meromorphicOrderAt f x := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  -- Trivial case: f locally zero
  by_cases h : meromorphicOrderAt f x = ⊤
  · simp only [h, ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [← WithTop.coe_untop₀_of_ne_top h, ← WithTop.coe_mul,
    meromorphicOrderAt_eq_int_iff (hf.zpow n)]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp_all [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply, hy, Algebra.smul_def, Algebra.smul_def, mul_zpow, ← map_zpow₀]
    congr 1
    rw [mul_comm, zpow_mul]

/-- The order of the inverse is the negative of the order. -/
/-
**meromorphicOrderAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_4} [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {x : 𝕜} {f : 𝕜 →
 𝕜'}, meromorphicOrderAt f⁻¹ x = -meromorphicOrderAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedAddCommGroupWithTop.neg_top`：∀ {α : Type u_3} [self : Linea
rOrderedAddCommGroupWithTop α], -⊤ = ⊤
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The order of the inverse is the negative of the order.
-/
@[to_fun] theorem meromorphicOrderAt_inv {f : 𝕜 → 𝕜'} :
    meromorphicOrderAt (f⁻¹) x = -meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x; swap
  · have : ¬ MeromorphicAt (f⁻¹) x := by
      contrapose hf
      simpa using hf.inv
    simp [hf, this]
  by_cases h₂f : meromorphicOrderAt f x = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_neg]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h₂f]
    simp
  lift meromorphicOrderAt f x to ℤ using h₂f with a ha
  apply (meromorphicOrderAt_eq_int_iff hf.inv).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ha.symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp [h₁a h₂a, Algebra.smul_def, mul_comm]

/--
The order of a quotient is the difference of the orders.
-/
/-
**meromorphicOrderAt_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_4} [inst_
1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜'] {x : 𝕜} {f g : 𝕜
 → 𝕜'},   MeromorphicAt f x → MeromorphicAt g x → meromorphicOrderAt (f / g) x =
 meromorphicOrderAt f x - meromorphicOrderAt g x
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `meromorphicOrderAt_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
· 使用定理 `meromorphicOrderAt_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b

--- 原说明 ---
The order of a quotient is the difference of the orders.
-/
@[to_fun] theorem meromorphicOrderAt_div {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x = meromorphicOrderAt f x - meromorphicOrderAt g x := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, sub_eq_add_neg]

/--
Adding a locally vanishing function does not change the order.
-/
@[simp]
/-
**meromorphicOrderAt_add_of_top_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_add_of_top_left {f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₁ : meromor
phicOrderAt f₁ x = ⊤) : meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x
参数：hf₁ : meromorphicOrderAt f₁ x = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Adding a locally vanishing function does not change the order.
-/
theorem meromorphicOrderAt_add_of_top_left
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

/--
Adding a locally vanishing function does not change the order.
-/
@[simp]
/-
**meromorphicOrderAt_add_of_top_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_add_of_top_right {f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₂ : meromo
rphicOrderAt f₂ x = ⊤) : meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ 
x
参数：hf₂ : meromorphicOrderAt f₂ x = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `meromorphicOrderAt_add_of_top_left`：meromorphicOrderAt_add_of_top_left {
f₁ f₂ : 𝕜 -> E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) : meromorphicOrderAt
 (f₁ + f₂) x = meromorph…

--- 原说明 ---
Adding a locally vanishing function does not change the order.
-/
theorem meromorphicOrderAt_add_of_top_right
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₂ : meromorphicOrderAt f₂ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ x := by
  rw [add_comm, meromorphicOrderAt_add_of_top_left hf₂]

/--
The order of a sum is at least the minimum of the orders of the summands.
-/
/-
**meromorphicOrderAt_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ 
x) : min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) <= meromorphicOrder
At (f₁ + f₂) x
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `min_top_left`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderTop
 α] (a : α), min ⊤ a = a
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.zpow_nonneg`：AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n :
 Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
The order of a sum is at least the minimum of the orders of the summands.
-/
theorem meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) ≤ meromorphicOrderAt (f₁ + f₂) x := by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₂f₁, min_top_left, meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to ℤ using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x to ℤ using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z ↦ (z - x) ^ (n₁ - n)) • g₁ + (fun z ↦ (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[≠] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr this, meromorphicOrderAt_smul t₀ h₁g.meromorphicAt, t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
/-
**meromorphicOrderAt_add_eq_left_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_add_eq_left_of_lt (hf₂ : MeromorphicAt f₂ x) (h : merom
orphicOrderAt f₁ x < meromorphicOrderAt f₂ x) : meromorphicOrderAt (f₁ + f₂) x =
 meromorphicOrderAt f₁ x
参数：hf₂ : MeromorphicAt f₂ x；h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用引理 `MeromorphicAt.add`：add {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f + g) x
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.zpow_nonneg`：AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n :
 Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_left_of_lt (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ x := by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ (MeromorphicAt (f₁ + f₂) x) := by
      contrapose hf₁
      simpa using hf₁.sub hf₂
    simp [this, hf₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to ℤ using h₁f₂ with n₂ hn₂
  lift meromorphicOrderAt f₁ x to ℤ using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [meromorphicOrderAt_eq_int_iff (hf₁.add hf₂)]
  refine ⟨g₁ + (· - x) ^ (n₂ - n₁) • g₂, ?_, ?_, ?_⟩
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop)
      (sub_nonneg.2 (le_of_lt (WithTop.coe_lt_coe.1 h)))
  · simpa [zero_zpow _ <| sub_ne_zero.mpr (WithTop.coe_lt_coe.1 h).ne']
  · filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
/-
**meromorphicOrderAt_add_eq_right_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_add_eq_right_of_lt (hf₁ : MeromorphicAt f₁ x) (h : mero
morphicOrderAt f₂ x < meromorphicOrderAt f₁ x) : meromorphicOrderAt (f₁ + f₂) x 
= meromorphicOrderAt f₂ x
参数：hf₁ : MeromorphicAt f₁ x；h : meromorphicOrderAt f₂ x < meromorphicOrderAt f₁ 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `meromorphicOrderAt_add_eq_left_of_lt`：meromorphicOrderAt_add_eq_left_of_
lt (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt 
f₂ x) : meromorphicOrderAt…

--- 原说明 ---
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_right_of_lt (hf₁ : MeromorphicAt f₁ x)
    (h : meromorphicOrderAt f₂ x < meromorphicOrderAt f₁ x) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [add_comm]
  exact meromorphicOrderAt_add_eq_left_of_lt hf₁ h

/--
If two meromorphic functions have unequal orders, then the order of their sum is
exactly the minimum of the orders of the summands.
-/
/-
**meromorphicOrderAt_add_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_add_of_ne (hf₁ : MeromorphicAt f₁ x) (hf₂ : Meromorphic
At f₂ x) (h : meromorphicOrderAt f₁ x != meromorphicOrderAt f₂ x) : meromorphicO
rderAt (f₁ + f₂) x = min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x)
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x；h : meromorphicOrderAt f₁ x
 != meromorphicOrderAt f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `meromorphicOrderAt_add_eq_left_of_lt`：meromorphicOrderAt_add_eq_left_of_
lt (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt 
f₂ x) : meromorphicOrderAt…
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用引理 `meromorphicOrderAt_add_eq_right_of_lt`：meromorphicOrderAt_add_eq_right_o
f_lt (hf₁ : MeromorphicAt f₁ x) (h : meromorphicOrderAt f₂ x < meromorphicOrderA
t f₁ x) : meromorphicOrderA…

--- 原说明 ---
If two meromorphic functions have unequal orders, then the order of their sum is
exactly the minimum of the orders of the summands.
-/
theorem meromorphicOrderAt_add_of_ne
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x ≠ meromorphicOrderAt f₂ x) :
    meromorphicOrderAt (f₁ + f₂) x = min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) := by
  rcases lt_or_lt_iff_ne.mpr h with h | h
  · simpa [h.le] using meromorphicOrderAt_add_eq_left_of_lt hf₂ h
  · simpa [h.le] using meromorphicOrderAt_add_eq_right_of_lt hf₁ h

/-!
## Level Sets of the Order Function
-/

namespace MeromorphicOn

variable {U : Set 𝕜}

/-- The set where a meromorphic function has infinite order is clopen in its domain of meromorphy.
-/
/-
**MeromorphicOn.isClopen_setOfPred_meromorphicOrderAt_eq_top** 是 Mathlib 中的一个定理，
位于命名空间 `MeromorphicOn`。
形式化陈述：isClopen_setOfPred_meromorphicOrderAt_eq_top (hf : MeromorphicOn f U) : Is
Clopen { u : U | meromorphicOrderAt f u = ⊤ }
参数：hf : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`：MeromorphicAt.ev
entually_eq_zero_or_eventually_ne_zero {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt
 f z₀) : (forallᶠ z in 𝓝[!=] z₀, f z = 0) ∨ …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.not_eventually`：not_eventually {p : α -> Prop} {f : Filter α} : (
¬forallᶠ x in f, p x) ↔ existsᶠ x in f, ¬p x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.sdiff`：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s
 \ t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The set where a meromorphic function has infinite order is clopen in its domain 
of meromorphy.
-/
theorem isClopen_setOfPred_meromorphicOrderAt_eq_top (hf : MeromorphicOn f U) :
    IsClopen { u : U | meromorphicOrderAt f u = ⊤ } := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← meromorphicOrderAt_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ ∈ _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [meromorphicOrderAt_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y ↦ h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [meromorphicOrderAt_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    simp only [mem_ofPred_eq] at hz
    rw [meromorphicOrderAt_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [mem_compl_iff, mem_singleton_iff, isOpen_induced h₂t', mem_preimage,
      h₃t', and_self, and_true]
    intro w hw
    simp only [mem_ofPred_eq]
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y h₁y _ ↦ h₁t' y (mem_of_mem_sdiff h₁y) (mem_of_mem_inter_right h₁y)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (mem_sdiff w).1
      exact ⟨hw, mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_meromorphicOrderAt_eq_top := isClopen_setOfPred_meromorphicOrderAt_eq_top

/--
On a connected set, there exists a point where a meromorphic function `f` has finite order iff `f`
has finite order at every point.

See `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall` in file
`Mathlib/Analysis/Meromorphic/RCLike` for a related result assuming that `f` is meromorphic on all
of `𝕜`.
-/
/-
**MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall** 是 Mathlib 中的一个定理，位
于命名空间 `MeromorphicOn`。
形式化陈述：exists_meromorphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU :
 IsConnected U) : (exists u : U, meromorphicOrderAt f u != ⊤) ↔ (forall u : U, m
eromorphicOrderAt f u != ⊤)
参数：hf : MeromorphicOn f U；hU : IsConnected U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPreconnected_iff_preconnectedSpace`：isPreconnected_iff_preconnectedSpa
ce {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `isClopen_iff`：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen 
s ↔ s = ∅ ∨ s = univ
· 使用定理 `MeromorphicOn.isClopen_setOfPred_meromorphicOrderAt_eq_top`：isClopen_set
OfPred_meromorphicOrderAt_eq_top (hf : MeromorphicOn f U) : IsClopen { u : U | m
eromorphicOrderAt f u = ⊤ }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty

--- 原说明 ---
On a connected set, there exists a point where a meromorphic function `f` has fi
nite order iff `f`
has finite order at every point.

See `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall` in file
`Mathlib/Analysis/Meromorphic/RCLike` for a related result assuming that `f` is 
meromorphic on all
of `𝕜`.
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU : IsConnected U) :
    (∃ u : U, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u : U, meromorphicOrderAt f u ≠ ⊤) := by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOfPred_meromorphicOrderAt_eq_top with h | h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have : u ∈ univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    use ⟨v, hv⟩, h₂f ⟨v, hv⟩

/--
Variant of `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`, with membership in lieu of
subtypes.
-/
/-
**MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem** 是 Mathlib 中的一个
定理，位于命名空间 `MeromorphicOn`。
形式化陈述：exists_meromorphicOrderAt_ne_top_iff_forall_mem (hf : MeromorphicOn f U) (
hU : IsConnected U) : (exists u in U, meromorphicOrderAt f u != ⊤) ↔ (forall u i
n U, meromorphicOrderAt f u != ⊤)
参数：hf : MeromorphicOn f U；hU : IsConnected U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`：exists_meromo
rphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU : IsConnected U) : (
exists u : U, meromorphicOrderAt f u != ⊤) ↔ (f…

--- 原说明 ---
Variant of `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`, with mem
bership in lieu of
subtypes.
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall_mem (hf : MeromorphicOn f U)
    (hU : IsConnected U) :
    (∃ u ∈ U, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) := by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
/-
**MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected** 是 Mathlib 中的一个定理，位
于命名空间 `MeromorphicOn`。
形式化陈述：meromorphicOrderAt_ne_top_of_isPreconnected (hf : MeromorphicOn f U) {y : 
𝕜} (hU : IsPreconnected U) (h₁x : x in U) (hy : y in U) (h₂x : meromorphicOrderA
t f x != ⊤) : meromorphicOrderAt f y != ⊤
参数：hf : MeromorphicOn f U；hU : IsPreconnected U；h₁x : x in U；hy : y in U；h₂x : m
eromorphicOrderAt f x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`：exists_meromo
rphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU : IsConnected U) : (
exists u : U, meromorphicOrderAt f u != ⊤) ↔ (f…
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty

--- 原说明 ---
On a preconnected set, a meromorphic function has finite order at one point if i
t has finite
order at another point.
-/
theorem meromorphicOrderAt_ne_top_of_isPreconnected (hf : MeromorphicOn f U) {y : 𝕜}
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U) (h₂x : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt f y ≠ ⊤ :=
  (hf.exists_meromorphicOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1
    (by use ⟨x, h₁x⟩) ⟨y, hy⟩

/-- If a function is meromorphic on a set `U`, then for each point in `U`, it is analytic at nearby
points in `U`. When the target space is complete, this can be strengthened to analyticity at all
nearby points, see `MeromorphicAt.eventually_analyticAt`. -/
/-
**MeromorphicOn.eventually_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：eventually_analyticAt (h : MeromorphicOn f U) (hx : x in U) : forallᶠ y in
 𝓝[U \ {x}] x, AnalyticAt 𝕜 f y
参数：h : MeromorphicOn f U；hx : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `MeromorphicAt.eventually_continuousAt`：eventually_continuousAt {f : 𝕜 ->
 E} (h : MeromorphicAt f x) : forallᶠ y in 𝓝[!=] x, ContinuousAt f y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeromorphicAt.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {f : 𝕜 → E} …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If a function is meromorphic on a set `U`, then for each point in `U`, it is ana
lytic at nearby
points in `U`. When the target space is complete, this can be strengthened to an
alyticity at all
nearby points, see `MeromorphicAt.eventually_analyticAt`.
-/
theorem eventually_analyticAt (h : MeromorphicOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[U \ {x}] x, AnalyticAt 𝕜 f y := by
  /- At neighboring points in `U`, the function `f` is both meromorphic (by meromorphicity on `U`)
  and continuous (thanks to the formula for a meromorphic function around the point `x`), so it is
  analytic. -/
  have : ∀ᶠ y in 𝓝[U \ {x}] x, ContinuousAt f y := by
    have : U \ {x} ⊆ {x}ᶜ := by simp
    exact nhdsWithin_mono _ this (h x hx).eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  exact (h y h'y.1).analyticAt hy
/-
**MeromorphicOn.eventually_analyticAt_or_mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `Me
romorphicOn`。
形式化陈述：eventually_analyticAt_or_mem_compl (h : MeromorphicOn f U) (hx : x in U) :
 forallᶠ y in 𝓝[!=] x, AnalyticAt 𝕜 f y ∨ y in Uᶜ
参数：h : MeromorphicOn f U；hx : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.eventually_analyticAt`：eventually_analyticAt (h : Meromorp
hicOn f U) (hx : x in U) : forallᶠ y in 𝓝[U \ {x}] x, AnalyticAt 𝕜 f y
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem eventually_analyticAt_or_mem_compl (h : MeromorphicOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y ∨ y ∈ Uᶜ := by
  have : {x}ᶜ = (U \ {x}) ∪ Uᶜ := by aesop (add simp Classical.em)
  rw [this, nhdsWithin_union]
  simp only [mem_compl_iff, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.eventually_analyticAt hx] with y hy using Or.inl hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using Or.inr hy

/-- Meromorphic functions on `U` are analytic on `U`, outside of a discrete subset. -/
/-
**MeromorphicOn.analyticAt_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `Merom
orphicOn`。
形式化陈述：analyticAt_mem_codiscreteWithin (hf : MeromorphicOn f U) : { x | AnalyticA
t 𝕜 f x } in Filter.codiscreteWithin U
参数：hf : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_codiscreteWithin`：mem_codiscreteWithin {S T : Set X} : S in codiscre
teWithin T ↔ forall x in T, Disjoint (𝓝[!=] x) (𝓟 (T \ S))
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_mem_set`：eventually_mem_set {s : Set α} {l : Filter α}
 : (forallᶠ x in l, x in s) ↔ s in l
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.eventually_analyticAt_or_mem_compl`：eventually_analyticAt_
or_mem_compl (h : MeromorphicOn f U) (hx : x in U) : forallᶠ y in 𝓝[!=] x, Analy
ticAt 𝕜 f y ∨ y in Uᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Meromorphic functions on `U` are analytic on `U`, outside of a discrete subset.
-/
theorem analyticAt_mem_codiscreteWithin (hf : MeromorphicOn f U) :
    { x | AnalyticAt 𝕜 f x } ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right, ← Filter.eventually_mem_set]
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with y hy
  simp
  tauto

/-- The set where a meromorphic function has zero or infinite
order is codiscrete within its domain of meromorphicity. -/
/-
**MeromorphicOn.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top** 是 Mathl
ib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top (hf : MeromorphicOn
 f U) : {u : U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} in Fil
ter.codiscrete U
参数：hf : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_codiscrete_subtype_iff_mem_codiscreteWithin`：mem_codiscrete_subtype_
iff_mem_codiscreteWithin {S : Set X} {U : Set S} : U in codiscrete S ↔ (↑) '' U 
in codiscreteWithin S
· 使用引理 `mem_codiscreteWithin`：mem_codiscreteWithin {S T : Set X} : S in codiscre
teWithin T ↔ forall x in T, Disjoint (𝓝[!=] x) (𝓟 (T \ S))
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`：MeromorphicAt.ev
entually_eq_zero_or_eventually_ne_zero {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt
 f z₀) : (forallᶠ z in 𝓝[!=] z₀, f z = 0) ∨ …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.sdiff`：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s
 \ t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.mem_sdiff_of_mem`：mem_sdiff_of_mem {s t : Set α} {x : α} (h1 : x in 
s) (h2 : x ∉ t) : x in s \ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The set where a meromorphic function has zero or infinite
order is codiscrete within its domain of meromorphicity.
-/
theorem codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top (hf : MeromorphicOn f U) :
    {u : U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f] with a h₁a
    suffices ∀ᶠ (z : 𝕜) in 𝓝[≠] a, f z = 0 by
      simp +contextual [meromorphicOrderAt_eq_top_iff, this]
    obtain rfl | hax := eq_or_ne a x
    · exact h₁a
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h₁a ⊢
    obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
    use t \ {x}, fun y h₁y _ ↦ h₁t y h₁y.1 h₁y.2
    exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_sdiff_of_mem h₃t hax⟩
  · filter_upwards [hf.eventually_analyticAt_or_mem_compl hx, h₁f] with a h₁a h'₁a
    simp only [mem_compl_iff, Set.mem_sdiff, mem_image, mem_ofPred_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    rcases h₁a with h' | h'
    · simp +contextual [h'.meromorphicOrderAt_eq, h'.analyticOrderAt_eq_zero.2, h'₁a]
    · exact fun ha ↦ (h' ha).elim

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top

/--
Variant of `codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top`: The set where a meromorphic
function has zero or infinite order is codiscrete within its domain of meromorphicity.
-/
/-
**MeromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top** 是
 Mathlib 中的一个定理，位于命名空间 `MeromorphicOn`。
形式化陈述：codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top (h₁f : Meromo
rphicOn f U) (h₂f : forall u in U, meromorphicOrderAt f u != ⊤) : {u in U | mero
morphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} in codiscreteWithin U
参数：h₁f : MeromorphicOn f U；h₂f : forall u in U, meromorphicOrderAt f u != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sep_or`：sep_or : { x in s | p x ∨ q x } = { x in s | p x } union { x
 in s | q x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_codiscrete_subtype_iff_mem_codiscreteWithin`：mem_codiscrete_subtype_
iff_mem_codiscreteWithin {S : Set X} {U : Set S} : U in codiscrete S ↔ (↑) '' U 
in codiscreteWithin S
· 使用定理 `MeromorphicOn.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top`：co
discrete_setOfPred_meromorphicOrderAt_eq_zero_or_top (hf : MeromorphicOn f U) : 
{u : U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f…

--- 原说明 ---
Variant of `codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top`: The set whe
re a meromorphic
function has zero or infinite order is codiscrete within its domain of meromorph
icity.
-/
theorem codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) :
    {u ∈ U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} ∈ codiscreteWithin U := by
  convert!
    mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      h₁f.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top
  aesop

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top

end MeromorphicOn

section comp
/-!
## Order at a Point: Behaviour under Composition
-/
variable {x : 𝕜} {f : 𝕜 → E} {g : 𝕜 → 𝕜}

/-- If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g` is not locally constant near
`x`, the order of `f ∘ g` is the product of the orders of `f` and `g · - g x`. -/
/-
**MeromorphicAt.meromorphicOrderAt_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicOrderAt_comp (hf : MeromorphicAt f (g x)) (hg : A
nalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) : meromorphicOrderAt (f ∘ g)
 x = (meromorphicOrderAt f (g x)) * (analyticOrderAt (g · - g x) x).map Nat.cast
参数：hf : MeromorphicAt f (g x)；hg : AnalyticAt 𝕜 g x；hg_nc : ¬EventuallyConst g (
𝓝 x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `AnalyticAt.map_nhdsNE`：AnalyticAt.map_nhdsNE {x : 𝕜} {f : 𝕜 -> E} (hfx :
 AnalyticAt 𝕜 f x) (h₂f : ¬EventuallyConst f (𝓝 x)) : (𝓝[!=] x).map f <= (𝓝[!=] 
f x)
· 使用引理 `WithTop.coe_untop₀_of_ne_top`：coe_untop₀_of_ne_top {a : WithTop α} (ha :
 a != ⊤) : a.untop₀ = a
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `Filter.EventuallyEq.comp_tendsto`：Filter.EventuallyEq.comp_tendsto {l : 
Filter α} {f : α -> β} {f' : α -> β} (H : f =ᶠ[l] f') {g : γ -> α} {lc : Filter 
γ} (hg : Tendsto g lc …
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `analyticOrderAt_eq_zero`：analyticOrderAt_eq_zero : analyticOrderAt f z₀ 
= 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ != 0
· 使用定理 `ENat.map_zero`：∀ {α : Type u_1} (f : ℕ → α), ENat.map f 0 = ↑(f 0)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `WithTop.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g` is not locally c
onstant near
`x`, the order of `f ∘ g` is the product of the orders of `f` and `g · - g x`.
-/
lemma MeromorphicAt.meromorphicOrderAt_comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicOrderAt (f ∘ g) x =
      (meromorphicOrderAt f (g x)) * (analyticOrderAt (g · - g x) x).map Nat.cast := by
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x)) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def, ← eventually_map (P := (f · = 0))]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [(show AnalyticAt 𝕜 (g · - g x) x by fun_prop).analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x)).untop₀
  rw [hr]
  -- Now write `f = (· - g x) ^ r • F` for `F` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have aux1 : f ∘ g =ᶠ[𝓝[≠] x] (g · - g x) ^ r • (F ∘ g) := hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop),
      analyticOrderAt_eq_zero.mpr (by exact .inr hFne), ENat.map_zero, CharP.cast_eq_zero,
      WithTop.coe_zero]
  rw [meromorphicOrderAt_congr aux1, meromorphicOrderAt_smul ?_ (AnalyticAt.meromorphicAt ?_),
    aux2, add_zero, meromorphicOrderAt_zpow, AnalyticAt.meromorphicOrderAt_eq] <;>
  fun_prop

/-- If `g` is analytic at `x`, and `g' x ≠ 0`, then the meromorphic order of
`f ∘ g` at `x` is the meromorphic order of `f` at `g x` (even if `f` is not meromorphic). -/
/-
**meromorphicOrderAt_comp_of_deriv_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : de
riv g x != 0) [CompleteSpace 𝕜] [CharZero 𝕜] : meromorphicOrderAt (f ∘ g) x = me
romorphicOrderAt f (g x)
参数：hg : AnalyticAt 𝕜 g x；hg' : deriv g x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`：AnalyticAt.analy
ticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : de
riv f x != 0) : analyticOrderAt (f · - f x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicAt.meromorphicOrderAt_comp`：MeromorphicAt.meromorphicOrderAt_
comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyCo
nst g (𝓝 x)) : meromorphicO…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `meromorphicOrderAt_of_not_meromorphicAt`：meromorphicOrderAt_of_not_merom
orphicAt (hf : ¬ MeromorphicAt f x) : meromorphicOrderAt f x = 0
· 使用引理 `meromorphicAt_comp_iff_of_deriv_ne_zero`：meromorphicAt_comp_iff_of_deriv
_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> E} {g : 𝕜 -> 𝕜} (hg : Analytic
At 𝕜 g x) (hg' : deriv g x !=…

--- 原说明 ---
If `g` is analytic at `x`, and `g' x ≠ 0`, then the meromorphic order of
`f ∘ g` at `x` is the meromorphic order of `f` at `g x` (even if `f` is not mero
morphic).
-/
lemma meromorphicOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0)
    [CompleteSpace 𝕜] [CharZero 𝕜] :
    meromorphicOrderAt (f ∘ g) x = meromorphicOrderAt f (g x) := by
  by_cases hf : MeromorphicAt f (g x)
  · have hgo : analyticOrderAt _ x = 1 := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
    rw [hf.meromorphicOrderAt_comp hg, hgo] <;>
    simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_comp_iff_of_deriv_ne_zero hg hg']

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
/-
**meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 -> 
E} : meromorphicOrderAt (f ∘ (· + c)) x = meromorphicOrderAt f (x + c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_of_not_meromorphicAt`：meromorphicOrderAt_of_not_merom
orphicAt (hf : ¬ MeromorphicAt f x) : meromorphicOrderAt f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `meromorphicAt_comp_add_const_iff_meromorphicAt`：meromorphicAt_comp_add_c
onst_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} : MeromorphicAt (f ∘ (· + c)) x ↔ Me
romorphicAt f (x + c)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.meromorphicOrderAt_comp`：MeromorphicAt.meromorphicOrderAt_
comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyCo
nst g (𝓝 x)) : meromorphicO…
· 使用定理 `AnalyticAt.fun_add`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `analyticOrderAt_id_sub_const_self`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {c : 𝕜}, analyticOrderAt (fun x => x - c) c = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
`meromorphicOrderAt` is invariant under translation.
-/
theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ (· + c)) x = meromorphicOrderAt f (x + c) := by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
/-
**meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 -> 
E} : meromorphicOrderAt (f ∘ (· - c)) x = meromorphicOrderAt f (x - c)
该定理/引理给出了一组等式。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`meromorphicOrderAt` is invariant under translation.
-/
theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ (· - c)) x = meromorphicOrderAt f (x - c) := by
  simp_rw [sub_eq_add_neg, ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

end comp

section smul

variable {g : 𝕜 → 𝕜}

/-
**meromorphicOrderAt_smul_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_smul_of_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0
) : meromorphicOrderAt (g • f) x = meromorphicOrderAt f x
参数：hg : AnalyticAt 𝕜 g x；hg' : g x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicOrderAt_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {R : Type u_…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `meromorphicOrderAt_of_not_meromorphicAt`：meromorphicOrderAt_of_not_merom
orphicAt (hf : ¬ MeromorphicAt f x) : meromorphicOrderAt f x = 0
· 使用引理 `meromorphicAt_smul_iff_of_ne_zero`：meromorphicAt_smul_iff_of_ne_zero {f 
: 𝕜 -> E} (hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) : MeromorphicAt (g • f) x ↔ M
eromorphicAt f x
-/
lemma meromorphicOrderAt_smul_of_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    meromorphicOrderAt (g • f) x = meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x
  · simp [meromorphicOrderAt_smul hg.meromorphicAt hf, hg.meromorphicOrderAt_eq,
      hg.analyticOrderAt_eq_zero.mpr hg']
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_smul_iff_of_ne_zero hg hg']
/-
**meromorphicOrderAt_mul_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_mul_of_ne_zero {f : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg
' : g x != 0) : meromorphicOrderAt (g * f) x = meromorphicOrderAt f x
参数：hg : AnalyticAt 𝕜 g x；hg' : g x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `meromorphicOrderAt_smul_of_ne_zero`：meromorphicOrderAt_smul_of_ne_zero (
hg : AnalyticAt 𝕜 g x) (hg' : g x != 0) : meromorphicOrderAt (g • f) x = meromor
phicOrderAt f x
-/
lemma meromorphicOrderAt_mul_of_ne_zero {f : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    meromorphicOrderAt (g * f) x = meromorphicOrderAt f x :=
  meromorphicOrderAt_smul_of_ne_zero hg hg'

end smul

/-!
## Order at a Point of the Derivative
-/

section deriv

/-- The meromorphic order of the derivative is one less than the order of the original function.
This however is not true if the characteristic of the domain field divides the original order,
where the order of the derivative can rise to a larger integer. -/
/-
**meromorphicOrderAt_deriv_eq_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_deriv_eq_sub_one [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜}
 {n : Int} (hn : (n : 𝕜) != 0) (hf : meromorphicOrderAt f x = ↑n) : meromorphicO
rderAt (deriv f) x = ↑(n - 1)
参数：hn : (n : 𝕜) != 0；hf : meromorphicOrderAt f x = ↑n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `meromorphicAt_of_meromorphicOrderAt_ne_zero`：meromorphicAt_of_meromorphi
cOrderAt_ne_zero (hf : meromorphicOrderAt f x != 0) : MeromorphicAt f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `MeromorphicAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [Co
mpleteSpa…
· 使用定理 `AnalyticAt.fun_add`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `AnalyticAt.fun_const_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 …
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.EventuallyEq.nhdsNE_deriv`：Filter.EventuallyEq.nhdsNE_deriv (h : 
f₁ =ᶠ[𝓝[!=] x] f) : deriv f₁ =ᶠ[𝓝[!=] x] deriv f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
The meromorphic order of the derivative is one less than the order of the origin
al function.
This however is not true if the characteristic of the domain field divides the o
riginal order,
where the order of the derivative can rise to a larger integer.
-/
lemma meromorphicOrderAt_deriv_eq_sub_one [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℤ}
    (hn : (n : 𝕜) ≠ 0) (hf : meromorphicOrderAt f x = ↑n) :
    meromorphicOrderAt (deriv f) x = ↑(n - 1) := by
  have hmero : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero (by aesop)
  rw [meromorphicOrderAt_eq_int_iff hmero] at hf
  rw [meromorphicOrderAt_eq_int_iff hmero.deriv]
  obtain ⟨g, hga, hg0, (hg : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z)⟩ := hf
  refine ⟨fun z ↦ (n : 𝕜) • g z + (z - x) • deriv g z, by fun_prop, by simpa using ⟨hn, hg0⟩, ?_⟩
  filter_upwards [hga.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds),
    eventually_mem_nhdsWithin, hg.nhdsNE_deriv] with z hgz hmem hz
  have hzx : z - x ≠ 0 := by simpa [sub_eq_zero] using hmem
  calc
    deriv f z = deriv (fun z ↦ (z - x) ^ n • g z) z :=
      hz
    _ = (z - x) ^ n • deriv g z + deriv ((· ^ n) ∘ (· - x)) z • g z :=
      deriv_fun_smul (by fun_prop (disch := grind)) hgz.differentiableAt
    _ = (z - x) ^ n • deriv g z + (n * (z - x) ^ (n - 1)) • g z := by
      rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
      simp [deriv_zpow]
    _ = (z - x) ^ (n - 1) • ((n : 𝕜) • g z + (z - x) • deriv g z) := by
      simp [smul_smul, ← zpow_add_one₀ hzx, add_comm, mul_comm]

/-- Equivalent to `meromorphicOrderAt_deriv_eq_sub_one` with a slightly different statement so the
conclusion matches more targets -/
/-
**meromorphicOrderAt_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_deriv [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int} 
(hn : (↑(n + 1) : 𝕜) != 0) (hf : meromorphicOrderAt f x = ↑(n + 1)) : meromorphi
cOrderAt (deriv f) x = ↑n
参数：hn : (↑(n + 1) : 𝕜) != 0；hf : meromorphicOrderAt f x = ↑(n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用引理 `meromorphicOrderAt_deriv_eq_sub_one`：meromorphicOrderAt_deriv_eq_sub_one
 [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int} (hn : (n : 𝕜) != 0) (hf : mero
morphicOrderAt f x = ↑n) …

--- 原说明 ---
Equivalent to `meromorphicOrderAt_deriv_eq_sub_one` with a slightly different st
atement so the
conclusion matches more targets
-/
lemma meromorphicOrderAt_deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℤ}
    (hn : (↑(n + 1) : 𝕜) ≠ 0) (hf : meromorphicOrderAt f x = ↑(n + 1)) :
    meromorphicOrderAt (deriv f) x = ↑n := by
  simpa using meromorphicOrderAt_deriv_eq_sub_one hn hf
variable [CompleteSpace 𝕜] {f : 𝕜 → 𝕜}

/--
At zeros and poles of a meromorphic function `f`, the logarithmic derivative has a simple pole: its
meromorphic order equals `-1`.
-/
/-
**meromorphicOrderAt_logDeriv_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f 
x) (h₁ : meromorphicOrderAt f x != 0) (h₂ : meromorphicOrderAt f x != ⊤) : merom
orphicOrderAt (logDeriv f) x = -1
参数：hf : MeromorphicAt f x；h₁ : meromorphicOrderAt f x != 0；h₂ : meromorphicOrder
At f x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `meromorphicOrderAt_div`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `MeromorphicAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [Co
mpleteSpa…
· 使用引理 `meromorphicOrderAt_deriv_eq_sub_one`：meromorphicOrderAt_deriv_eq_sub_one
 [CompleteSpace E] {f : 𝕜 -> E} {x : 𝕜} {n : Int} (hn : (n : 𝕜) != 0) (hf : mero
morphicOrderAt f x = ↑n) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
At zeros and poles of a meromorphic function `f`, the logarithmic derivative has
 a simple pole: its
meromorphic order equals `-1`.
-/
theorem meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f x)
    (h₁ : meromorphicOrderAt f x ≠ 0) (h₂ : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt (logDeriv f) x = -1 := by
  lift meromorphicOrderAt f x to ℤ using h₂ with n hn
  rw [logDeriv, meromorphicOrderAt_div hf.deriv hf,
    meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr (by exact_mod_cast h₁)) hn.symm,
    ← hn]
  norm_cast
  simp

/--
At points where a meromorphic function has order zero, the meromorphic order of the logarithmic
derivative is nonnegative.
-/
/-
**meromorphicOrderAt_logDeriv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x) (h : meromorph
icOrderAt f x = 0) : 0 <= meromorphicOrderAt (logDeriv f) x
参数：hf : MeromorphicAt f x；h : meromorphicOrderAt f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用引理 `logDeriv_congr_nhdsNE`：logDeriv_congr_nhdsNE {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h 
: f =ᶠ[𝓝[!=] x] g) : logDeriv f =ᶠ[𝓝[!=] x] logDeriv g
· 使用定理 `AnalyticAt.meromorphicOrderAt_nonneg`：AnalyticAt.meromorphicOrderAt_nonn
eg (hf : AnalyticAt 𝕜 f x) : 0 <= meromorphicOrderAt f x
· 使用定理 `AnalyticAt.div`：AnalyticAt.div {f g : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜
 f x) (ga : AnalyticAt 𝕜 g x) (g0 : g x != 0) : AnalyticAt 𝕜 (f / g) x
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…

--- 原说明 ---
At points where a meromorphic function has order zero, the meromorphic order of 
the logarithmic
derivative is nonnegative.
-/
theorem meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x = 0) :
    0 ≤ meromorphicOrderAt (logDeriv f) x := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[≠] x] g := by
    filter_upwards [h₃g] with z hz using by simpa using hz
  rw [meromorphicOrderAt_congr (logDeriv_congr_nhdsNE h₄)]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

end deriv

