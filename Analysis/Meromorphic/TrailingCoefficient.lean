/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# The Trailing Coefficient of a Meromorphic Function

This file defines the trailing coefficient of a meromorphic function. If `f` is meromorphic at a
point `x`, the trailing coefficient is defined as the (unique!) value `g x` for a presentation of
`f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.

The lemma `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` expresses the trailing coefficient
as a limit.
-/

@[expose] public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x : 𝕜}

open Filter Topology

variable (f x) in
/--
If `f` is meromorphic of finite order at a point `x`, the trailing coefficient is defined as the
(unique!) value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with `g`
analytic at `x`. In all other cases, the trailing coefficient is defined to be zero.
-/
/-
**meromorphicTrailingCoeffAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt : E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic of finite order at a point `x`, the trailing coefficient i
s defined as the
(unique!) value `g x` for a presentation of `f` in the form `(z - x) ^ order • g
 z` with `g`
analytic at `x`. In all other cases, the trailing coefficient is defined to be z
ero.
-/
noncomputable def meromorphicTrailingCoeffAt : E := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · exact 0
    · exact ((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose x
  · exact 0

/--
If `f` is not meromorphic at `x`, the trailing coefficient is zero by definition.
-/
/-
**meromorphicTrailingCoeffAt_of_not_MeromorphicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}, ¬Mero
morphicAt f x → meromorphicTrailingCoeffAt f x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is not meromorphic at `x`, the trailing coefficient is zero by definition
.
-/
@[simp] lemma meromorphicTrailingCoeffAt_of_not_MeromorphicAt (h : ¬MeromorphicAt f x) :
    meromorphicTrailingCoeffAt f x = 0 := by simp [meromorphicTrailingCoeffAt, h]

/--
If `f` is meromorphic of infinite order at `x`, the trailing coefficient is zero by definition.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top** 是 Mathlib 中的一个定理，位于
命名空间 `MeromorphicAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}, merom
orphicOrderAt f x = ⊤ → meromorphicTrailingCoeffAt f x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a

--- 原说明 ---
If `f` is meromorphic of infinite order at `x`, the trailing coefficient is zero
 by definition.
-/
@[simp] lemma MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    (h : meromorphicOrderAt f x = ⊤) :
    meromorphicTrailingCoeffAt f x = 0 := by simp_all [meromorphicTrailingCoeffAt]

/-!
## Characterization of the Trailing Coefficient
-/

/--
Definition of the trailing coefficient in case where `f` is meromorphic and a presentation of the
form `f = (z - x) ^ order • g z` is given, with `g` analytic at `x`.
-/
/-
**AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x
) (h : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ (meromorphicOrderAt f x).untop₀ • g z) :
 meromorphicTrailingCoeffAt f x = g x
参数：h₁g : AnalyticAt 𝕜 g x；h : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ (meromorphicOrder
At f x).untop₀ • g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicAt.meromorphicAt_congr`：meromorphicAt_congr {f g : 𝕜 -> E} (h
 : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x
· 使用定理 `MeromorphicAt.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{R : Type u_…
· 使用定理 `MeromorphicAt.fun_zpow`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontriv
iallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`：ContinuousAt.eve
ntuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X -> Y} (hf : 
ContinuousAt f x) (hg : ContinuousAt g x) [(…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_top`：untop₀_top : untop₀ ⊤ = (0 : α)
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Definition of the trailing coefficient in case where `f` is meromorphic and a pr
esentation of the
form `f = (z - x) ^ order • g z` is given, with `g` analytic at `x`.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (meromorphicOrderAt f x).untop₀ • g z) :
    meromorphicTrailingCoeffAt f x = g x := by
  have h₁f : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  by_cases h₃ : meromorphicOrderAt f x = ⊤
  · simp only [h₃, WithTop.untop₀_top, zpow_zero, one_smul,
      MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top] at ⊢ h
    apply EventuallyEq.eq_of_nhds (f := 0)
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) (by fun_prop)]
    apply (h.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₃)).symm
  · unfold meromorphicTrailingCoeffAt
    simp only [h₁f, reduceDIte, h₃, ne_eq]
    obtain ⟨h'₁, h'₂, h'₃⟩ := ((meromorphicOrderAt_ne_top_iff h₁f).1 h₃).choose_spec
    apply Filter.EventuallyEq.eq_of_nhds
    rw [← h'₁.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₁g.continuousAt]
    filter_upwards [h, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    rw [← sub_eq_zero]
    rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
    simp_all [zpow_ne_zero, sub_ne_zero]

/--
Variant of `meromorphicTrailingCoeffAt_of_order_eq_finite`: Definition of the trailing coefficient
in case where `f` is meromorphic of finite order and a presentation is given.
-/
/-
**AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h
₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ n 
• g z) : meromorphicTrailingCoeffAt f x = g x
参数：h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0；h : f =ᶠ[𝓝[!=] x] fun z => (z - x) ^ n 
• g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicAt.meromorphicAt_congr`：meromorphicAt_congr {f g : 𝕜 -> E} (h
 : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x
· 使用定理 `MeromorphicAt.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{R : Type u_…
· 使用定理 `MeromorphicAt.fun_zpow`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontriv
iallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE`：AnalyticAt.meromorph
icTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x) (h : f =ᶠ[𝓝[!=] x] fun z
 => (z - x) ^ (meromorphicOrderAt f x).u…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `meromorphicTrailingCoeffAt_of_order_eq_finite`: Definition of the tr
ailing coefficient
in case where `f` is meromorphic of finite order and a presentation is given.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : ℤ} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) :
    meromorphicTrailingCoeffAt f x = g x := by
  have h₄ : MeromorphicAt f x := by
    rw [MeromorphicAt.meromorphicAt_congr h]
    fun_prop
  have : meromorphicOrderAt f x = n := by
    simp only [meromorphicOrderAt_eq_int_iff h₄, ne_eq]
    use g, h₁g, h₂g
    exact h
  simp_all [meromorphicTrailingCoeffAt_of_eq_nhdsNE h₁g]

/--
If `f` is analytic and does not vanish at `x`, then the trailing coefficient of `f` at `x` is `f x`.
-/
@[simp]
/-
**AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (
h₂ : f x != 0) : meromorphicTrailingCoeffAt f x = f x
参数：h₁ : AnalyticAt 𝕜 f x；h₂ : f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `f` is analytic and does not vanish at `x`, then the trailing coefficient of 
`f` at `x` is `f x`.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x ≠ 0) :
    meromorphicTrailingCoeffAt f x = f x := by
  rw [h₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) h₂]
  filter_upwards
  simp

/--
If `f` is meromorphic at `x`, then the trailing coefficient of `f` at `x` is the limit of the
function `(· - x) ^ (-order) • f`.
-/
/-
**MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h : MeromorphicAt f
 x) : Tendsto ((· - x) ^ (-(meromorphicOrderAt f x).untop₀) • f) (𝓝[!=] x) (𝓝 (m
eromorphicTrailingCoeffAt f x))
参数：h : MeromorphicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `WithTop.untop₀_top`：untop₀_top : untop₀ ⊤ = (0 : α)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用引理 `Pi.inv_apply`：inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹
· 使用引理 `Pi.pow_apply`：pow_apply (f : forall i, M i) (a : α) (i : ι) : (f ^ a) i 
= f i ^ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `zpow_add'`：zpow_add' {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 
0) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is meromorphic at `x`, then the trailing coefficient of `f` at `x` is the
 limit of the
function `(· - x) ^ (-order) • f`.
-/
lemma MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h : MeromorphicAt f x) :
    Tendsto ((· - x) ^ (-(meromorphicOrderAt f x).untop₀) • f) (𝓝[≠] x)
      (𝓝 (meromorphicTrailingCoeffAt f x)) := by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all only [WithTop.untop₀_top, neg_zero, zpow_zero, one_smul,
      meromorphicTrailingCoeffAt_of_order_eq_top]
    apply Tendsto.congr' (f₁ := 0)
    · filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with y hy
      simp_all
    · apply Tendsto.congr' (f₁ := 0) (by rfl) continuousWithinAt_const.tendsto
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h).1 h₂
  apply Tendsto.congr' (f₁ := g)
  · filter_upwards [h₃g, self_mem_nhdsWithin] with y h₁y h₂y
    rw [zpow_neg, Pi.smul_apply', Pi.inv_apply, Pi.pow_apply, h₁y, ← smul_assoc, smul_eq_mul,
      ← zpow_neg, ← zpow_add', neg_add_cancel, zpow_zero, one_smul]
    left
    simp_all [sub_ne_zero]
  · rw [h₁g.meromorphicTrailingCoeffAt_of_eq_nhdsNE h₃g]
    apply h₁g.continuousAt.continuousWithinAt

/-!
## Elementary Properties
-/

/--
If `f` is meromorphic of finite order at `x`, then the trailing coefficient is not zero.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x) 
(h₂ : meromorphicOrderAt f x != ⊤) : meromorphicTrailingCoeffAt f x != 0
参数：h₁ : MeromorphicAt f x；h₂ : meromorphicOrderAt f x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…

--- 原说明 ---
If `f` is meromorphic of finite order at `x`, then the trailing coefficient is n
ot zero.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x)
    (h₂ : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicTrailingCoeffAt f x ≠ 0 := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  simpa [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g] using h₂g

/--
The trailing coefficient of a constant function is the constant.
-/
@[simp]
/-
**meromorphicTrailingCoeffAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_const {x : 𝕜} {e : 𝕜} : meromorphicTrailingCoef
fAt (fun _ => e) x = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x

--- 原说明 ---
The trailing coefficient of a constant function is the constant.
-/
theorem meromorphicTrailingCoeffAt_const {x : 𝕜} {e : 𝕜} :
    meromorphicTrailingCoeffAt (fun _ ↦ e) x = e := by
  by_cases he : e = 0
  · rw [he]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
    rw [meromorphicOrderAt_eq_top_iff]
    simp
  · exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero he

/--
The trailing coefficient of `fun z ↦ z - constant` at `z₀` equals one if `z₀ = constant`, or else
`z₀ - constant`.
-/
/-
**meromorphicTrailingCoeffAt_id_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_id_sub_const [DecidableEq 𝕜] {x y : 𝕜} : meromo
rphicTrailingCoeffAt (· - y) x = if x = y then 1 else x - y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The trailing coefficient of `fun z ↦ z - constant` at `z₀` equals one if `z₀ = c
onstant`, or else
`z₀ - constant`.
-/
theorem meromorphicTrailingCoeffAt_id_sub_const [DecidableEq 𝕜] {x y : 𝕜} :
    meromorphicTrailingCoeffAt (· - y) x = if x = y then 1 else x - y := by
  by_cases h : x = y
  · simp_all only [sub_self, ite_true]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by fun_prop)
      (by apply one_ne_zero)
    simp
  · simp_all only [ite_false]
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (by fun_prop)
    simp_all [sub_ne_zero]

/-!
## Congruence Lemma
-/

/--
If two functions agree in a punctured neighborhood, then their trailing coefficients agree.
-/
/-
**meromorphicTrailingCoeffAt_congr_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_congr_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] 
x] f₂) : meromorphicTrailingCoeffAt f₁ x = meromorphicTrailingCoeffAt f₂ x
参数：h : f₁ =ᶠ[𝓝[!=] x] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `MeromorphicAt.meromorphicAt_congr`：meromorphicAt_congr {f g : 𝕜 -> E} (h
 : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If two functions agree in a punctured neighborhood, then their trailing coeffici
ents agree.
-/
lemma meromorphicTrailingCoeffAt_congr_nhdsNE {f₁ f₂ : 𝕜 → E} (h : f₁ =ᶠ[𝓝[≠] x] f₂) :
    meromorphicTrailingCoeffAt f₁ x = meromorphicTrailingCoeffAt f₂ x := by
  by_cases h₁ : ¬MeromorphicAt f₁ x
  · simp [h₁, (MeromorphicAt.meromorphicAt_congr h).not.1 h₁]
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_congr h]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g,
    h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g (h.symm.trans h₃g)]

/-!
## Behavior under Arithmetic Operations
-/

/--
Taking the negative commutes with taking `meromorphicTrailingCoeffAt`.
-/
/-
**meromorphicTrailingCoeffAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_neg {f : 𝕜 -> E} : meromorphicTrailingCoeffAt (
-f) x = -meromorphicTrailingCoeffAt f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE`：AnalyticAt.meromorph
icTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x) (h : f =ᶠ[𝓝[!=] x] fun z
 => (z - x) ^ (meromorphicOrderAt f x).u…
· 使用定理 `AnalyticAt.neg`：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-
f) x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)

--- 原说明 ---
Taking the negative commutes with taking `meromorphicTrailingCoeffAt`.
-/
theorem meromorphicTrailingCoeffAt_neg {f : 𝕜 → E} :
    meromorphicTrailingCoeffAt (-f) x = -meromorphicTrailingCoeffAt f x := by
  by_cases h₁ : ¬ MeromorphicAt f x
  · aesop
  rw [not_not] at h₁
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · simp_all [← meromorphicOrderAt_neg]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g]
  rw [AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (g := -g)]
  · simp
  · fun_prop
  · filter_upwards [h₃g] with a ha
    simp [ha, ← meromorphicOrderAt_neg]

/--
Taking the negative commutes with taking `meromorphicTrailingCoeffAt`.
-/
/-
**meromorphicTrailingCoeffAt_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_fun_neg {f : 𝕜 -> E} : meromorphicTrailingCoeff
At (fun z => -f z) x = -meromorphicTrailingCoeffAt f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicTrailingCoeffAt_neg`：meromorphicTrailingCoeffAt_neg {f : 𝕜 ->
 E} : meromorphicTrailingCoeffAt (-f) x = -meromorphicTrailingCoeffAt f x

--- 原说明 ---
Taking the negative commutes with taking `meromorphicTrailingCoeffAt`.
-/
theorem meromorphicTrailingCoeffAt_fun_neg {f : 𝕜 → E} :
    meromorphicTrailingCoeffAt (fun z ↦ -f z) x = -meromorphicTrailingCoeffAt f x :=
  meromorphicTrailingCoeffAt_neg

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 -> E
} (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f
₂ x) : meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x
参数：hf₂ : MeromorphicAt f₂ x；h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MeromorphicAt.meromorphicAt_add_iff_meromorphicAt₁`：meromorphicAt_add_if
f_meromorphicAt₁ {f g : 𝕜 -> E} (hf : MeromorphicAt f x) : MeromorphicAt (f + g)
 x ↔ MeromorphicAt g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `AnalyticAt.fun_add`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁
 + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTrailingCoeffAt f₁ x := by
  -- Trivial case: f₁ not meromorphic at x
  by_cases! hf₁ : ¬MeromorphicAt f₁ x
  · have : ¬MeromorphicAt (f₁ + f₂) x := by
      rwa [add_comm, hf₂.meromorphicAt_add_iff_meromorphicAt₁]
    simp_all
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to ℤ using h₁f₂ with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  lift meromorphicOrderAt f₁ x to ℤ using (by aesop) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  rw [WithTop.coe_lt_coe] at h
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + (z - x) ^ (n₂ - n₁) • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp only [Pi.add_apply, h₁z, h₂z, Pi.smul_apply, smul_add, ← smul_assoc, smul_eq_mul,
      add_right_inj]
    rw [← zpow_add₀, add_sub_cancel]
    simp_all [sub_ne_zero]
  have τ₁ : AnalyticAt 𝕜 (fun z ↦ g₁ z + (z - x) ^ (n₂ - n₁) • g₂ z) x :=
    h₁g₁.fun_add (AnalyticAt.fun_smul (AnalyticAt.fun_zpow_nonneg (by fun_prop)
      (sub_nonneg_of_le h.le)) h₁g₂)
  have τ₂ : g₁ x + (x - x) ^ (n₂ - n₁) • g₂ x ≠ 0 := by
    simp_all [zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    τ₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE τ₂ τ₀, sub_self, add_eq_left,
    smul_eq_zero, zero_zpow _ (sub_ne_zero.2 (ne_of_lt h).symm)]
  tauto

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt {f₁ f₂ : 𝕜 
-> E} (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrder
At f₂ x) : meromorphicTrailingCoeffAt (fun z => f₁ z + f₂ z) x = meromorphicTrai
lingCoeffAt f₁ x
参数：hf₂ : MeromorphicAt f₂ x；h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt`：MeromorphicA
t.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 -> E} (hf₂ : Meromorph
icAt f₂ x) (h : meromorphicOrderAt f₁ x < meromo…

--- 原说明 ---
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁
 + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z + f₂ z) x = meromorphicTrailingCoeffAt f₁ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt hf₂ h

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ - f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt {f₁ f₂ : 𝕜 -> E
} (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f
₂ x) : meromorphicTrailingCoeffAt (f₁ - f₂) x = meromorphicTrailingCoeffAt f₁ x
参数：hf₂ : MeromorphicAt f₂ x；h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt`：MeromorphicA
t.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 -> E} (hf₂ : Meromorph
icAt f₂ x) (h : meromorphicOrderAt f₁ x < meromo…
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicOrderAt_neg`：meromorphicOrderAt_neg {f : 𝕜 -> E} : meromorphi
cOrderAt f x = meromorphicOrderAt (-f) x

--- 原说明 ---
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁
 - f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ - f₂) x = meromorphicTrailingCoeffAt f₁ x := by
  rw [sub_eq_add_neg]
  apply MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt (by fun_prop)
  rwa [← meromorphicOrderAt_neg]

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ - f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt {f₁ f₂ : 𝕜 
-> E} (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrder
At f₂ x) : meromorphicTrailingCoeffAt (fun z => f₁ z - f₂ z) x = meromorphicTrai
lingCoeffAt f₁ x
参数：hf₂ : MeromorphicAt f₂ x；h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt`：MeromorphicA
t.meromorphicTrailingCoeffAt_sub_eq_left_of_lt {f₁ f₂ : 𝕜 -> E} (hf₂ : Meromorph
icAt f₂ x) (h : meromorphicOrderAt f₁ x < meromo…

--- 原说明 ---
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁
 - f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₂ : MeromorphicAt f₂ x) (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z - f₂ z) x = meromorphicTrailingCoeffAt f₁ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt hf₂ h

/--
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do not cancel, then the
trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 -> E} (hf₁ 
: MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) (h₁ : meromorphicOrderAt f₁ x =
 meromorphicOrderAt f₂ x) (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTra
ilingCoeffAt f₂ x != 0) : meromorphicTrailingCoeffAt (f₁ + f₂) x = meromorphicTr
ailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x；h₁ : meromorphicOrderAt f₁ 
x = meromorphicOrderAt f₂ x；h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTr
ailingCoeffAt f₂ x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
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
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do n
ot cancel, then the
trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients
.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x ≠ 0) :
    meromorphicTrailingCoeffAt (f₁ + f₂) x
      = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x := by
  -- Trivial case: f₁ vanishes locally around x
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [meromorphicTrailingCoeffAt_of_order_eq_top h₁f₁, zero_add]
    apply meromorphicTrailingCoeffAt_congr_nhdsNE
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₁]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to ℤ using (by lia) with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  lift meromorphicOrderAt f₂ x to ℤ using (by lia) with n₂ hn₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [WithTop.coe_eq_coe, h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂] at *
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp_all
  simp [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (by fun_prop)
    (by simp_all) τ₀]

/--
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do not cancel, then the
trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add {f₁ f₂ : 𝕜 -> E} (
hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) (h₁ : meromorphicOrderAt f₁
 x = meromorphicOrderAt f₂ x) (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphi
cTrailingCoeffAt f₂ x != 0) : meromorphicTrailingCoeffAt (fun z => f₁ z + f₂ z) 
x = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x；h₁ : meromorphicOrderAt f₁ 
x = meromorphicOrderAt f₂ x；h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTr
ailingCoeffAt f₂ x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add`：MeromorphicAt.merom
orphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf
₂ : MeromorphicAt f₂ x) (h₁ : meromorphic…

--- 原说明 ---
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do n
ot cancel, then the
trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients
.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x ≠ 0) :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z + f₂ z) x
      = meromorphicTrailingCoeffAt f₁ x + meromorphicTrailingCoeffAt f₂ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add hf₁ hf₂ h₁ h₂

/--
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do not cancel, then the
trailing coefficient of `f₁ - f₂` at `x` is the sum of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub {f₁ f₂ : 𝕜 -> E} (hf₁ 
: MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) (h₁ : meromorphicOrderAt f₁ x =
 meromorphicOrderAt f₂ x) (h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTra
ilingCoeffAt f₂ x != 0) : meromorphicTrailingCoeffAt (f₁ - f₂) x = meromorphicTr
ailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x；h₁ : meromorphicOrderAt f₁ 
x = meromorphicOrderAt f₂ x；h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTr
ailingCoeffAt f₂ x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add`：MeromorphicAt.merom
orphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf
₂ : MeromorphicAt f₂ x) (h₁ : meromorphic…
· 使用引理 `MeromorphicAt.neg`：neg {f : 𝕜 -> E} (hf : MeromorphicAt f x) : Meromorph
icAt (-f) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicOrderAt_neg`：meromorphicOrderAt_neg {f : 𝕜 -> E} : meromorphi
cOrderAt f x = meromorphicOrderAt (-f) x
· 使用定理 `meromorphicTrailingCoeffAt_neg`：meromorphicTrailingCoeffAt_neg {f : 𝕜 ->
 E} : meromorphicTrailingCoeffAt (-f) x = -meromorphicTrailingCoeffAt f x

--- 原说明 ---
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do n
ot cancel, then the
trailing coefficient of `f₁ - f₂` at `x` is the sum of the trailing coefficients
.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x ≠ 0) :
    meromorphicTrailingCoeffAt (f₁ - f₂) x
      = meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x := by
  rw [sub_eq_add_neg, hf₁.meromorphicTrailingCoeffAt_add_eq_add (by fun_prop)]
  · rw [meromorphicTrailingCoeffAt_neg, sub_eq_add_neg]
  · rwa [← meromorphicOrderAt_neg]
  · rwa [meromorphicTrailingCoeffAt_neg, ← sub_eq_add_neg]

/--
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do not cancel, then the
trailing coefficient of `f₁ - f₂` at `x` is the sum of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub {f₁ f₂ : 𝕜 -> E} (
hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) (h₁ : meromorphicOrderAt f₁
 x = meromorphicOrderAt f₂ x) (h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphi
cTrailingCoeffAt f₂ x != 0) : meromorphicTrailingCoeffAt (fun z => f₁ z - f₂ z) 
x = meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x；h₁ : meromorphicOrderAt f₁ 
x = meromorphicOrderAt f₂ x；h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTr
ailingCoeffAt f₂ x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub`：MeromorphicAt.merom
orphicTrailingCoeffAt_sub_eq_sub {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf
₂ : MeromorphicAt f₂ x) (h₁ : meromorphic…

--- 原说明 ---
If `f₁` and `f₂` have equal order at `x` and if their trailing coefficients do n
ot cancel, then the
trailing coefficient of `f₁ - f₂` at `x` is the sum of the trailing coefficients
.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁ : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x)
    (h₂ : meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x ≠ 0) :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z - f₂ z) x
      = meromorphicTrailingCoeffAt f₁ x - meromorphicTrailingCoeffAt f₂ x :=
  MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub hf₁ hf₂ h₁ h₂

/--
The trailing coefficient of a scalar product is the scalar product of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} 
(hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) : meromorphicTrailingCoeff
At (f₁ • f₂) x = (meromorphicTrailingCoeffAt f₁ x) • (meromorphicTrailingCoeffAt
 f₂ x)
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `WithTop.untop₀_add`：untop₀_add [AddZeroClass α] {a b : WithTop α} (ha : 
a != ⊤) (hb : b != ⊤) : (a + b).untop₀ = a.untop₀ + b.untop₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
The trailing coefficient of a scalar product is the scalar product of the traili
ng coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ • f₂) x =
      (meromorphicTrailingCoeffAt f₁ x) • (meromorphicTrailingCoeffAt f₂ x) := by
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp_all [meromorphicOrderAt_smul hf₁ hf₂]
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_ne_top_iff hf₂).1 h₁f₂
  have : f₁ • f₂ =ᶠ[𝓝[≠] x]
      fun z ↦ (z - x) ^ (meromorphicOrderAt (f₁ • f₂) x).untop₀ • (g₁ • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    simp_all [meromorphicOrderAt_smul hf₁ hf₂, zpow_add₀ (sub_ne_zero.2 h₃y)]
    module
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂,
    (h₁g₁.smul h₁g₂).meromorphicTrailingCoeffAt_of_eq_nhdsNE this]
  simp

/--
The trailing coefficient of a scalar product is the scalar product of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 ->
 E} (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) : meromorphicTrailingC
oeffAt (fun z => f₁ z • f₂ z) x = (meromorphicTrailingCoeffAt f₁ x) • (meromorph
icTrailingCoeffAt f₂ x)
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`：MeromorphicAt.meromorphic
TrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf₂
 : MeromorphicAt f₂ x) : meromorphi…

--- 原说明 ---
The trailing coefficient of a scalar product is the scalar product of the traili
ng coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z • f₂ z) x =
      (meromorphicTrailingCoeffAt f₁ x) • (meromorphicTrailingCoeffAt f₂ x) :=
  MeromorphicAt.meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_mul {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : Merom
orphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) : meromorphicTrailingCoeffAt (f₁ * f₂)
 x = (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCoeffAt f₂ x)
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`：MeromorphicAt.meromorphic
TrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf₂
 : MeromorphicAt f₂ x) : meromorphi…

--- 原说明 ---
The trailing coefficient of a product is the product of the trailing coefficient
s.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (f₁ * f₂) x =
      (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCoeffAt f₂ x) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : M
eromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) : meromorphicTrailingCoeffAt (fun 
z => f₁ z * f₂ z) x = (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCo
effAt f₂ x)
参数：hf₁ : MeromorphicAt f₁ x；hf₂ : MeromorphicAt f₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`：MeromorphicAt.meromorphic
TrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf₂
 : MeromorphicAt f₂ x) : meromorphi…

--- 原说明 ---
The trailing coefficient of a product is the product of the trailing coefficient
s.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul {f₁ f₂ : 𝕜 → 𝕜}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z * f₂ z) x =
      (meromorphicTrailingCoeffAt f₁ x) * (meromorphicTrailingCoeffAt f₂ x) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
/-
**meromorphicTrailingCoeffAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 
𝕜} {x : 𝕜} (h : forall σ in s, MeromorphicAt (f σ) x) : meromorphicTrailingCoeff
At (∏ n in s, f n) x = ∏ n in s, meromorphicTrailingCoeffAt (f n) x
参数：h : forall σ in s, MeromorphicAt (f σ) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `meromorphicTrailingCoeffAt_const`：meromorphicTrailingCoeffAt_const {x : 
𝕜} {e : 𝕜} : meromorphicTrailingCoeffAt (fun _ => e) x = e
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_mul`：MeromorphicAt.meromorphicT
railingCoeffAt_mul {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : MeromorphicAt f₁ x) (hf₂ : Meromorphi
cAt f₂ x) : meromorphicTrailingCoe…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `MeromorphicAt.prod`：prod (hf : forall σ in s, MeromorphicAt (F σ) x) : M
eromorphicAt (∏ i in s, F i) x

--- 原说明 ---
The trailing coefficient of a product is the product of the trailing coefficient
s.
-/
theorem meromorphicTrailingCoeffAt_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    {x : 𝕜} (h : ∀ σ ∈ s, MeromorphicAt (f σ) x) :
    meromorphicTrailingCoeffAt (∏ n ∈ s, f n) x = ∏ n ∈ s, meromorphicTrailingCoeffAt (f n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    apply meromorphicTrailingCoeffAt_const
  | insert σ s₁ hσ hind =>
    have : ∀ σ₀ ∈ s₁, MeromorphicAt (f σ₀) x := by
      intro τ hτ
      apply h τ (Finset.mem_insert_of_mem hτ)
    rw [Finset.prod_insert hσ, Finset.prod_insert hσ,
      (h σ (Finset.mem_insert_self σ s₁)).meromorphicTrailingCoeffAt_mul
      (MeromorphicAt.prod this), hind this]

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
/-
**meromorphicTrailingCoeffAt_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_fun_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜
 -> 𝕜} {x : 𝕜} (h : forall σ in s, MeromorphicAt (f σ) x) : meromorphicTrailingC
oeffAt (fun z => ∏ n in s, f n z) x = ∏ n in s, meromorphicTrailingCoeffAt (f n)
 x
参数：h : forall σ in s, MeromorphicAt (f σ) x。
该定理/引理给出了一组等式。
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
· 使用定理 `meromorphicTrailingCoeffAt_prod`：meromorphicTrailingCoeffAt_prod {ι : Ty
pe*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} {x : 𝕜} (h : forall σ in s, MeromorphicAt 
(f σ) x) : meromorphi…

--- 原说明 ---
The trailing coefficient of a product is the product of the trailing coefficient
s.
-/
theorem meromorphicTrailingCoeffAt_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    {x : 𝕜} (h : ∀ σ ∈ s, MeromorphicAt (f σ) x) :
    meromorphicTrailingCoeffAt (fun z ↦ ∏ n ∈ s, f n z) x
      = ∏ n ∈ s, meromorphicTrailingCoeffAt (f n) x := by
  convert! meromorphicTrailingCoeffAt_prod h
  simp

/--
The trailing coefficient of the inverse function is the inverse of the trailing coefficient.
-/
/-
**meromorphicTrailingCoeffAt_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_inv {f : 𝕜 -> 𝕜} : meromorphicTrailingCoeffAt f
⁻¹ x = (meromorphicTrailingCoeffAt f x)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `meromorphicOrderAt_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlge
bra 𝕜 𝕜'] {x…
· 使用定理 `LinearOrderedAddCommGroupWithTop.neg_top`：∀ {α : Type u_3} [self : Linea
rOrderedAddCommGroupWithTop α], -⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff_eventually_ne_zero`：meromorphicOrderAt_ne_
top_iff_eventually_ne_zero {f : 𝕜 -> E} (hf : MeromorphicAt f x) : meromorphicOr
derAt f x != ⊤ ↔ forallᶠ x in 𝓝[!=] x,…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_eq_one_iff_eq_inv₀`：mul_eq_one_iff_eq_inv₀ (hb : b != 0) : a * b = 1
 ↔ a = b⁻¹
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero`：MeromorphicAt.meromorp
hicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x) (h₂ : meromorphicOrderAt f x
 != ⊤) : meromorphicTrailingCoeffAt f …
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_mul`：MeromorphicAt.meromorphicT
railingCoeffAt_mul {f₁ f₂ : 𝕜 -> 𝕜} (hf₁ : MeromorphicAt f₁ x) (hf₂ : Meromorphi
cAt f₂ x) : meromorphicTrailingCoe…
· 使用引理 `MeromorphicAt.inv`：inv {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) : Meromorp
hicAt f⁻¹ x
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The trailing coefficient of the inverse function is the inverse of the trailing 
coefficient.
-/
lemma meromorphicTrailingCoeffAt_inv {f : 𝕜 → 𝕜} :
    meromorphicTrailingCoeffAt f⁻¹ x = (meromorphicTrailingCoeffAt f x)⁻¹ := by
  by_cases h₁ : MeromorphicAt f x
  · by_cases h₂ : meromorphicOrderAt f x = ⊤
    · simp_all [meromorphicOrderAt_inv (f := f) (x := x)]
    have : f⁻¹ * f =ᶠ[𝓝[≠] x] 1 := by
      filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero h₁).1 h₂]
      simp_all
    rw [← mul_eq_one_iff_eq_inv₀ (h₁.meromorphicTrailingCoeffAt_ne_zero h₂),
      ← h₁.inv.meromorphicTrailingCoeffAt_mul h₁, meromorphicTrailingCoeffAt_congr_nhdsNE this,
      analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0)]
    · simp
    · simp only [zpow_zero, smul_eq_mul, mul_one]
      exact eventuallyEq_nhdsWithin_of_eqOn fun _ ↦ congrFun rfl
  · simp_all

/--
The trailing coefficient of the inverse function is the inverse of the trailing coefficient.
-/
/-
**meromorphicTrailingCoeffAt_fun_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_fun_inv {f : 𝕜 -> 𝕜} : meromorphicTrailingCoeff
At (fun z => (f z)⁻¹) x = (meromorphicTrailingCoeffAt f x)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `meromorphicTrailingCoeffAt_inv`：meromorphicTrailingCoeffAt_inv {f : 𝕜 ->
 𝕜} : meromorphicTrailingCoeffAt f⁻¹ x = (meromorphicTrailingCoeffAt f x)⁻¹

--- 原说明 ---
The trailing coefficient of the inverse function is the inverse of the trailing 
coefficient.
-/
lemma meromorphicTrailingCoeffAt_fun_inv {f : 𝕜 → 𝕜} :
    meromorphicTrailingCoeffAt (fun z ↦ (f z)⁻¹) x = (meromorphicTrailingCoeffAt f x)⁻¹ :=
  meromorphicTrailingCoeffAt_inv

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_zpow {n : Int} {f : 𝕜 -> 𝕜} (h₁ :
 MeromorphicAt f x) : meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailin
gCoeffAt f x) ^ n
参数：h₁ : MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `ne_zero_of_eq_one`：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h
 : a = 1) : a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `meromorphicOrderAt_zpow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {𝕜' : Type u_4} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlg
ebra 𝕜 𝕜'] {f…
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用引理 `AnalyticAt.zpow`：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : A
nalyticAt 𝕜 f z) (h₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用引理 `WithTop.untop₀_mul`：untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : W
ithTop α) : (a * b).untop₀ = a.untop₀ * b.untop₀

--- 原说明 ---
The trailing coefficient of the power of a function is the power of the trailing
 coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_zpow {n : ℤ} {f : 𝕜 → 𝕜} (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n := by
  by_cases h₂ : meromorphicOrderAt f x = ⊤
  · by_cases h₃ : n = 0
    · simp only [h₃, zpow_zero]
      apply analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero (ne_zero_of_eq_one rfl)
    · simp_all [meromorphicOrderAt_zpow h₁, zero_zpow n h₃]
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
    rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (n := (meromorphicOrderAt f x).untop₀) h₂g h₃g,
      (h₁g.zpow h₂g (n := n)).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (n := (meromorphicOrderAt (f ^ n) x).untop₀)
        (by simp_all [zpow_ne_zero])]
    · simp only [Pi.pow_apply]
    · filter_upwards [h₃g] with a ha
      simp_all [mul_zpow, ← zpow_mul, meromorphicOrderAt_zpow h₁, mul_comm]

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow {n : Int} {f : 𝕜 -> 𝕜} (
h₁ : MeromorphicAt f x) : meromorphicTrailingCoeffAt (fun z => f z ^ n) x = (mer
omorphicTrailingCoeffAt f x) ^ n
参数：h₁ : MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_zpow`：MeromorphicAt.meromorphic
TrailingCoeffAt_zpow {n : Int} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x) : meromorph
icTrailingCoeffAt (f ^ n) x = (mero…

--- 原说明 ---
The trailing coefficient of the power of a function is the power of the trailing
 coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow {n : ℤ} {f : 𝕜 → 𝕜}
    (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (fun z ↦ f z ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n :=
  MeromorphicAt.meromorphicTrailingCoeffAt_zpow h₁

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_pow {n : Nat} {f : 𝕜 -> 𝕜} (h₁ : 
MeromorphicAt f x) : meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailing
CoeffAt f x) ^ n
参数：h₁ : MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_zpow`：MeromorphicAt.meromorphic
TrailingCoeffAt_zpow {n : Int} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x) : meromorph
icTrailingCoeffAt (f ^ n) x = (mero…

--- 原说明 ---
The trailing coefficient of the power of a function is the power of the trailing
 coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_pow {n : ℕ} {f : 𝕜 → 𝕜}
    (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (f ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n := by
  convert! h₁.meromorphicTrailingCoeffAt_zpow (n := n) <;> simp

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow {n : Nat} {f : 𝕜 -> 𝕜} (h
₁ : MeromorphicAt f x) : meromorphicTrailingCoeffAt (fun z => f z ^ n) x = (mero
morphicTrailingCoeffAt f x) ^ n
参数：h₁ : MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_pow`：MeromorphicAt.meromorphicT
railingCoeffAt_pow {n : Nat} {f : 𝕜 -> 𝕜} (h₁ : MeromorphicAt f x) : meromorphic
TrailingCoeffAt (f ^ n) x = (merom…

--- 原说明 ---
The trailing coefficient of the power of a function is the power of the trailing
 coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow {n : ℕ} {f : 𝕜 → 𝕜}
    (h₁ : MeromorphicAt f x) :
    meromorphicTrailingCoeffAt (fun z ↦ f z ^ n) x = (meromorphicTrailingCoeffAt f x) ^ n :=
  MeromorphicAt.meromorphicTrailingCoeffAt_pow h₁

/-!
## Behavior under Composition
-/

/--
If `g` is analytic at `x` and not locally constant, and `f` is meromorphic at `g x`, express the
trailing coefficient of `f ∘ g` at `x` in terms of `g` and `f`.
-/
/-
**MeromorphicAt.meromorphicTrailingCoeffAt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicTrailingCoeffAt_comp {g : 𝕜 -> 𝕜} (hf : Meromorph
icAt f (g x)) (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) : merom
orphicTrailingCoeffAt (f ∘ g) x = (meromorphicTrailingCoeffAt (g · - g x) x) ^ (
meromorphicOrderAt f (g x)).untop₀ • meromorphicTrailingCoeffAt f (g x)
参数：hf : MeromorphicAt f (g x)；hg : AnalyticAt 𝕜 g x；hg_nc : ¬EventuallyConst g (
𝓝 x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`：∀ {𝕜 : Type u_
1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGrou
p E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `AnalyticAt.map_nhdsNE`：AnalyticAt.map_nhdsNE {x : 𝕜} {f : 𝕜 -> E} (hfx :
 AnalyticAt 𝕜 f x) (h₂f : ¬EventuallyConst f (𝓝 x)) : (𝓝[!=] x).map f <= (𝓝[!=] 
f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `WithTop.untop₀_top`：untop₀_top : untop₀ ⊤ = (0 : α)
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicOrderAt_ne_top_iff`：meromorphicOrderAt_ne_top_iff {f : 𝕜 -> E
} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) : meromorphicOrderAt f z₀ != ⊤ ↔ exists (g 
: 𝕜 -> E), Analytic…
· 使用引理 `meromorphicTrailingCoeffAt_congr_nhdsNE`：meromorphicTrailingCoeffAt_cong
r_nhdsNE {f₁ f₂ : 𝕜 -> E} (h : f₁ =ᶠ[𝓝[!=] x] f₂) : meromorphicTrailingCoeffAt f
₁ x = meromorphicTrailingCoef…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用引理 `MeromorphicAt.meromorphicTrailingCoeffAt_smul`：MeromorphicAt.meromorphic
TrailingCoeffAt_smul {f₁ : 𝕜 -> 𝕜} {f₂ : 𝕜 -> E} (hf₁ : MeromorphicAt f₁ x) (hf₂
 : MeromorphicAt f₂ x) : meromorphi…
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用引理 `MeromorphicAt.comp_analyticAt`：MeromorphicAt.comp_analyticAt {f : 𝕜' -> 
F} {g : 𝕜 -> 𝕜'} (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) : Meromorp
hicAt (f ∘ g) x
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`：AnalyticA
t.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : Int} (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) (h : f =ᶠ[𝓝[!=] x] fun z =…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `g` is analytic at `x` and not locally constant, and `f` is meromorphic at `g
 x`, express the
trailing coefficient of `f ∘ g` at `x` in terms of `g` and `f`.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp {g : 𝕜 → 𝕜} (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicTrailingCoeffAt (f ∘ g) x =
      (meromorphicTrailingCoeffAt (g · - g x) x) ^ (meromorphicOrderAt f (g x)).untop₀ •
      meromorphicTrailingCoeffAt f (g x) := by
  by_cases h : meromorphicOrderAt f (g x) = ⊤
  · have : meromorphicTrailingCoeffAt (f ∘ g) x = 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff] at *
      exact (hg.map_nhdsNE hg_nc) h
    aesop
  · set r := (meromorphicOrderAt f (g x)).untop₀
    obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    have h₁ : meromorphicTrailingCoeffAt (f ∘ g) x
        = meromorphicTrailingCoeffAt ((g · - g x) ^ r • (F ∘ g)) x := by
      apply meromorphicTrailingCoeffAt_congr_nhdsNE
      apply Filter.Tendsto.eventually (hg.map_nhdsNE hg_nc) h₃F
    rw [h₁, MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop) (by fun_prop),
      (h₁F.comp hg).meromorphicTrailingCoeffAt_of_ne_zero h₂F,
      h₁F.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂F h₃F]
    simp_all only [ne_eq, Function.comp_apply, not_false_eq_true, smul_left_inj]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt]
/-
**meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt {c
 : 𝕜} : meromorphicTrailingCoeffAt (f ∘ (· + c)) x = meromorphicTrailingCoeffAt 
f (x + c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicTrailingCoeffAt_of_not_MeromorphicAt`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `meromorphicAt_comp_add_const_iff_meromorphicAt`：meromorphicAt_comp_add_c
onst_iff_meromorphicAt {c : 𝕜} {f : 𝕜 -> E} : MeromorphicAt (f ∘ (· + c)) x ↔ Me
romorphicAt f (x + c)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicAt.meromorphicTrailingCoeffAt_comp`：MeromorphicAt.meromorphic
TrailingCoeffAt_comp {g : 𝕜 -> 𝕜} (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 
𝕜 g x) (hg_nc : ¬EventuallyConst g …
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
· 使用定理 `meromorphicTrailingCoeffAt_id_sub_const`：meromorphicTrailingCoeffAt_id_s
ub_const [DecidableEq 𝕜] {x y : 𝕜} : meromorphicTrailingCoeffAt (· - y) x = if x
 = y then 1 else x - y
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
`meromorphicTrailingCoefficientAt` is invariant under translation.
-/
theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} :
    meromorphicTrailingCoeffAt (f ∘ (· + c)) x = meromorphicTrailingCoeffAt f (x + c) := by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp [meromorphicTrailingCoeffAt_id_sub_const]

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_sub_const_eq_meromorphicTrailingCoeffAt]
/-
**meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt {c
 : 𝕜} : meromorphicTrailingCoeffAt (f ∘ (· - c)) x = meromorphicTrailingCoeffAt 
f (x - c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`meromorphicTrailingCoefficientAt` is invariant under translation.
-/
theorem meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} :
    meromorphicTrailingCoeffAt (f ∘ (· - c)) x = meromorphicTrailingCoeffAt f (x - c) := by
  simp [sub_eq_add_neg, ← meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt]
