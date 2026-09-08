/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Normal form of meromorphic functions and continuous extension

If a function `f` is meromorphic on `U` and if `g` differs from `f` only along a set that is
codiscrete within `U`, then `g` is likewise meromorphic. The set of meromorphic functions is
therefore huge, and `=ᶠ[codiscreteWithin U]` defines an equivalence relation.

This file implements continuous extension to provide an API that allows picking the 'unique best'
representative of any given equivalence class, where 'best' means that the representative can
locally near any point `x` be written 'in normal form', as `f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g`
where `g` is analytic and does not vanish at `x`.

The relevant notions are `MeromorphicNFAt` and `MeromorphicNFOn`; these guarantee normal
form at a single point and along a set, respectively.
-/

@[expose] public section

open Metric Set Topology WithTop
open scoped Pointwise

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜}
  {x : 𝕜}
  {U : Set 𝕜}

/-!
## Normal form of meromorphic functions at a given point

### Definition and characterizations
-/

variable (f x) in
/-- A function is 'meromorphic in normal form' at `x` if it vanishes around `x`
or if it can locally be written as `fun z ↦ (z - x) ^ n • g` where `g` is
analytic and does not vanish at `x`. -/
@[fun_prop]
/-
**MeromorphicNFAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeromorphicNFAt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is 'meromorphic in normal form' at `x` if it vanishes around `x`
or if it can locally be written as `fun z ↦ (z - x) ^ n • g` where `g` is
analytic and does not vanish at `x`.
-/
def MeromorphicNFAt :=
  f =ᶠ[𝓝 x] 0 ∨
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ f =ᶠ[𝓝 x] (· - x) ^ n • g

/-- A meromorphic function has normal form at `x` iff it is either analytic
there, or if it has a pole at `x` and takes the default value `0`. -/
/-
**meromorphicNFAt_iff_analyticAt_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_iff_analyticAt_or : MeromorphicNFAt f x ↔ AnalyticAt 𝕜 f x
 ∨ (MeromorphicAt f x ∧ meromorphicOrderAt f x < 0 ∧ f x = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `analyticAt_congr`：analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x 
↔ AnalyticAt 𝕜 g x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `MeromorphicAt.congr`：congr {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hfg 
: f =ᶠ[𝓝[!=] x] g) : MeromorphicAt g x
· 使用引理 `MeromorphicAt.smul`：smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 
𝕜 -> R} {g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) : Meromor
phicAt (…
· 使用引理 `MeromorphicAt.zpow`：zpow {f : 𝕜 -> 𝕜'} (hf : MeromorphicAt f x) (n : Int
) : MeromorphicAt (f ^ n) x
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.zpow_nonneg`：AnalyticAt.zpow_nonneg {f : E -> 𝕝} {z : E} {n :
 Int} (hf : AnalyticAt 𝕜 f z) (hn : 0 <= n) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.coe_lt_zero`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α] {a :
 α}, ↑a < 0 ↔ a < 0
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
A meromorphic function has normal form at `x` iff it is either analytic
there, or if it has a pole at `x` and takes the default value `0`.
-/
theorem meromorphicNFAt_iff_analyticAt_or :
    MeromorphicNFAt f x ↔
      AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt f x < 0 ∧ f x = 0) := by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : meromorphicOrderAt f x = n := by
        rw [meromorphicOrderAt_eq_int_iff hf]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases! hn : 0 ≤ n
      · left
        rw [analyticAt_congr h₃g]
        apply (AnalyticAt.zpow_nonneg (by fun_prop) hn).smul h₁g
      · right
        use hf
        simp [this, WithTop.coe_lt_zero.2 hn, h₃g.eq_of_nhds,
          zero_zpow n hn.ne]
  · rintro (h | ⟨h₁, h₂, h₃⟩)
    · by_cases h₂f : analyticOrderAt f x = ⊤
      · rw [analyticOrderAt_eq_top] at h₂f
        tauto
      · right
        use analyticOrderNatAt f x
        have : analyticOrderAt f x ≠ ⊤ := h₂f
        rw [← ENat.natCast_toNat_eq_self, eq_comm, h.analyticOrderAt_eq_natCast] at this
        obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
        use g, h₁g, h₂g
        simpa
    · right
      lift meromorphicOrderAt f x to ℤ using LT.lt.ne_top h₂ with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff h₁).1 hn.symm
      use n, g, h₁g, h₂g
      filter_upwards [eventually_nhdsWithin_iff.1 h₃g]
      intro z hz
      by_cases h₁z : z = x
      · simp only [h₁z, Pi.smul_apply', Pi.pow_apply, sub_self]
        rw [h₃]
        apply (smul_eq_zero_of_left (zero_zpow n _) (g x)).symm
        by_contra hCon
        simp [hCon] at h₂
      · exact hz h₁z

/-!
### Relation to other properties of functions
-/

/-- If a function is meromorphic in normal form at `x`, then it is meromorphic at `x`. -/
/-
**MeromorphicNFAt.meromorphicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFAt.meromorphicAt (hf : MeromorphicNFAt f x) : MeromorphicAt f
 x
参数：hf : MeromorphicNFAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFAt_iff_analyticAt_or`：meromorphicNFAt_iff_analyticAt_or : M
eromorphicNFAt f x ↔ AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt 
f x < 0 ∧ f x = 0)
· 使用引理 `AnalyticAt.meromorphicAt`：AnalyticAt.meromorphicAt {f : 𝕜 -> E} {x : 𝕜} 
(hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x

--- 原说明 ---
If a function is meromorphic in normal form at `x`, then it is meromorphic at `x
`.
-/
theorem MeromorphicNFAt.meromorphicAt (hf : MeromorphicNFAt f x) :
    MeromorphicAt f x := by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf
  rcases hf with h | h
  · exact h.meromorphicAt
  · obtain ⟨hf, _⟩ := h
    exact hf

/-- If a function is meromorphic in normal form at `x`, then it has non-negative order iff it is
analytic. -/
/-
**MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : Meromorphic
NFAt f x) : 0 <= meromorphicOrderAt f x ↔ AnalyticAt 𝕜 f x
参数：hf : MeromorphicNFAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFAt_iff_analyticAt_or`：meromorphicNFAt_iff_analyticAt_or : M
eromorphicNFAt f x ↔ AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt 
f x < 0 ∧ f x = 0)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If a function is meromorphic in normal form at `x`, then it has non-negative ord
er iff it is
analytic.
-/
theorem MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
    0 ≤ meromorphicOrderAt f x ↔ AnalyticAt 𝕜 f x := by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicOrderAt_eq]
    simp

/-- Analytic functions are meromorphic in normal form. -/
/-
**AnalyticAt.meromorphicNFAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) : MeromorphicNFAt f x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
Analytic functions are meromorphic in normal form.
-/
theorem AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x := by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

/-- Meromorphic functions have normal form outside of a discrete subset in the domain of
meromorphicity. -/
/-
**MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin {U : Set 𝕜} (hf : Merom
orphicOn f U) : { x | MeromorphicNFAt f x } in Filter.codiscreteWithin U
参数：hf : MeromorphicOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x

--- 原说明 ---
Meromorphic functions have normal form outside of a discrete subset in the domai
n of
meromorphicity.
-/
theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-!
### Vanishing and order
-/

/-- If `f` is meromorphic in normal form at `x`, then `f` has order zero iff it does not vanish at
`x`.

See `AnalyticAt.order_eq_zero_iff` for an analogous statement about analytic functions. -/
/-
**MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) 
: meromorphicOrderAt f x = 0 ↔ f x != 0
参数：hf : MeromorphicNFAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`：MeromorphicNFA
t.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) : 0 <= mer
omorphicOrderAt f x ↔ AnalyticAt 𝕜 f x
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `ENat.map_natCast_eq_zero`：∀ {n : ℕ∞} {α : Type u_1} [inst : AddMonoidWit
hOne α] [inst_1 : PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]   [CharZero
 α], ENat.map …
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `MeromorphicNFAt.meromorphicAt`：MeromorphicNFAt.meromorphicAt (hf : Merom
orphicNFAt f x) : MeromorphicAt f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a

--- 原说明 ---
If `f` is meromorphic in normal form at `x`, then `f` has order zero iff it does
 not vanish at
`x`.

See `AnalyticAt.order_eq_zero_iff` for an analogous statement about analytic fun
ctions.
-/
theorem MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) :
    meromorphicOrderAt f x = 0 ↔ f x ≠ 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    rw [← h₂f.analyticOrderAt_eq_zero, ← ENat.map_natCast_eq_zero (α := ℤ)]
    rwa [h₂f.meromorphicOrderAt_eq] at h₁f
  · intro h
    rcases id hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩
    · have := h₁.eq_of_nhds
      tauto
    · have : n = 0 := by
        by_contra hContra
        have := h₃g.eq_of_nhds
        simp only [Pi.smul_apply', Pi.pow_apply, sub_self, zero_zpow n hContra, zero_smul] at this
        tauto
      simp only [this, zpow_zero] at h₃g
      apply (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).2
      use g, h₁g, h₂g
      simp only [zpow_zero]
      exact h₃g.filter_mono nhdsWithin_le_nhds

/-!
### Local nature of the definition and local identity theorem
-/

/-- **Local identity theorem**: two meromorphic functions in normal form agree in a
neighborhood iff they agree in a pointed neighborhood.

See `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` for the analogous
statement for continuous functions.
-/
/-
**MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 -> E} (hf
 : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) : f =ᶠ[𝓝[!=] x] g ↔ f =ᶠ[𝓝 x]
 g
参数：hf : MeromorphicNFAt f x；hg : MeromorphicNFAt g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`：MeromorphicNFA
t.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) : 0 <= mer
omorphicOrderAt f x ↔ AnalyticAt 𝕜 f x
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`：ContinuousAt.eve
ntuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X -> Y} (hf : 
ContinuousAt f x) (hg : ContinuousAt g x) [(…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`：eventuallyEq_nhds_of_eventuall
yEq_nhdsNE {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g) (h₂ : f a = g a) : f =ᶠ
[𝓝 a] g
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a

--- 原说明 ---
**Local identity theorem**: two meromorphic functions in normal form agree in a
neighborhood iff they agree in a pointed neighborhood.

See `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` for the analogous
statement for continuous functions.
-/
theorem MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 → E}
    (hf : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor
  · intro h
    have t₀ := meromorphicOrderAt_congr h
    by_cases cs : meromorphicOrderAt f x = 0
    · rw [cs] at t₀
      have Z := (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq t₀)).continuousAt
      exact (Z.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE W).1 h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.meromorphicOrderAt_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.meromorphicOrderAt_eq_zero_iff] at h₁g
      simp only [not_not] at *
      rw [h₁f, h₁g]
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)

/-- Meromorphicity in normal form is a local property. -/
/-
**meromorphicNFAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_congr {g : 𝕜 -> E} (hfg : f =ᶠ[𝓝 x] g) : MeromorphicNFAt f
 x ↔ MeromorphicNFAt g x
参数：hfg : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
Meromorphicity in normal form is a local property.
-/
theorem meromorphicNFAt_congr {g : 𝕜 → E} (hfg : f =ᶠ[𝓝 x] g) :
    MeromorphicNFAt f x ↔ MeromorphicNFAt g x := by
  constructor
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.symm.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.symm.trans h₃h⟩
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.trans h₃h⟩

/-!
### Criteria to guarantee normal form
-/

/-- Helper lemma for `meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic`: if
`f` is meromorphic in normal form at `x` and `g` is analytic without zero at
`x`, then `g • f` is meromorphic in normal form at `x`. -/
/-
**MeromorphicNFAt.smul_analytic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicNFAt.smul_analytic (hf : MeromorphicNFAt f x) (h₁g : AnalyticAt
 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (g • f) x
参数：hf : MeromorphicNFAt f x；h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `smul_ne_zero`：smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…

--- 原说明 ---
Helper lemma for `meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic`: if
`f` is meromorphic in normal form at `x` and `g` is analytic without zero at
`x`, then `g • f` is meromorphic in normal form at `x`.
-/
lemma MeromorphicNFAt.smul_analytic (hf : MeromorphicNFAt f x)
    (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g • f) x := by
  rcases hf with h₁f | ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩
  · left
    filter_upwards [h₁f]
    simp_all
  · right
    use n, g • g_f, h₁g.smul h₁g_f
    constructor
    · simp [smul_ne_zero h₂g h₂g_f]
    · filter_upwards [h₃g_f]
      intro y hy
      simp only [Pi.smul_apply', hy, Pi.pow_apply]
      rw [smul_comm]

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g • f` is meromorphic in normal form at `z₀`. -/
/-
**meromorphicNFAt_smul_iff_right_of_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g : AnalyticAt 𝕜 g x) (h₂g
 : g x != 0) : MeromorphicNFAt (g • f) x ↔ MeromorphicNFAt f x where mp hprod
参数：h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `compl_singleton_mem_nhds_iff`：compl_singleton_mem_nhds_iff [T1Space X] {
x y : X} : {x}ᶜ in 𝓝 y ↔ y != x
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `meromorphicNFAt_congr`：meromorphicNFAt_congr {g : 𝕜 -> E} (hfg : f =ᶠ[𝓝 
x] g) : MeromorphicNFAt f x ↔ MeromorphicNFAt g x
· 使用引理 `MeromorphicNFAt.smul_analytic`：MeromorphicNFAt.smul_analytic (hf : Merom
orphicNFAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (g •
 f) x
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0

--- 原说明 ---
If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is mer
omorphic in
normal form at `z₀` iff `g • f` is meromorphic in normal form at `z₀`.
-/
theorem meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g • f) x ↔ MeromorphicNFAt f x where
  mp hprod := by
    have : f =ᶠ[𝓝 x] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact hprod.smul_analytic (h₁g.inv h₂g) (inv_ne_zero h₂g)
  mpr hf := hf.smul_analytic h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g * f` is meromorphic in normal form at `z₀`. -/
/-
**meromorphicNFAt_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_mul_iff_right {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x) (h₂g :
 g x != 0) : MeromorphicNFAt (g * f) x ↔ MeromorphicNFAt f x
参数：h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicNFAt_smul_iff_right_of_analyticAt`：meromorphicNFAt_smul_iff_r
ight_of_analyticAt (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (
g • f) x ↔ MeromorphicNFAt f x whe…

--- 原说明 ---
If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is mer
omorphic in
normal form at `z₀` iff `g * f` is meromorphic in normal form at `z₀`.
-/
theorem meromorphicNFAt_mul_iff_right {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g * f) x ↔ MeromorphicNFAt f x :=
  meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `f * g` is meromorphic in normal form at `z₀`. -/
/-
**meromorphicNFAt_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_mul_iff_left {f : 𝕜 -> 𝕜} (h₁g : AnalyticAt 𝕜 g x) (h₂g : 
g x != 0) : MeromorphicNFAt (f * g) x ↔ MeromorphicNFAt f x
参数：h₁g : AnalyticAt 𝕜 g x；h₂g : g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `meromorphicNFAt_smul_iff_right_of_analyticAt`：meromorphicNFAt_smul_iff_r
ight_of_analyticAt (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (
g • f) x ↔ MeromorphicNFAt f x whe…

--- 原说明 ---
If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is mer
omorphic in
normal form at `z₀` iff `f * g` is meromorphic in normal form at `z₀`.
-/
theorem meromorphicNFAt_mul_iff_left {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (f * g) x ↔ MeromorphicNFAt f x := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
/-
**meromorphicNFAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} 
(h₁f : forall i in s, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ in s |
 f σ x = 0}) : MeromorphicNFAt (∏ i in s, f i) x
参数：h₁f : forall i in s, MeromorphicNFAt (f i) x；h₂f : Set.Subsingleton {σ in s |
 f σ x = 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`：MeromorphicNFA
t.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) : 0 <= mer
omorphicOrderAt f x ↔ AnalyticAt 𝕜 f x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `Finset.analyticAt_prod`：Finset.analyticAt_prod {α : Type*} {A : Type*} [
NormedCommRing A] [NormedAlgebra 𝕜 A] {f : α -> E -> A} {c : E} (N : Finset α) (
h : forall n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.filter_eq_empty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, Finset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `meromorphicNFAt_mul_iff_left`：meromorphicNFAt_mul_iff_left {f : 𝕜 -> 𝕜} 
(h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (f * g) x ↔ Meromorp
hicNFAt f x
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
A product of meromorphic functions in normal form is in normal form if at most o
ne of the factors
vanishes.
-/
theorem meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (∏ i ∈ s, f i) x := by
  classical
  have h₃f {τ : ι} (h₁τ : τ ∈ s) (h₂τ : τ ∉ {σ ∈ s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    grind
  by_cases h₄f : {σ ∈ s | f σ x = 0} = ∅
  · exact (Finset.analyticAt_prod _ (fun σ hσ ↦ h₃f hσ (by aesop))).meromorphicNFAt
  rw [Finset.filter_eq_empty_iff] at h₄f
  push Not at h₄f
  obtain ⟨τ, h₁τ, h₂τ⟩ := h₄f
  have {μ : ι} (hμ : μ ∈ s.erase τ) : f μ x ≠ 0 := by
    by_contra
    have : τ = μ := h₂f (by aesop) (by aesop)
    aesop
  rw [← Finset.mul_prod_erase _ _ h₁τ, meromorphicNFAt_mul_iff_left]
  · apply h₁f τ h₁τ
  · apply Finset.analyticAt_prod _ (fun μ hμ ↦ h₃f (Finset.mem_of_mem_erase hμ) (by aesop))
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    aesop

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
/-
**meromorphicNFAt_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 ->
 𝕜} (h₁f : forall i in s, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ in
 s | f σ x = 0}) : MeromorphicNFAt (fun a => ∏ i in s, f i a) x
参数：h₁f : forall i in s, MeromorphicNFAt (f i) x；h₂f : Set.Subsingleton {σ in s |
 f σ x = 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `meromorphicNFAt_prod`：meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Fins
et ι} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i in s, MeromorphicNFAt (f i) x) (h₂f : Se
t.Subsingl…

--- 原说明 ---
A product of meromorphic functions in normal form is in normal form if at most o
ne of the factors
vanishes.
-/
theorem meromorphicNFAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (fun a ↦ ∏ i ∈ s, f i a) x := by
  convert! meromorphicNFAt_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
/-
**meromorphicNFAt_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι -> 𝕜 -> 𝕜} (h₁f : foral
l i, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ | f σ x = 0}) : Meromor
phicNFAt (∏ᶠ i, f i) x
参数：h₁f : forall i, MeromorphicNFAt (f i) x；h₂f : Set.Subsingleton {σ | f σ x = 0
}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod`：finprod_eq_prod (f : α -> M) (hf : HasFiniteMulSupport 
f) : ∏ᶠ i : α, f i = ∏ i in hf.toFinset, f i
· 使用定理 `meromorphicNFAt_prod`：meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Fins
et ι} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i in s, MeromorphicNFAt (f i) x) (h₂f : Se
t.Subsingl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finprod_of_not_hasFiniteMulSupport`：finprod_of_not_hasFiniteMulSupport {
f : α -> M} (hf : ¬ f.HasFiniteMulSupport) : ∏ᶠ i, f i = 1

--- 原说明 ---
A finprod of meromorphic functions in normal form is in normal form if at most o
ne of the factors
vanishes.
-/
theorem meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ | f σ x = 0}) :
    MeromorphicNFAt (∏ᶠ i, f i) x := by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop) (fun _ _ _ _ ↦ by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt

/--
Integer powers of meromorphic functions in normal form are in normal form.
-/
@[to_fun]
/-
**MeromorphicNFAt.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFAt.zpow {f : 𝕜 -> 𝕜} {n : Int} {x : 𝕜} (hf : MeromorphicNFAt 
f x) : MeromorphicNFAt (f ^ n) x
参数：hf : MeromorphicNFAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AnalyticAt.zpow`：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : A
nalyticAt 𝕜 f z) (h₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z
· 使用引理 `Pi.pow_apply`：pow_apply (f : forall i, M i) (a : α) (i : ι) : (f ^ a) i 
= f i ^ a
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_mul'`：zpow_mul' (a : α) (m n : Int) : a ^ (m * n) = (a ^ n) ^ m

--- 原说明 ---
Integer powers of meromorphic functions in normal form are in normal form.
-/
theorem MeromorphicNFAt.zpow {f : 𝕜 → 𝕜} {n : ℤ} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (f ^ n) x := by
  by_cases hn : n = 0
  · simp_all only [zpow_zero]
    apply AnalyticAt.meromorphicNFAt
    apply analyticAt_const
  rcases hf with hf | hf
  · left
    filter_upwards [hf] with z hz
    simp_all only [Pi.zero_apply, Pi.pow_apply, zero_zpow n hn]
  · obtain ⟨m, g, h₁g, h₂g, h₃g⟩ := hf
    right
    use n * m, g ^ n, h₁g.zpow h₂g
    constructor
    · rw [Pi.pow_apply]
      exact zpow_ne_zero n h₂g
    · filter_upwards [h₃g] with z hz
      simp [hz, mul_zpow, (zpow_mul' (z - x) n m).symm]

/--
If `f` is meromorphic in normal form, then so is its inverse.
-/
/-
**MeromorphicNFAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFAt.inv {f : 𝕜 -> 𝕜} (hf : MeromorphicNFAt f x) : MeromorphicN
FAt f⁻¹ x
参数：hf : MeromorphicNFAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_inv_one`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {a : α}, Mathlib.Meta.NormNum.IsNat a 1 → Mathlib.Meta.NormNum.IsNat a⁻
¹ 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is meromorphic in normal form, then so is its inverse.
-/
theorem MeromorphicNFAt.inv {f : 𝕜 → 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt f⁻¹ x := by
  rcases hf with h | ⟨n, g, h₁, h₂, h₃⟩
  · left
    filter_upwards [h] with x hx
    simp [hx]
  · right
    use -n, g⁻¹, h₁.inv h₂, (by simp_all)
    filter_upwards [h₃] with y hy
    simp only [Pi.inv_apply, hy, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, mul_inv_rev, zpow_neg]
    ring

/--
A function to 𝕜 is meromorphic in normal form at a point iff its inverse is.
-/
/-
**meromorphicNFAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {f : 𝕜 → 𝕜}, M
eromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFAt.inv`：MeromorphicNFAt.inv {f : 𝕜 -> 𝕜} (hf : MeromorphicN
FAt f x) : MeromorphicNFAt f⁻¹ x
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
A function to 𝕜 is meromorphic in normal form at a point iff its inverse is.
-/
@[simp] theorem meromorphicNFAt_inv {f : 𝕜 → 𝕜} : MeromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x where
  mp hf := inv_inv f ▸ hf.inv
  mpr hf := hf.inv
/-
**MeromorphicNFOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFOn.div {f : 𝕜 -> 𝕜} {g : 𝕜 -> 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f
 x) (hg : MeromorphicNFAt g x) (hor : g x != 0 ∨ f x != 0) : MeromorphicNFAt (f 
/ g) x
参数：hf : AnalyticAt 𝕜 f x；hg : MeromorphicNFAt g x；hor : g x != 0 ∨ f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `AnalyticAt.inv`：AnalyticAt.inv {f : E -> 𝕝} {x : E} (fa : AnalyticAt 𝕜 f
 x) (f0 : f x != 0) : AnalyticAt 𝕜 f⁻¹ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicNFAt_mul_iff_left`：meromorphicNFAt_mul_iff_left {f : 𝕜 -> 𝕜} 
(h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (f * g) x ↔ Meromorp
hicNFAt f x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem MeromorphicNFOn.div {f : 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : MeromorphicNFAt g x) (hor : g x ≠ 0 ∨ f x ≠ 0) : MeromorphicNFAt (f / g) x := by
  rw [div_eq_mul_inv]
  rcases hor with hgne | hfne
  · have hf := hf.meromorphicNFAt
    have hgAnalytic : AnalyticAt 𝕜 g x := by grind [meromorphicNFAt_iff_analyticAt_or]
    have hgInvAnalytic : AnalyticAt 𝕜 g⁻¹ x := hgAnalytic.inv hgne
    rwa [← meromorphicNFAt_mul_iff_left hgInvAnalytic (inv_ne_zero hgne)] at hf
  · grind [meromorphicNFAt_mul_iff_right, hg.inv]

/--
The composition of a meromorphic function in normal form and an analytic
function is meromorphic in normal form.
-/
@[fun_prop]
/-
**MeromorphicNFAt.comp_analyticAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFAt.comp_analyticAt (hf : MeromorphicNFAt f (g x)) (hg : Analy
ticAt 𝕜 g x) : MeromorphicNFAt (f ∘ g) x
参数：hf : MeromorphicNFAt f (g x)；hg : AnalyticAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.zpow`：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : A
nalyticAt 𝕜 f z) (h₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The composition of a meromorphic function in normal form and an analytic
function is meromorphic in normal form.
-/
theorem MeromorphicNFAt.comp_analyticAt (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicNFAt (f ∘ g) x := by
  rcases hf with hf | ⟨n, q, hq_an, hq_ne, hf⟩
  · exact Or.inl (hg.continuousAt.tendsto.eventually hf)
  by_cases hord : analyticOrderAt (g · - g x) x = ⊤
  · rw [analyticOrderAt_eq_top] at hord
    by_cases h : f (g x) = 0
    · apply Or.inl
      filter_upwards [hord, hg.continuousAt.preimage_mem_nhds (hf.filter_mono (by simp))]
        using by simp_all [sub_eq_zero]
    · refine Or.inr ⟨0, fun _ ↦ f (g x), by fun_prop, h, ?_⟩
      filter_upwards [hord, hg.continuousAt.preimage_mem_nhds (hf.filter_mono (by simp))]
        using by simp_all [sub_eq_zero]
  lift analyticOrderAt (g · - g x) x to ℕ using hord with m hm
  obtain ⟨p, h₁p, h₂p, h₃p⟩ := (AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)).1 hm.symm
  refine Or.inr ⟨n * m, fun z ↦ (p z) ^ n • q (g z), (h₁p.zpow h₂p).smul (by fun_prop), ?_⟩
  simp_all only [ne_eq, smul_eq_mul, isUnit_iff_ne_zero, zpow_ne_zero n h₂p, not_false_eq_true,
    IsUnit.smul_eq_zero, true_and]
  filter_upwards [h₃p, hg.continuousAt.preimage_mem_nhds (hf.filter_mono (by simp))]
    with a h₁a h₂a
  simp_all only [Pi.smul_apply', Pi.pow_apply, Set.preimage_ofPred_eq, Set.mem_ofPred_eq,
    Function.comp_apply, ← smul_assoc, mul_zpow, smul_eq_mul]
  congr 2
  rw [mul_comm, zpow_mul, zpow_natCast]

/--
A function is meromorphic in normal form at a point iff it is meromorphic in normal form after
composition with an analytic function of nonvanishing derivative, such as translation.
-/
/-
**meromorphicNFAt_comp_iff_of_deriv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {
x : 𝕜} {g : 𝕜 -> 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0) : Meromorphic
NFAt (f ∘ g) x ↔ MeromorphicNFAt f (g x)
参数：hg : AnalyticAt 𝕜 g x；hg' : deriv g x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `analyticAt_comp_iff_of_deriv_ne_zero`：analyticAt_comp_iff_of_deriv_ne_ze
ro (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0) : AnalyticAt 𝕜 (g ∘ f) x ↔ Ana
lyticAt 𝕜 g (f x)
· 使用引理 `meromorphicAt_comp_iff_of_deriv_ne_zero`：meromorphicAt_comp_iff_of_deriv
_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> E} {g : 𝕜 -> 𝕜} (hg : Analytic
At 𝕜 g x) (hg' : deriv g x !=…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `meromorphicOrderAt_comp_of_deriv_ne_zero`：meromorphicOrderAt_comp_of_der
iv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0) [CompleteSpace 𝕜] [Cha
rZero 𝕜] : meromorphicOrderAt …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is meromorphic in normal form at a point iff it is meromorphic in nor
mal form after
composition with an analytic function of nonvanishing derivative, such as transl
ation.
-/
theorem meromorphicNFAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {x : 𝕜}
    {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    MeromorphicNFAt (f ∘ g) x ↔ MeromorphicNFAt f (g x) := by
  simp [meromorphicNFAt_iff_analyticAt_or, analyticAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicAt_comp_iff_of_deriv_ne_zero hg hg',
    meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt]
/-
**meromorphicNFAt_comp_add_const_iff_meromorphicNFAt** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：meromorphicNFAt_comp_add_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 -> E} : 
MeromorphicNFAt (f ∘ (· + c)) x ↔ MeromorphicNFAt f (x + c)
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
· 使用定理 `MeromorphicNFAt.comp_analyticAt`：MeromorphicNFAt.comp_analyticAt (hf : M
eromorphicNFAt f (g x)) (hg : AnalyticAt 𝕜 g x) : MeromorphicNFAt (f ∘ g) x
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
`MeromorphicNFAt` is invariant under translation.
-/
theorem meromorphicNFAt_comp_add_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicNFAt (f ∘ (· + c)) x ↔ MeromorphicNFAt f (x + c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = ((f ∘ fun x ↦ x + c) ∘ fun z ↦ z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_sub_const_iff_meromorphicNFAt]
/-
**meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 -> E} : 
MeromorphicNFAt (f ∘ (· - c)) x ↔ MeromorphicNFAt f (x - c)
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
`MeromorphicNFAt` is invariant under translation.
-/
theorem meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicNFAt (f ∘ (· - c)) x ↔ MeromorphicNFAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]

/-!
### Continuous extension and conversion to normal form
-/

variable (f x) in
/-- If `f` is meromorphic at `x`, convert `f` to normal form at `x` by changing its value at `x`.
Otherwise, returns the 0 function. -/
/-
**toMeromorphicNFAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toMeromorphicNFAt : 𝕜 -> E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic at `x`, convert `f` to normal form at `x` by changing its 
value at `x`.
Otherwise, returns the 0 function.
-/
noncomputable def toMeromorphicNFAt :
    𝕜 → E := by
  by_cases hf : MeromorphicAt f x
  · classical -- do not complain about decidability issues in Function.update
    apply Function.update f x
    by_cases h₁f : meromorphicOrderAt f x = (0 : ℤ)
    · rw [meromorphicOrderAt_eq_int_iff hf] at h₁f
      exact (Classical.choose h₁f) x
    · exact 0
  · exact 0

/-- Conversion to normal form at `x` changes the value only at x. -/
/-
**MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt (hf : MeromorphicAt f
 x) : Set.EqOn f (toMeromorphicNFAt f x) {x}ᶜ
参数：hf : MeromorphicAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Conversion to normal form at `x` changes the value only at x.
-/
lemma MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    Set.EqOn f (toMeromorphicNFAt f x) {x}ᶜ :=
  fun _ _ ↦ by simp_all [toMeromorphicNFAt]

/-- If `f` is not meromorphic, conversion to normal form at `x` maps the function to `0`. -/
/-
**toMeromorphicNFAt_of_not_meromorphicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}, ¬Mero
morphicAt f x → toMeromorphicNFAt f x = 0
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
If `f` is not meromorphic, conversion to normal form at `x` maps the function to
 `0`.
-/
@[simp] lemma toMeromorphicNFAt_of_not_meromorphicAt (hf : ¬MeromorphicAt f x) :
    toMeromorphicNFAt f x = 0 := by
  simp [toMeromorphicNFAt, hf]
/-
**toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}, merom
orphicOrderAt f x ≠ 0 → toMeromorphicNFAt f x x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero
    (horder : meromorphicOrderAt f x ≠ 0) : toMeromorphicNFAt f x x = 0 := by
  simp [toMeromorphicNFAt, meromorphicAt_of_meromorphicOrderAt_ne_zero, horder]

/-- Conversion to normal form at `x` changes the value only at x. -/
/-
**MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt (hf : MeromorphicAt f x) : f =ᶠ[
𝓝[!=] x] toMeromorphicNFAt f x
参数：hf : MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用引理 `MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt`：MeromorphicAt.eqOn
_compl_singleton_toMeromorphicNFAt (hf : MeromorphicAt f x) : Set.EqOn f (toMero
morphicNFAt f x) {x}ᶜ

--- 原说明 ---
Conversion to normal form at `x` changes the value only at x.
-/
lemma MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    f =ᶠ[𝓝[≠] x] toMeromorphicNFAt f x :=
  eventually_nhdsWithin_of_forall (fun _ hz ↦ hf.eqOn_compl_singleton_toMeromorphicNFAt hz)

/-- After conversion to normal form at `x`, the function has normal form. -/
/-
**meromorphicNFAt_toMeromorphicNFAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFAt_toMeromorphicNFAt : MeromorphicNFAt (toMeromorphicNFAt f x
) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`：eventuallyEq_nhds_of_eventuall
yEq_nhdsNE {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g) (h₂ : f a = g a) : f =ᶠ
[𝓝 a] g
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`：MeromorphicAt.eq_nhdsNE_toMer
omorphicNFAt (hf : MeromorphicAt f x) : f =ᶠ[𝓝[!=] x] toMeromorphicNFAt f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `analyticAt_congr`：analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x 
↔ AnalyticAt 𝕜 g x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
After conversion to normal form at `x`, the function has normal form.
-/
theorem meromorphicNFAt_toMeromorphicNFAt :
    MeromorphicNFAt (toMeromorphicNFAt f x) x := by
  by_cases hf : MeromorphicAt f x
  · by_cases h₂f : meromorphicOrderAt f x = ⊤
    · have : toMeromorphicNFAt f x =ᶠ[𝓝 x] 0 := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        · exact hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₂f)
        · simp [h₂f, toMeromorphicNFAt, hf]
      apply AnalyticAt.meromorphicNFAt
      rw [analyticAt_congr this]
      exact analyticAt_const
    · lift meromorphicOrderAt f x to ℤ using h₂f with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
      right
      use n, g, h₁g, h₂g
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans h₃g)
      simp only [toMeromorphicNFAt, hf, ↓reduceDIte, ← hn, WithTop.coe_zero,
        WithTop.coe_eq_zero, ne_eq, Function.update_self, sub_self]
      split_ifs with h₃f
      · obtain ⟨h₁G, _, h₃G⟩ :=
          Classical.choose_spec ((meromorphicOrderAt_eq_int_iff hf).1 (h₃f ▸ hn.symm))
        apply Filter.EventuallyEq.eq_of_nhds
        apply (h₁G.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop)).1
        filter_upwards [h₃g, h₃G]
        simp_all
      · simp [h₃f, zero_zpow]
  · simp only [toMeromorphicNFAt, hf, ↓reduceDIte]
    exact analyticAt_const.meromorphicNFAt

@[simp]
/-
**MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt (hf : MeromorphicAt f x
) : meromorphicOrderAt (toMeromorphicNFAt f x) x = meromorphicOrderAt f x
参数：hf : MeromorphicAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用引理 `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`：MeromorphicAt.eq_nhdsNE_toMer
omorphicNFAt (hf : MeromorphicAt f x) : f =ᶠ[𝓝[!=] x] toMeromorphicNFAt f x
-/
lemma MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    meromorphicOrderAt (toMeromorphicNFAt f x) x = meromorphicOrderAt f x :=
  (meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt).symm
/-
**MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero** 是 Mat
hlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero (hf
 : MeromorphicAt f x) : meromorphicOrderAt f x = 0 ↔ toMeromorphicNFAt f x x != 
0
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `meromorphicNFAt_toMeromorphicNFAt`：meromorphicNFAt_toMeromorphicNFAt : M
eromorphicNFAt (toMeromorphicNFAt f x) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt`：MeromorphicAt.meromo
rphicOrderAt_toMeromorphicNFAt (hf : MeromorphicAt f x) : meromorphicOrderAt (to
MeromorphicNFAt f x) x = meromorphicOrde…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma MeromorphicAt.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero
    (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 ↔ toMeromorphicNFAt f x x ≠ 0 := by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_eq_zero_iff, hf]
/-
**MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt** 是 M
athlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt (
hf : MeromorphicAt f x) : 0 <= meromorphicOrderAt f x ↔ AnalyticAt 𝕜 (toMeromorp
hicNFAt f x) x
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`：MeromorphicNFA
t.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) : 0 <= mer
omorphicOrderAt f x ↔ AnalyticAt 𝕜 f x
· 使用定理 `meromorphicNFAt_toMeromorphicNFAt`：meromorphicNFAt_toMeromorphicNFAt : M
eromorphicNFAt (toMeromorphicNFAt f x) x
· 使用引理 `MeromorphicAt.meromorphicOrderAt_toMeromorphicNFAt`：MeromorphicAt.meromo
rphicOrderAt_toMeromorphicNFAt (hf : MeromorphicAt f x) : meromorphicOrderAt (to
MeromorphicNFAt f x) x = meromorphicOrde…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma MeromorphicAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt
    (hf : MeromorphicAt f x) :
    0 ≤ meromorphicOrderAt f x ↔ AnalyticAt 𝕜 (toMeromorphicNFAt f x) x := by
  simp [← meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt, hf]

@[gcongr]
/-
**toMeromorphicNFAt_eventuallyEq_nhds_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toMeromorphicNFAt_eventuallyEq_nhds_congr {f g : 𝕜 -> E} (hfg : f =ᶠ[𝓝[!=]
 x] g) : toMeromorphicNFAt f x =ᶠ[𝓝 x] toMeromorphicNFAt g x
参数：hfg : f =ᶠ[𝓝[!=] x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`：MeromorphicNF
At.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 -> E} (hf : MeromorphicNFAt 
f x) (hg : MeromorphicNFAt g x) : f =ᶠ[𝓝[!=] x]…
· 使用定理 `meromorphicNFAt_toMeromorphicNFAt`：meromorphicNFAt_toMeromorphicNFAt : M
eromorphicNFAt (toMeromorphicNFAt f x) x
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`：MeromorphicAt.eq_nhdsNE_toMer
omorphicNFAt (hf : MeromorphicAt f x) : f =ᶠ[𝓝[!=] x] toMeromorphicNFAt f x
· 使用引理 `MeromorphicAt.meromorphicAt_congr`：meromorphicAt_congr {f g : 𝕜 -> E} (h
 : f =ᶠ[𝓝[!=] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toMeromorphicNFAt_of_not_meromorphicAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
lemma toMeromorphicNFAt_eventuallyEq_nhds_congr {f g : 𝕜 → E} (hfg : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x =ᶠ[𝓝 x] toMeromorphicNFAt g x := by
  by_cases hf : MeromorphicAt f x
  · exact meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        meromorphicNFAt_toMeromorphicNFAt |>.mp <| hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans
      <| hfg.trans ((MeromorphicAt.meromorphicAt_congr hfg).mp hf).eq_nhdsNE_toMeromorphicNFAt
  · simp [hf, MeromorphicAt.meromorphicAt_congr hfg |>.not.mp]

@[simp]
/-
**MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff {f g : 𝕜 -> E} (hf :
 MeromorphicAt f x) (hg : MeromorphicAt g x) : toMeromorphicNFAt f x =ᶠ[𝓝 x] toM
eromorphicNFAt g x ↔ f =ᶠ[𝓝[!=] x] g where mp h
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用引理 `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`：MeromorphicAt.eq_nhdsNE_toMer
omorphicNFAt (hf : MeromorphicAt f x) : f =ᶠ[𝓝[!=] x] toMeromorphicNFAt f x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `toMeromorphicNFAt_eventuallyEq_nhds_congr`：toMeromorphicNFAt_eventuallyE
q_nhds_congr {f g : 𝕜 -> E} (hfg : f =ᶠ[𝓝[!=] x] g) : toMeromorphicNFAt f x =ᶠ[𝓝
 x] toMeromorphicNFAt g x
-/
lemma MeromorphicAt.toMeromorphicNFAt_eventuallyEq_nhds_iff {f g : 𝕜 → E} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    toMeromorphicNFAt f x =ᶠ[𝓝 x] toMeromorphicNFAt g x ↔ f =ᶠ[𝓝[≠] x] g where
  mp h :=
    hf.eq_nhdsNE_toMeromorphicNFAt.trans (h.filter_mono nhdsWithin_le_nhds)
      |>.trans hg.eq_nhdsNE_toMeromorphicNFAt.symm
  mpr := toMeromorphicNFAt_eventuallyEq_nhds_congr

/-- If `f` has normal form at `x`, then `f` equals `f.toNF`. -/
/-
**toMeromorphicNFAt_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜}, toMer
omorphicNFAt f x = f ↔ MeromorphicNFAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicNFAt_toMeromorphicNFAt`：meromorphicNFAt_toMeromorphicNFAt : M
eromorphicNFAt (toMeromorphicNFAt f x) x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeromorphicNFAt.meromorphicAt`：MeromorphicNFAt.meromorphicAt (hf : Merom
orphicNFAt f x) : MeromorphicAt f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOrderAt_eq_top_iff`：meromorphicOrderAt_eq_top_iff : meromorph
icOrderAt f x = ⊤ ↔ forallᶠ z in 𝓝[!=] x, f z = 0
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用引理 `meromorphicOrderAt_eq_int_iff`：meromorphicOrderAt_eq_int_iff {n : Int} (
hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔ exists g : 𝕜 -> E, Analyt
icAt 𝕜 g x ∧ g x !=…
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` has normal form at `x`, then `f` equals `f.toNF`.
-/
@[simp] theorem toMeromorphicNFAt_eq_self :
    toMeromorphicNFAt f x = f ↔ MeromorphicNFAt f x where
  mp hf := by
    rw [hf.symm]
    exact meromorphicNFAt_toMeromorphicNFAt
  mpr hf := by
    funext z
    by_cases hz : z = x
    · rw [hz]
      simp only [toMeromorphicNFAt, hf.meromorphicAt, WithTop.coe_zero, ne_eq]
      have h₀f := hf
      rcases hf with h₁f | h₁f
      · simpa [meromorphicOrderAt_eq_top_iff.2 (h₁f.filter_mono nhdsWithin_le_nhds)]
          using h₁f.eq_of_nhds.symm
      · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁f
        rw [Filter.EventuallyEq.eq_of_nhds h₃g]
        have : meromorphicOrderAt f x = n := by
          rw [meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt]
          use g, h₁g, h₂g
          exact eventually_nhdsWithin_of_eventually_nhds h₃g
        by_cases h₃f : meromorphicOrderAt f x = 0
        · simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte]
          have hn : n = (0 : ℤ) := by
            rw [h₃f] at this
            exact WithTop.coe_eq_zero.mp this.symm
          simp_rw [hn]
          simp only [zpow_zero, one_smul]
          have : g =ᶠ[𝓝 x]
              Classical.choose ((meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt).1 h₃f) := by
            obtain ⟨h₀, h₁, h₂⟩ := Classical.choose_spec
              ((meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt).1 h₃f)
            rw [← h₁g.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₀.continuousAt]
            rw [hn] at h₃g
            simp only [zpow_zero, one_smul, ne_eq] at h₃g h₂
            exact (h₃g.filter_mono nhdsWithin_le_nhds).symm.trans h₂
          simp only [Function.update_self]
          exact Filter.EventuallyEq.eq_of_nhds this.symm
        · rw [eq_comm]
          simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte, smul_eq_zero,
            Function.update_self, smul_eq_zero]
          left
          apply zero_zpow n
          by_contra hn
          rw [hn] at this
          tauto
    · exact (hf.meromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt hz).symm

/-!
## Normal form of meromorphic functions on a given set

### Definition
-/

/--
A function is 'meromorphic in normal form' on `U` if has normal form at every
point of `U`.
-/
/-
**MeromorphicNFOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeromorphicNFOn (f : 𝕜 -> E) (U : Set 𝕜)
参数：f : 𝕜 -> E；U : Set 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is 'meromorphic in normal form' on `U` if has normal form at every
point of `U`.
-/
def MeromorphicNFOn (f : 𝕜 → E) (U : Set 𝕜) := ∀ ⦃z⦄, z ∈ U → MeromorphicNFAt f z

/-!
### Relation to other properties of functions
-/

/--
If a function is meromorphic in normal form on `U`, then it is meromorphic on
`U`.
-/
/-
**MeromorphicNFOn.meromorphicOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFOn.meromorphicOn (hf : MeromorphicNFOn f U) : MeromorphicOn f
 U
参数：hf : MeromorphicNFOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFAt.meromorphicAt`：MeromorphicNFAt.meromorphicAt (hf : Merom
orphicNFAt f x) : MeromorphicAt f x

--- 原说明 ---
If a function is meromorphic in normal form on `U`, then it is meromorphic on
`U`.
-/
theorem MeromorphicNFOn.meromorphicOn (hf : MeromorphicNFOn f U) :
    MeromorphicOn f U := fun _ hz ↦ (hf hz).meromorphicAt

/--
If a function is meromorphic in normal form on `U`, then its divisor is
non-negative iff it is analytic.
-/
/-
**MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f : MeromorphicNFOn f 
U) : 0 <= MeromorphicOn.divisor f U ↔ AnalyticOnNhd 𝕜 f U
参数：h₁f : MeromorphicNFOn f U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`：MeromorphicNFA
t.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) : 0 <= mer
omorphicOrderAt f x ↔ AnalyticAt 𝕜 f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If a function is meromorphic in normal form on `U`, then its divisor is
non-negative iff it is analytic.
-/
theorem MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
    (h₁f : MeromorphicNFOn f U) :
    0 ≤ MeromorphicOn.divisor f U ↔ AnalyticOnNhd 𝕜 f U := by
  constructor <;> intro h x
  · intro hx
    rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
    have := h x
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
      MeromorphicOn.divisor_apply, untop₀_nonneg] at this
    assumption
  · by_cases hx : x ∈ U
    · simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
        MeromorphicOn.divisor_apply, untop₀_nonneg]
      exact (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt.2 (h x hx)
    · simp [hx]

/-- Analytic functions are meromorphic in normal form. -/
/-
**AnalyticOnNhd.meromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) : MeromorphicNFO
n f U
参数：h₁f : AnalyticOnNhd 𝕜 f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x

--- 原说明 ---
Analytic functions are meromorphic in normal form.
-/
theorem AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) :
    MeromorphicNFOn f U := fun z hz ↦ (h₁f z hz).meromorphicNFAt

/-!
### Divisors and zeros of meromorphic functions in normal form.
-/

/--
If `f` is meromorphic in normal form on `U` and nowhere locally constant zero,
then its zero set equals the support of the associated divisor.
-/
/-
**MeromorphicNFOn.zero_set_eq_divisor_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFOn.zero_set_eq_divisor_support (h₁f : MeromorphicNFOn f U) (h
₂f : forall u : U, meromorphicOrderAt f u != ⊤) : U inter f ⁻¹' {0} = Function.s
upport (MeromorphicOn.divisor f U)
参数：h₁f : MeromorphicNFOn f U；h₂f : forall u : U, meromorphicOrderAt f u != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`：MeromorphicNFAt.meromorp
hicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) : meromorphicOrderAt f x = 0 ↔
 f x != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p

--- 原说明 ---
If `f` is meromorphic in normal form on `U` and nowhere locally constant zero,
then its zero set equals the support of the associated divisor.
-/
theorem MeromorphicNFOn.zero_set_eq_divisor_support (h₁f : MeromorphicNFOn f U)
    (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) :
    U ∩ f ⁻¹' {0} = Function.support (MeromorphicOn.divisor f U) := by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.forall, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untop₀_eq_zero, (h₁f hu.1).meromorphicOrderAt_eq_zero_iff, not_true_eq_false, or_self,
      not_false_eq_true]
  · simp only [Function.mem_support, ne_eq] at hu
    constructor
    · exact (MeromorphicOn.divisor f U).supportWithinDomain hu
    · rw [Set.mem_preimage, Set.mem_singleton_iff]
      have := h₁f ((MeromorphicOn.divisor f U).supportWithinDomain hu)
        |>.meromorphicOrderAt_eq_zero_iff.not
      simp only [h₁f.meromorphicOn, (MeromorphicOn.divisor f U).supportWithinDomain hu,
        MeromorphicOn.divisor_apply, WithTop.untop₀_eq_zero, not_or] at hu
      simp_all [hu.1]

/-!
### Criteria to guarantee normal form
-/

/--
If `f` is any function and `g` is analytic without zero on `U`, then `f` is
meromorphic in normal form on `U` iff `g • f` is meromorphic in normal form on
`U`.
-/
/-
**meromorphicNFOn_smul_iff_right_of_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_smul_iff_right_of_analyticOnNhd {g : 𝕜 -> 𝕜} (h₁g : Analyt
icOnNhd 𝕜 g U) (h₂g : forall u in U, g u != 0) : MeromorphicNFOn (g • f) U ↔ Mer
omorphicNFOn f U
参数：h₁g : AnalyticOnNhd 𝕜 g U；h₂g : forall u in U, g u != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicNFAt_smul_iff_right_of_analyticAt`：meromorphicNFAt_smul_iff_r
ight_of_analyticAt (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (
g • f) x ↔ MeromorphicNFAt f x whe…
· 使用引理 `MeromorphicNFAt.smul_analytic`：MeromorphicNFAt.smul_analytic (hf : Merom
orphicNFAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x != 0) : MeromorphicNFAt (g •
 f) x

--- 原说明 ---
If `f` is any function and `g` is analytic without zero on `U`, then `f` is
meromorphic in normal form on `U` iff `g • f` is meromorphic in normal form on
`U`.
-/
theorem meromorphicNFOn_smul_iff_right_of_analyticOnNhd {g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (g • f) U ↔ MeromorphicNFOn f U := by
  constructor <;> intro h z hz
  · rw [← meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g z hz) (h₂g z hz)]
    exact h hz
  · apply (h hz).smul_analytic (h₁g z hz)
    exact h₂g z hz

/--
If `f` is any function and `g` is analytic without zero in `U`, then `f` is
meromorphic in normal form on `U` iff `g * f` is meromorphic in normal form on
`U`.
-/
/-
**meromorphicNFOn_mul_iff_right_of_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_mul_iff_right_of_analyticOnNhd {f g : 𝕜 -> 𝕜} (h₁g : Analy
ticOnNhd 𝕜 g U) (h₂g : forall u in U, g u != 0) : MeromorphicNFOn (g * f) U ↔ Me
romorphicNFOn f U
参数：h₁g : AnalyticOnNhd 𝕜 g U；h₂g : forall u in U, g u != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `meromorphicNFOn_smul_iff_right_of_analyticOnNhd`：meromorphicNFOn_smul_if
f_right_of_analyticOnNhd {g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U) (h₂g : forall 
u in U, g u != 0) : MeromorphicNFOn (…

--- 原说明 ---
If `f` is any function and `g` is analytic without zero in `U`, then `f` is
meromorphic in normal form on `U` iff `g * f` is meromorphic in normal form on
`U`.
-/
theorem meromorphicNFOn_mul_iff_right_of_analyticOnNhd {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (g * f) U ↔ MeromorphicNFOn f U := by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticOnNhd h₁g h₂g

/--
If `f` is any function and `g` is analytic without zero in `U`, then `f` is
meromorphic in normal form on `U` iff `f * g` is meromorphic in normal form on
`U`.
-/
/-
**meromorphicNFOn_mul_iff_left_of_analyticOnNhd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_mul_iff_left_of_analyticOnNhd {f g : 𝕜 -> 𝕜} (h₁g : Analyt
icOnNhd 𝕜 g U) (h₂g : forall u in U, g u != 0) : MeromorphicNFOn (f * g) U ↔ Mer
omorphicNFOn f U
参数：h₁g : AnalyticOnNhd 𝕜 g U；h₂g : forall u in U, g u != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `meromorphicNFOn_mul_iff_right_of_analyticOnNhd`：meromorphicNFOn_mul_iff_
right_of_analyticOnNhd {f g : 𝕜 -> 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U) (h₂g : forall 
u in U, g u != 0) : MeromorphicNFOn …

--- 原说明 ---
If `f` is any function and `g` is analytic without zero in `U`, then `f` is
meromorphic in normal form on `U` iff `f * g` is meromorphic in normal form on
`U`.
-/
theorem meromorphicNFOn_mul_iff_left_of_analyticOnNhd {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (f * g) U ↔ MeromorphicNFOn f U := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFOn_mul_iff_right_of_analyticOnNhd h₁g h₂g

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
/-
**meromorphicNFOn_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} (h₁f : f
orall i in s, MeromorphicNFOn (f i) U) (h₂f : forall x in U, Set.Subsingleton {σ
 in s | f σ x = 0}) : MeromorphicNFOn (∏ i in s, f i) U
参数：h₁f : forall i in s, MeromorphicNFOn (f i) U；h₂f : forall x in U, Set.Subsing
leton {σ in s | f σ x = 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicNFAt_prod`：meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Fins
et ι} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i in s, MeromorphicNFAt (f i) x) (h₂f : Se
t.Subsingl…

--- 原说明 ---
A product of meromorphic functions in normal form is in normal form if at most o
ne of the factors
vanishes.
-/
theorem meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFOn (∏ i ∈ s, f i) U :=
  fun x hx ↦ meromorphicNFAt_prod (h₁f · · hx) (h₂f x hx)

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
/-
**meromorphicNFOn_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_fun_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜} (h₁f
 : forall i in s, MeromorphicNFOn (f i) U) (h₂f : forall x in U, Set.Subsingleto
n {σ in s | f σ x = 0}) : MeromorphicNFOn (fun x => ∏ i in s, f i x) U
参数：h₁f : forall i in s, MeromorphicNFOn (f i) U；h₂f : forall x in U, Set.Subsing
leton {σ in s | f σ x = 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `meromorphicNFOn_prod`：meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {f
 : ι -> 𝕜 -> 𝕜} (h₁f : forall i in s, MeromorphicNFOn (f i) U) (h₂f : forall x i
n U, Set.S…

--- 原说明 ---
A product of meromorphic functions in normal form is in normal form if at most o
ne of the factors
vanishes.
-/
theorem meromorphicNFOn_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFOn (fun x ↦ ∏ i ∈ s, f i x) U := by
  convert! meromorphicNFOn_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
/-
**meromorphicNFOn_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_finprod {ι : Type*} {f : ι -> 𝕜 -> 𝕜} (h₁f : forall i, Mer
omorphicNFOn (f i) U) (h₂f : forall x in U, Set.Subsingleton {σ | f σ x = 0}) : 
MeromorphicNFOn (∏ᶠ i, f i) U
参数：h₁f : forall i, MeromorphicNFOn (f i) U；h₂f : forall x in U, Set.Subsingleton
 {σ | f σ x = 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicNFAt_finprod`：meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f 
: ι -> 𝕜 -> 𝕜} (h₁f : forall i, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton
 {σ | f σ x =…

--- 原说明 ---
A finprod of meromorphic functions in normal form is in normal form if at most o
ne of the factors
vanishes.
-/
theorem meromorphicNFOn_finprod {ι : Type*} {f : ι → 𝕜 → 𝕜} (h₁f : ∀ i, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ | f σ x = 0}) :
  MeromorphicNFOn (∏ᶠ i, f i) U :=
  fun x hx ↦ meromorphicNFAt_finprod (h₁f · hx) (h₂f x hx)

/--
Integer powers of meromorphic functions in normal form are in normal form.
-/
@[to_fun]
/-
**MeromorphicNFOn.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicNFOn.zpow {f : 𝕜 -> 𝕜} {n : Int} {U : Set 𝕜} (hf : MeromorphicN
FOn f U) : MeromorphicNFOn (f ^ n) U
参数：hf : MeromorphicNFOn f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFAt.zpow`：MeromorphicNFAt.zpow {f : 𝕜 -> 𝕜} {n : Int} {x : 𝕜
} (hf : MeromorphicNFAt f x) : MeromorphicNFAt (f ^ n) x

--- 原说明 ---
Integer powers of meromorphic functions in normal form are in normal form.
-/
theorem MeromorphicNFOn.zpow {f : 𝕜 → 𝕜} {n : ℤ} {U : Set 𝕜} (hf : MeromorphicNFOn f U) :
    MeromorphicNFOn (f ^ n) U := fun _ hz ↦ (hf hz).zpow

/--
A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is.
-/
/-
**meromorphicNFOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_inv {f : 𝕜 -> 𝕜} : MeromorphicNFOn f⁻¹ U ↔ MeromorphicNFOn
 f U where mp h _ hx
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicNFAt_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {x : 𝕜} {f : 𝕜 → 𝕜}, MeromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is.
-/
theorem meromorphicNFOn_inv {f : 𝕜 → 𝕜} :
    MeromorphicNFOn f⁻¹ U ↔ MeromorphicNFOn f U where
  mp h _ hx := meromorphicNFAt_inv.1 (h hx)
  mpr h _ hx := meromorphicNFAt_inv.2 (h hx)

/--
A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is.
-/
/-
**meromorphicNFOn_fun_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_fun_inv {f : 𝕜 -> 𝕜} : MeromorphicNFOn (fun x => (f x)⁻¹) 
U ↔ MeromorphicNFOn f U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicNFOn_inv`：meromorphicNFOn_inv {f : 𝕜 -> 𝕜} : MeromorphicNFOn 
f⁻¹ U ↔ MeromorphicNFOn f U where mp h _ hx

--- 原说明 ---
A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is.
-/
theorem meromorphicNFOn_fun_inv {f : 𝕜 → 𝕜} :
    MeromorphicNFOn (fun x ↦ (f x)⁻¹) U ↔ MeromorphicNFOn f U :=
  meromorphicNFOn_inv

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_add_const_iff_meromorphicNFOn]
/-
**meromorphicNFOn_comp_add_const_iff_meromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：meromorphicNFOn_comp_add_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} : M
eromorphicNFOn (f ∘ (· + c)) U ↔ MeromorphicNFOn f (U + {c})
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
· 使用定理 `meromorphicNFAt_comp_add_const_iff_meromorphicNFAt`：meromorphicNFAt_comp
_add_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 -> E} : MeromorphicNFAt (f ∘ (· + 
c)) x ↔ MeromorphicNFAt f (x + c)
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
`MeromorphicNFOn` is invariant under translation.
-/
theorem meromorphicNFOn_comp_add_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· + c)) U ↔ MeromorphicNFOn f (U + {c}) := by
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicNFAt_comp_add_const_iff_meromorphicNFAt] using h h₁x
  · rw [meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]
    aesop

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_sub_const_iff_meromorphicNFOn]
/-
**meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} : M
eromorphicNFOn (f ∘ (· - c)) U ↔ MeromorphicNFOn f (U - {c})
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
`MeromorphicNFOn` is invariant under translation.
-/
theorem meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· - c)) U ↔ MeromorphicNFOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicNFOn_ball_fun_comp_sub_const_iff_meromorphicNFOn_ball]
/-
**meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball {c : 𝕜} {R : 
Real} : MeromorphicNFOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicNFOn f (ball 0 R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn`：meromorphicNFOn_comp
_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} : MeromorphicNFOn (f ∘ (· - c
)) U ↔ MeromorphicNFOn f (U - {c})
· 使用定理 `ball_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E] (
δ : ℝ) (x y : E), Metric.ball x δ - {y} = Metric.ball (x - y) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`MeromorphicNFOn` is invariant under translation, special case where the set is 
a ball.
-/
theorem meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicNFOn f (ball 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, ball_sub_singleton, sub_self]

/--
`MeromorphicNFOn` is invariant under translation, special case where the set is a closed ball.
-/
@[to_fun (attr := simp)
  meromorphicNFOn_closedBall_fun_comp_sub_const_iff_meromorphicNFOn_closedBall]
/-
**meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall** 是 M
athlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall {
c : 𝕜} {R : Real} : MeromorphicNFOn (f ∘ (· - c)) (closedBall c R) ↔ Meromorphic
NFOn f (closedBall 0 R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn`：meromorphicNFOn_comp
_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} : MeromorphicNFOn (f ∘ (· - c
)) U ↔ MeromorphicNFOn f (U - {c})
· 使用定理 `closedBall_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGrou
p E] (δ : ℝ) (x y : E),   Metric.closedBall x δ - {y} = Metric.closedBall (x - y
) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicNFOn f (closedBall 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, closedBall_sub_singleton, sub_self]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicNFOn_sphere_fun_comp_sub_const_iff_meromorphicNFOn_sphere]
/-
**meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere {c : 𝕜} {
R : Real} : MeromorphicNFOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicNFOn f (sphe
re 0 R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn`：meromorphicNFOn_comp
_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} : MeromorphicNFOn (f ∘ (· - c
)) U ↔ MeromorphicNFOn f (U - {c})
· 使用定理 `sphere_sub_singleton`：∀ {E : Type u_1} [inst : SeminormedAddCommGroup E]
 (δ : ℝ) (x y : E), Metric.sphere x δ - {y} = Metric.sphere (x - y) δ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`MeromorphicNFOn` is invariant under translation, special case where the set is 
a sphere.
-/
theorem meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicNFOn f (sphere 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, sphere_sub_singleton, sub_self]

/-!
### Continuous extension and conversion to normal form
-/

variable (f U) in
/--
If `f` is meromorphic on `U`, convert `f` to normal form on `U` by changing its
values along a discrete subset within `U`. Otherwise, returns the 0 function.
-/
/-
**toMeromorphicNFOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toMeromorphicNFOn : 𝕜 -> E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is meromorphic on `U`, convert `f` to normal form on `U` by changing its
values along a discrete subset within `U`. Otherwise, returns the 0 function.
-/
noncomputable def toMeromorphicNFOn :
    𝕜 → E := by
  by_cases h₁f : MeromorphicOn f U
  · intro z
    by_cases hz : z ∈ U
    · exact toMeromorphicNFAt f z z
    · exact f z
  · exact 0

/--
If `f` is not meromorphic on `U`, conversion to normal form maps the function
to `0`.
-/
/-
**toMeromorphicNFOn_of_not_meromorphicOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}, ¬
MeromorphicOn f U → toMeromorphicNFOn f U = 0
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
If `f` is not meromorphic on `U`, conversion to normal form maps the function
to `0`.
-/
@[simp] lemma toMeromorphicNFOn_of_not_meromorphicOn (hf : ¬MeromorphicOn f U) :
    toMeromorphicNFOn f U = 0 := by
  simp [toMeromorphicNFOn, hf]

/--
Conversion to normal form on `U` does not change values outside of `U`.
-/
/-
**toMeromorphicNFOn_eq_self_on_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}, M
eromorphicOn f U → Set.EqOn (toMeromorphicNFOn f U) f Uᶜ
参数：toMeromorphicNFOn f U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Conversion to normal form on `U` does not change values outside of `U`.
-/
@[simp] lemma toMeromorphicNFOn_eq_self_on_compl (hf : MeromorphicOn f U) :
    Set.EqOn (toMeromorphicNFOn f U) f Uᶜ := by
  intro x hx
  simp_all [toMeromorphicNFOn]

/--
Conversion to normal form on `U` changes the value only along a discrete subset
of `U`.
-/
/-
**toMeromorphicNFOn_eqOn_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMeromorphicNFOn_eqOn_codiscrete (hf : MeromorphicOn f U) : f =ᶠ[Filter.c
odiscreteWithin U] toMeromorphicNFOn f U
参数：hf : MeromorphicOn f U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toMeromorphicNFAt_eq_self`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {f : 𝕜 → E} …
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Conversion to normal form on `U` changes the value only along a discrete subset
of `U`.
-/
theorem toMeromorphicNFOn_eqOn_codiscrete (hf : MeromorphicOn f U) :
    f =ᶠ[Filter.codiscreteWithin U] toMeromorphicNFOn f U := by
  have : U ∈ Filter.codiscreteWithin U := by simp
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 h₁a.meromorphicNFAt).symm]

/--
If `f` is meromorphic on `U` and `x ∈ U`, then `f` and its conversion to normal
form on `U` agree in a punctured neighborhood of `x`.
-/
/-
**MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (hf : MeromorphicOn f U)
 (hx : x in U) : toMeromorphicNFOn f U =ᶠ[𝓝[!=] x] f
参数：hf : MeromorphicOn f U；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.eventually_analyticAt_or_mem_compl`：eventually_analyticAt_
or_mem_compl (h : MeromorphicOn f U) (hx : x in U) : forallᶠ y in 𝓝[!=] x, Analy
ticAt 𝕜 f y ∨ y in Uᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toMeromorphicNFAt_eq_self`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {f : 𝕜 → E} …
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
If `f` is meromorphic on `U` and `x ∈ U`, then `f` and its conversion to normal
form on `U` agree in a punctured neighborhood of `x`.
-/
theorem MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝[≠] x] f := by
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with a ha
  rcases ha with ha | ha
  · simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt).symm]
  · simp only [Set.mem_compl_iff] at ha
    simp [toMeromorphicNFOn, ha, hf]

/--
If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at `x`
and conversion to normal form on `U` agree in a neighborhood of `x`.
-/
/-
**toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hf : MeromorphicOn f U) (h
x : x in U) : toMeromorphicNFOn f U =ᶠ[𝓝 x] toMeromorphicNFAt f x
参数：hf : MeromorphicOn f U；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`：eventuallyEq_nhds_of_eventuall
yEq_nhdsNE {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g) (h₂ : f a = g a) : f =ᶠ
[𝓝 a] g
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE`：MeromorphicOn.toMerom
orphicNFOn_eq_self_on_nhdsNE (hf : MeromorphicOn f U) (hx : x in U) : toMeromorp
hicNFOn f U =ᶠ[𝓝[!=] x] f
· 使用引理 `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`：MeromorphicAt.eq_nhdsNE_toMer
omorphicNFAt (hf : MeromorphicAt f x) : f =ᶠ[𝓝[!=] x] toMeromorphicNFAt f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at `x`
and conversion to normal form on `U` agree in a neighborhood of `x`.
-/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hf : MeromorphicOn f U)
    (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝 x] toMeromorphicNFAt f x := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx).trans (hf x hx).eq_nhdsNE_toMeromorphicNFAt
  · simp [toMeromorphicNFOn, hf, hx]

/--
If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at `x`
and conversion to normal form on `U` agree at `x`.
-/
/-
**toMeromorphicNFOn_eq_toMeromorphicNFAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMeromorphicNFOn_eq_toMeromorphicNFAt (hf : MeromorphicOn f U) (hx : x in
 U) : toMeromorphicNFOn f U x = toMeromorphicNFAt f x x
参数：hf : MeromorphicOn f U；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds`：toMeromorphicNFOn_eq_toM
eromorphicNFAt_on_nhds (hf : MeromorphicOn f U) (hx : x in U) : toMeromorphicNFO
n f U =ᶠ[𝓝 x] toMeromorphicNFAt f x

--- 原说明 ---
If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at `x`
and conversion to normal form on `U` agree at `x`.
-/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt (hf : MeromorphicOn f U)
    (hx : x ∈ U) :
    toMeromorphicNFOn f U x = toMeromorphicNFAt f x x := by
  apply Filter.EventuallyEq.eq_of_nhds (g := toMeromorphicNFAt f x)
  simp [(toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hx).trans]

variable (f U) in
/--
After conversion to normal form on `U`, the function has normal form.
-/
/-
**meromorphicNFOn_toMeromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：meromorphicNFOn_toMeromorphicNFOn : MeromorphicNFOn (toMeromorphicNFOn f U
) U
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `meromorphicNFAt_congr`：meromorphicNFAt_congr {g : 𝕜 -> E} (hfg : f =ᶠ[𝓝 
x] g) : MeromorphicNFAt f x ↔ MeromorphicNFAt g x
· 使用定理 `toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds`：toMeromorphicNFOn_eq_toM
eromorphicNFAt_on_nhds (hf : MeromorphicOn f U) (hx : x in U) : toMeromorphicNFO
n f U =ᶠ[𝓝 x] toMeromorphicNFAt f x
· 使用定理 `meromorphicNFAt_toMeromorphicNFAt`：meromorphicNFAt_toMeromorphicNFAt : M
eromorphicNFAt (toMeromorphicNFAt f x) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toMeromorphicNFOn_of_not_meromorphicOn`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AnalyticOnNhd.meromorphicNFOn`：AnalyticOnNhd.meromorphicNFOn (h₁f : Anal
yticOnNhd 𝕜 f U) : MeromorphicNFOn f U
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s

--- 原说明 ---
After conversion to normal form on `U`, the function has normal form.
-/
theorem meromorphicNFOn_toMeromorphicNFOn :
    MeromorphicNFOn (toMeromorphicNFOn f U) U := by
  by_cases hf : MeromorphicOn f U
  · intro z hz
    rw [meromorphicNFAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hz)]
    exact meromorphicNFAt_toMeromorphicNFAt
  · simpa [hf] using! analyticOnNhd_const.meromorphicNFOn

/--
If `f` has normal form on `U`, then `f` equals `toMeromorphicNFOn f U`.
-/
/-
**toMeromorphicNFOn_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}, t
oMeromorphicNFOn f U = f ↔ MeromorphicNFOn f U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `meromorphicNFOn_toMeromorphicNFOn`：meromorphicNFOn_toMeromorphicNFOn : M
eromorphicNFOn (toMeromorphicNFOn f U) U
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toMeromorphicNFAt_eq_self`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {f : 𝕜 → E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` has normal form on `U`, then `f` equals `toMeromorphicNFOn f U`.
-/
@[simp] theorem toMeromorphicNFOn_eq_self :
    toMeromorphicNFOn f U = f ↔ MeromorphicNFOn f U := by
  constructor <;> intro h
  · rw [h.symm]
    apply meromorphicNFOn_toMeromorphicNFOn
  · ext x
    by_cases hx : x ∈ U
    · simp only [toMeromorphicNFOn, h.meromorphicOn, ↓reduceDIte, hx]
      rw [toMeromorphicNFAt_eq_self.2 (h hx)]
    · simp [toMeromorphicNFOn, h.meromorphicOn, hx]

/--
Conversion of normal form does not affect orders.
-/
/-
**meromorphicOrderAt_toMeromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜} {U : S
et 𝕜},   MeromorphicOn f U → x ∈ U → meromorphicOrderAt (toMeromorphicNFOn f U) 
x = meromorphicOrderAt f x
参数：toMeromorphicNFOn f U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meromorphicOrderAt_congr`：meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[!=] x
] f₂) : meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x
· 使用定理 `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE`：MeromorphicOn.toMerom
orphicNFOn_eq_self_on_nhdsNE (hf : MeromorphicOn f U) (hx : x in U) : toMeromorp
hicNFOn f U =ᶠ[𝓝[!=] x] f

--- 原说明 ---
Conversion of normal form does not affect orders.
-/
@[simp] theorem meromorphicOrderAt_toMeromorphicNFOn (hf : MeromorphicOn f U) (hx : x ∈ U) :
    meromorphicOrderAt (toMeromorphicNFOn f U) x = meromorphicOrderAt f x := by
  apply meromorphicOrderAt_congr
  exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx

/--
Conversion of normal form does not affect divisors.
-/
/-
**MeromorphicOn.divisor_of_toMeromorphicNFOn** 是 Mathlib 中的一个定理，位于命名空间 `Meromorp
hicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜},  
 MeromorphicOn f U → MeromorphicOn.divisor (toMeromorphicNFOn f U) U = Meromorph
icOn.divisor f U
参数：toMeromorphicNFOn f U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用定理 `meromorphicNFOn_toMeromorphicNFOn`：meromorphicNFOn_toMeromorphicNFOn : M
eromorphicNFOn (toMeromorphicNFOn f U) U
· 使用定理 `meromorphicOrderAt_toMeromorphicNFOn`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.locallyFinsuppWithin.apply_eq_zero_of_notMem`：apply_eq_zero_of_
notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Conversion of normal form does not affect divisors.
-/
@[simp] theorem MeromorphicOn.divisor_of_toMeromorphicNFOn (hf : MeromorphicOn f U) :
    divisor (toMeromorphicNFOn f U) U = divisor f U := by
  ext z
  by_cases hz : z ∈ U <;> simp [hf, (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn, hz]
