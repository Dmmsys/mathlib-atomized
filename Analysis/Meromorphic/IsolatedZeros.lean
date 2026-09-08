/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Principles of Isolated Zeros and Identity Principles for Meromorphic Functions

In line with results in `Mathlib.Analysis.Analytic.IsolatedZeros` and
`Mathlib.Analysis.Analytic.Uniqueness`, this file establishes principles of isolated zeros and
identity principles for meromorphic functions.

Compared to the results for analytic functions, the principles established here are a little more
complicated to state. This is because meromorphic functions can be modified at will along discrete
subsets and still remain meromorphic.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 → E}

open Filter Topology

namespace MeromorphicAt

/-!
## Principles of Isolated Zeros
-/

/--
The principle of isolated zeros: If `f` is meromorphic at `x`, then `f` vanishes eventually in a
punctured neighborhood of `x` iff it vanishes frequently in punctured neighborhoods.

See `AnalyticAt.frequently_zero_iff_eventually_zero` for a stronger result in the analytic case.
-/
/-
**MeromorphicAt.frequently_zero_iff_eventuallyEq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MeromorphicAt`。
形式化陈述：frequently_zero_iff_eventuallyEq_zero (hf : MeromorphicAt f x) : (existsᶠ 
z in 𝓝[!=] x, f z = 0) ↔ f =ᶠ[𝓝[!=] x] 0
参数：hf : MeromorphicAt f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`：MeromorphicAt.ev
entually_eq_zero_or_eventually_ne_zero {f : 𝕜 -> E} {z₀ : 𝕜} (hf : MeromorphicAt
 f z₀) : (forallᶠ z in 𝓝[!=] z₀, f z = 0) ∨ …
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜

--- 原说明 ---
The principle of isolated zeros: If `f` is meromorphic at `x`, then `f` vanishes
 eventually in a
punctured neighborhood of `x` iff it vanishes frequently in punctured neighborho
ods.

See `AnalyticAt.frequently_zero_iff_eventually_zero` for a stronger result in th
e analytic case.
-/
theorem frequently_zero_iff_eventuallyEq_zero (hf : MeromorphicAt f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ f =ᶠ[𝓝[≠] x] 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h ↦ h.frequently⟩

/--
Variant of the principle of isolated zeros: Let `U` be a subset of `𝕜` and assume that `x ∈ U` is
not an isolated point of `U`. If a function `f` is meromorphic at `x` and vanishes along a subset
that is codiscrete within `U`, then `f` vanishes in a punctured neighbourhood of `f`.

For a typical application, let `U` be a path in the complex plane and let `x` be one of the end
points. If `f` is meromorphic at `x` and vanishes on `U`, then it will vanish in a punctured
neighbourhood of `x`, which intersects `U` non-trivially but is not contained in `U`.

The assumption that `x` is not an isolated point of `U` is expressed as `AccPt x (𝓟 U)`. See
`accPt_iff_frequently` and `accPt_iff_frequently_nhdsNE` for useful reformulations.
-/
/-
**MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin**
 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin (hf : Merom
orphicAt f x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U]
 0) : f =ᶠ[𝓝[!=] x] 0
参数：hf : MeromorphicAt f x；h₁x : x in U；h₂x : AccPt x (𝓟 U)；h : f =ᶠ[codiscreteWi
thin U] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero`：frequently_zero_iff
_eventuallyEq_zero (hf : MeromorphicAt f x) : (existsᶠ z in 𝓝[!=] x, f z = 0) ↔ 
f =ᶠ[𝓝[!=] x] 0
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `accPt_iff_frequently_nhdsNE`：accPt_iff_frequently_nhdsNE {X : Type*} [To
pologicalSpace X] {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ existsᶠ (y : X) in 𝓝[!=]
 x, y in C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_mem_set`：eventually_mem_set {s : Set α} {l : Filter α}
 : (forallᶠ x in l, x in s) ↔ s in l
· 使用定理 `mem_codiscreteWithin_iff_forall_mem_nhdsNE`：mem_codiscreteWithin_iff_for
all_mem_nhdsNE {S T : Set X} : S in codiscreteWithin T ↔ forall x in T, S union 
Tᶜ in 𝓝[!=] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Variant of the principle of isolated zeros: Let `U` be a subset of `𝕜` and assum
e that `x ∈ U` is
not an isolated point of `U`. If a function `f` is meromorphic at `x` and vanish
es along a subset
that is codiscrete within `U`, then `f` vanishes in a punctured neighbourhood of
 `f`.

For a typical application, let `U` be a path in the complex plane and let `x` be
 one of the end
points. If `f` is meromorphic at `x` and vanishes on `U`, then it will vanish in
 a punctured
neighbourhood of `x`, which intersects `U` non-trivially but is not contained in
 `U`.

The assumption that `x` is not an isolated point of `U` is expressed as `AccPt x
 (𝓟 U)`. See
`accPt_iff_frequently` and `accPt_iff_frequently_nhdsNE` for useful reformulatio
ns.
-/
theorem eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin (hf : MeromorphicAt f x)
    (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] 0) :
    f =ᶠ[𝓝[≠] x] 0 := by
  rw [← hf.frequently_zero_iff_eventuallyEq_zero]
  apply ((accPt_iff_frequently_nhdsNE.1 h₂x).and_eventually <| eventually_mem_set.2
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x h₁x)).mono
  simp +contextual

/--
Variant of the principle of isolated zeros, formulated in terms of orders: If `f` is nowhere locally
constant zero, then its zero set is discrete within its domain of meromorphicity.
-/
/-
**MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero** 是 Mathlib 中的一
个定理，位于命名空间 `MeromorphicAt.MeromorphicOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {U : Set 𝕜} {f : 𝕜 → E},  
 MeromorphicOn f U → (∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) → ∀ᶠ (x : 𝕜) in Filte
r.codiscreteWithin U, f x ≠ 0
参数：∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤；x : 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_t
op`：codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top (h₁f : Meromorp
hicOn f U) (h₂f : forall u in U, meromorphicOrderAt f u != ⊤) : …
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `AnalyticAt.meromorphicOrderAt_eq`：AnalyticAt.meromorphicOrderAt_eq (hf :
 AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of the principle of isolated zeros, formulated in terms of orders: If `f
` is nowhere locally
constant zero, then its zero set is discrete within its domain of meromorphicity
.
-/
theorem MeromorphicOn.codiscreteWithin_setOfPred_ne_zero (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) :
    ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  filter_upwards [h₁f.analyticAt_mem_codiscreteWithin,
    h₁f.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top h₂f] with x h₁x h₂x
  have := h₂f x h₂x.1
  simp_all [← h₁x.analyticOrderAt_eq_zero, h₁x.meromorphicOrderAt_eq]

@[deprecated (since := "2026-07-09")]
alias MeromorphicOn.codiscreteWithin_setOf_ne_zero :=
  MeromorphicOn.codiscreteWithin_setOfPred_ne_zero

/-!
## Identity Principles
-/

/--
Formulation of `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero` as an identity principle: If
`f` and `g` are meromorphic at `x`, then `f` and `g` agree eventually in a punctured neighborhood of
`x` iff they agree at points arbitrarily close to (but different from) `x`.
-/
/-
**MeromorphicAt.frequently_eq_iff_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Meromo
rphicAt`。
形式化陈述：frequently_eq_iff_eventuallyEq (hf : MeromorphicAt f x) (hg : MeromorphicA
t g x) : (existsᶠ z in 𝓝[!=] x, f z = g z) ↔ f =ᶠ[𝓝[!=] x] g
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_iff_sub`：eventuallyEq_iff_sub [AddGroup β] {f g : α 
-> β} {l : Filter α} : f =ᶠ[l] g ↔ f - g =ᶠ[l] 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero`：frequently_zero_iff
_eventuallyEq_zero (hf : MeromorphicAt f x) : (existsᶠ z in 𝓝[!=] x, f z = 0) ↔ 
f =ᶠ[𝓝[!=] x] 0
· 使用引理 `MeromorphicAt.sub`：sub {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f - g) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Formulation of `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero` as an ident
ity principle: If
`f` and `g` are meromorphic at `x`, then `f` and `g` agree eventually in a punct
ured neighborhood of
`x` iff they agree at points arbitrarily close to (but different from) `x`.
-/
theorem frequently_eq_iff_eventuallyEq (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (∃ᶠ z in 𝓝[≠] x, f z = g z) ↔ f =ᶠ[𝓝[≠] x] g := by
  rw [eventuallyEq_iff_sub, ← (hf.sub hg).frequently_zero_iff_eventuallyEq_zero]
  simp_rw [Pi.sub_apply, sub_eq_zero]

/--
Formulation of `MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin` as an
identity principle: Let `U` be a subset of `𝕜` and assume that `x ∈ U` is not an isolated point of
`U`. If function `f` and `g` are meromorphic at `x` and agree along a subset that is codiscrete
within `U`, then `f` and `g` agree in a punctured neighbourhood of `f`.
-/
/-
**MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin** 是 Mathlib
 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f
 x) (hg : MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codi
screteWithin U] g) : f =ᶠ[𝓝[!=] x] g
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x；h₁x : x in U；h₂x : AccPt x (𝓟 U
)；h : f =ᶠ[codiscreteWithin U] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_iff_sub`：eventuallyEq_iff_sub [AddGroup β] {f g : α 
-> β} {l : Filter α} : f =ᶠ[l] g ↔ f - g =ᶠ[l] 0
· 使用定理 `MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWi
thin`：eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin (hf : Merom
orphicAt f x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codis…
· 使用引理 `MeromorphicAt.sub`：sub {f g : 𝕜 -> E} (hf : MeromorphicAt f x) (hg : Mer
omorphicAt g x) : MeromorphicAt (f - g) x

--- 原说明 ---
Formulation of `MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codi
screteWithin` as an
identity principle: Let `U` be a subset of `𝕜` and assume that `x ∈ U` is not an
 isolated point of
`U`. If function `f` and `g` are meromorphic at `x` and agree along a subset tha
t is codiscrete
within `U`, then `f` and `g` agree in a punctured neighbourhood of `f`.
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g := by
  rw [eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h

/-
Variant of `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`, as a statement
about meromorphic functions that agree outside a set codiscrete within a perfect set.
-/
/-
**MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect*
* 是 Mathlib 中的一个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf : Mero
morphicAt f x) (hg : MeromorphicAt g x) (hx : x in U) (hU : Preperfect U) (h : f
 =ᶠ[codiscreteWithin U] g) : f =ᶠ[𝓝[!=] x] g
参数：hf : MeromorphicAt f x；hg : MeromorphicAt g x；hx : x in U；hU : Preperfect U；h
 : f =ᶠ[codiscreteWithin U] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`：even
tuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x) (hg : 
MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) …

--- 原说明 ---
Variant of `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`,
 as a statement
about meromorphic functions that agree outside a set codiscrete within a perfect
 set.
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (hx : x ∈ U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g :=
  hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hg hx (hU x hx) h

/-
Variant of `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`, as a statement
about meromorphic functions agreeing in a neighborhood of a preperfect set.
-/
/-
**MeromorphicAt.eventually_nhdsSet_eventuallyEq_codiscreteWithin** 是 Mathlib 中的一
个定理，位于命名空间 `MeromorphicAt`。
形式化陈述：eventually_nhdsSet_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U) 
(hg : MeromorphicOn g U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) : 
forallᶠ x in 𝓝ˢ U, f =ᶠ[𝓝[!=] x] g
参数：hf : MeromorphicOn f U；hg : MeromorphicOn g U；hU : Preperfect U；h : f =ᶠ[codi
screteWithin U] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsSet_iff_exists`：eventually_nhdsSet_iff_exists {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ exists t, IsOpen t ∧ s subseteq t ∧ forall x, 
x in t -> p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `isOpen_setOfPred_eventually_nhdsWithin`：isOpen_setOfPred_eventually_nhds
Within [T1Space X] {p : X -> Prop} : IsOpen { x | forallᶠ y in 𝓝[!=] x, p y }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`：even
tuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x) (hg : 
MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) …

--- 原说明 ---
Variant of `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`,
 as a statement
about meromorphic functions agreeing in a neighborhood of a preperfect set.
-/
theorem eventually_nhdsSet_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) :
    ∀ᶠ x in 𝓝ˢ U, f =ᶠ[𝓝[≠] x] g := by
  rw [eventually_nhdsSet_iff_exists]
  use {x | f =ᶠ[𝓝[≠] x] g}
  simp only [Set.mem_ofPred_eq, imp_self, implies_true, and_true]
  constructor
  · apply isOpen_setOfPred_eventually_nhdsWithin
  · intro x hx
    rw [Set.mem_ofPred]
    exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf x hx) (hg x hx) hx (hU x hx) h

end MeromorphicAt

/-- If meromorphic `f` and `g` agree on `codiscreteWithin U`, so do their derivatives. -/
/-
**MeromorphicOn.deriv_eventuallyEq_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：MeromorphicOn.deriv_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U)
 (hg : MeromorphicOn g U) (h : f =ᶠ[codiscreteWithin U] g) : deriv f =ᶠ[codiscre
teWithin U] deriv g
参数：hf : MeromorphicOn f U；hg : MeromorphicOn g U；h : f =ᶠ[codiscreteWithin U] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `mem_codiscreteWithin_iff_forall_mem_nhdsNE`：mem_codiscreteWithin_iff_for
all_mem_nhdsNE {S T : Set X} : S in codiscreteWithin T ↔ forall x in T, S union 
Tᶜ in 𝓝[!=] x
· 使用定理 `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`：even
tuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x) (hg : 
MeromorphicAt g x) (h₁x : x in U) (h₂x : AccPt x (𝓟 U)) …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.EventuallyEq.nhdsNE_deriv`：Filter.EventuallyEq.nhdsNE_deriv (h : 
f₁ =ᶠ[𝓝[!=] x] f) : deriv f₁ =ᶠ[𝓝[!=] x] deriv f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.not_frequently`：not_frequently {p : α -> Prop} {f : Filter α} : (
¬existsᶠ x in f, p x) ↔ forallᶠ x in f, ¬p x
· 使用定理 `accPt_iff_frequently_nhdsNE`：accPt_iff_frequently_nhdsNE {X : Type*} [To
pologicalSpace X] {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ existsᶠ (y : X) in 𝓝[!=]
 x, y in C

--- 原说明 ---
If meromorphic `f` and `g` agree on `codiscreteWithin U`, so do their derivative
s.
-/
theorem MeromorphicOn.deriv_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U) (h : f =ᶠ[codiscreteWithin U] g) :
    deriv f =ᶠ[codiscreteWithin U] deriv g := by
  rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  by_cases hacc : AccPt x (𝓟 U)
  · have h : f =ᶠ[𝓝[≠] x] g :=
      (hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hg x hx) hx hacc h
    filter_upwards [h.nhdsNE_deriv] using by simp +contextual
  · rw [accPt_iff_frequently_nhdsNE, not_frequently] at hacc
    filter_upwards [hacc] using by grind
