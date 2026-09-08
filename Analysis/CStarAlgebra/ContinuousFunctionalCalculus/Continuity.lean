/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Continuity of the continuous functional calculus in each variable

The continuous functional calculus is a map which takes a pair `a : A` (`A` is a C⋆-algebra) and
a function `f : C(spectrum R a, R)` where `a` satisfies some predicate `p`, depending on `R` and
returns another element of the algebra `A`. This is the map `cfcHom`. The class
`ContinuousFunctionalCalculus` declares that `cfcHom` is a continuous map from `C(spectrum R a, R)`
to `A`. However, users generally interact with the continuous functional calculus through `cfc`,
which operates on bare functions `f : R → R` instead and takes a junk value when `f` is not
continuous on the spectrum of `a`.  In this file we provide some lemma concerning the continuity
of `cfc`, subject to natural hypotheses.

However, the continuous functional calculus is *also* continuous in the variable `a`, but there
are some conditions that must be satisfied. In particular, given a function `f : R → R` the map
`a ↦ cfc f a` is continuous so long as `a` varies over a collection of elements satisfying the
predicate `p` and their spectra are collectively contained in a compact set on which `f` is
continuous. Moreover, it is required that the continuous functional calculus be the isometric
variant.

Under the assumption of `IsometricContinuousFunctionalCalculus`, we show that the continuous
functional calculus is Lipschitz with constant 1 in the variable `f : R →ᵤ[{spectrum R a}] R`
on the set of functions which are continuous on the spectrum of `a`. Combining this with the
continuity of the continuous functional calculus in the variable `a`, we obtain a joint continuity
result for `cfc` in both variables.

Finally, all of this is developed for both the unital and non-unital functional calculi.
The continuity results in the function variable are valid for all scalar rings, but the continuity
results in the variable `a` come in two flavors: those for `RCLike 𝕜` and those for `ℝ≥0`.

## Main results


+ `tendsto_cfc_fun`: If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and
  all these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
  to `cfc f a`.
+ `Filter.Tendsto.cfc`: If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` tends to
  `a₀ : A` along a filter `l` (such that eventually `a x` satisfies the predicate `p` associated to
  `𝕜` and has spectrum contained in `s`, as does `a₀`), then `fun x ↦ cfc f (a x)` tends to
  `cfc f a₀`.
+ `lipschitzOnWith_cfc_fun`: The function `f ↦ cfc f a` is Lipschitz with constant with constant 1
  with respect to supremum metric (on `R →ᵤ[{spectrum R a}] R`) on those functions which are
  continuous on the spectrum.
+ `continuousOn_cfc`: For `f : 𝕜 → 𝕜` continuous on a compact set `s`, `cfc f` is continuous on the
  set of `a : A` satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-spectrum is
  contained in `s`.
+ `continuousOn_cfc_setProd`: Let `s : Set 𝕜` be a compact set and consider pairs
  `(f, a) : (𝕜 → 𝕜) × A` where `f` is continuous on `s` and `spectrum 𝕜 a ⊆ s` and `a` satisfies
  the predicate `p a` for the continuous functional calculus. Then `cfc` is jointly continuous in
  both variables (i.e., continuous in its uncurried form) on this set of pairs when the function
  space is equipped with the topology of uniform convergence on `s`.
+ Versions of all of the above for non-unital algebras, and versions over `ℝ≥0` as well.

-/

public section

open scoped UniformConvergence NNReal
open Filter Topology

section Unital

section Left

section Generic

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
to `cfc f a`. -/
/-
**tendsto_cfc_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_cfc_fun {l : Filter X} {F : X -> R -> R} {f : R -> R} {a : A} (h_t
endsto : TendstoUniformlyOn F f l (spectrum R a)) (hF : forallᶠ x in l, Continuo
usOn (F x) (spectrum R a)) : Tendsto (fun x => cfc (F x) a) l (𝓝 (cfc f a))
参数：h_tendsto : TendstoUniformlyOn F f l (spectrum R a)；hF : forallᶠ x in l, Cont
inuousOn (F x) (spectrum R a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TendstoUniformlyOn.continuousOn`：∀ {α : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → α → β}   
{f : α → β} {s : Set …
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_comap'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α},   Set.range i ∈ f → (Fi
lter.Tendsto (m…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用定理 `ContinuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn`：∀ {α : Type u₁}
 {β : Type u₂} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {s : Set α}
 [CompactSpace ↑s]   {f : α → β} (hf : Contin…
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Peel.eventually_imp`：eventually_imp {α : Type*} {p q : α 
-> Prop} {f : Filter α} (hq : forall (x : α), p x -> q x) (hp : forallᶠ (x : α) 
in f, p x) : forallᶠ (x …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and al
l
these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
to `cfc f a`.
-/
theorem tendsto_cfc_fun {l : Filter X} {F : X → R → R} {f : R → R} {a : A}
    (h_tendsto : TendstoUniformlyOn F f l (spectrum R a))
    (hF : ∀ᶠ x in l, ContinuousOn (F x) (spectrum R a)) :
    Tendsto (fun x ↦ cfc (F x) a) l (𝓝 (cfc f a)) := by
  open scoped ContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (spectrum R a)}
    rw [← tendsto_comap'_iff (i := ((↑) : s → X)) (by simpa)]
    conv =>
      enter [1, x]
      rw [Function.comp_apply, cfc_apply (hf := x.2)]
    rw [cfc_apply ..]
    apply cfcHom_continuous _ |>.tendsto _ |>.comp
    rw [hf.tendsto_domRestrict_iff_tendstoUniformlyOn Subtype.property]
    intro t
    simp only [eventually_comap, Subtype.forall]
    peel h_tendsto t with ht x _
    simp_all
  · simpa [cfc_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` is
continuous at `x₀`. -/
/-
**continuousAt_cfc_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_cfc_fun [TopologicalSpace X] {f : X -> R -> R} {a : A} {x₀ : 
X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a)) (hf : forallᶠ
 x in 𝓝 x₀, ContinuousOn (f x) (spectrum R a)) : ContinuousAt (fun x => cfc (f x
) a) x₀
参数：h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a)；hf : forallᶠ x 
in 𝓝 x₀, ContinuousOn (f x) (spectrum R a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_cfc_fun`：tendsto_cfc_fun {l : Filter X} {F : X -> R -> R} {f : R
 -> R} {a : A} (h_tendsto : TendstoUniformlyOn F f l (spectrum R a)) (hF : foral
lᶠ x …

--- 原说明 ---
If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `
a`,
and each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` 
is
continuous at `x₀`.
-/
theorem continuousAt_cfc_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a))
    (hf : ∀ᶠ x in 𝓝 x₀, ContinuousOn (f x) (spectrum R a)) :
    ContinuousAt (fun x ↦ cfc (f x) a) x₀ :=
  tendsto_cfc_fun h_tendsto hf

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝[s] x₀`) on the spectrum of `a`,
and eventually each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` is
continuous at `x₀` within `s`. -/
/-
**continuousWithinAt_cfc_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_cfc_fun [TopologicalSpace X] {f : X -> R -> R} {a : A} 
{x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (spectru
m R a)) (hf : forallᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (spectrum R a)) : Continu
ousWithinAt (fun x => cfc (f x) a) s x₀
参数：h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (spectrum R a)；hf : forallᶠ
 x in 𝓝[s] x₀, ContinuousOn (f x) (spectrum R a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_cfc_fun`：tendsto_cfc_fun {l : Filter X} {F : X -> R -> R} {f : R
 -> R} {a : A} (h_tendsto : TendstoUniformlyOn F f l (spectrum R a)) (hF : foral
lᶠ x …

--- 原说明 ---
If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝[s] x₀`) on the spectrum o
f `a`,
and eventually each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cf
c (f x) a` is
continuous at `x₀` within `s`.
-/
theorem continuousWithinAt_cfc_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (spectrum R a))
    (hf : ∀ᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (spectrum R a)) :
    ContinuousWithinAt (fun x ↦ cfc (f x) a) s x₀ :=
  tendsto_cfc_fun h_tendsto hf

open UniformOnFun in
/-- If `f : X → R → R` is continuous on `s : Set X` in the topology on
`X → R →ᵤ[{spectrum R a}] → R`, and each `f` is continuous on the spectrum, then `x ↦ cfc (f x) a`
is continuous on `s` also. -/
/-
**ContinuousOn.cfc_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cfc_fun [TopologicalSpace X] {f : X -> R -> R} {a : A} {s : S
et X} (h_cont : ContinuousOn (fun x => ofFun {spectrum R a} (f x)) s) (hf : fora
ll x in s, ContinuousOn (f x) (spectrum R a)
参数：h_cont : ContinuousOn (fun x => ofFun {spectrum R a} (f x)) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `continuousWithinAt_cfc_fun`：continuousWithinAt_cfc_fun [TopologicalSpace
 X] {f : X -> R -> R} {a : A} {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformly
On f (f x₀) (𝓝[s…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : X → R → R` is continuous on `s : Set X` in the topology on
`X → R →ᵤ[{spectrum R a}] → R`, and each `f` is continuous on the spectrum, then
 `x ↦ cfc (f x) a`
is continuous on `s` also.
-/
theorem ContinuousOn.cfc_fun [TopologicalSpace X] {f : X → R → R} {a : A} {s : Set X}
    (h_cont : ContinuousOn (fun x ↦ ofFun {spectrum R a} (f x)) s)
    (hf : ∀ x ∈ s, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc (f x) a) s := by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx ↦ continuousWithinAt_cfc_fun (h_cont x hx) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hf x hx

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum, then `x ↦ cfc (f x) a` is continuous. -/
/-
**Continuous.cfc_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cfc_fun [TopologicalSpace X] (f : X -> R -> R) (a : A) (h_cont 
: Continuous (fun x => ofFun {spectrum R a} (f x))) (hf : forall x, ContinuousOn
 (f x) (spectrum R a)
参数：f : X -> R -> R；a : A；h_cont : Continuous (fun x => ofFun {spectrum R a} (f x
))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc_fun`：ContinuousOn.cfc_fun [TopologicalSpace X] {f : X -
> R -> R} {a : A} {s : Set X} (h_cont : ContinuousOn (fun x => ofFun {spectrum R
 a} (f x))…

--- 原说明 ---
If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → 
R`,
and each `f` is continuous on the spectrum, then `x ↦ cfc (f x) a` is continuous
.
-/
theorem Continuous.cfc_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {spectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    Continuous fun x ↦ cfc (f x) a := by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfc_fun (fun x _ ↦ hf x)

end Generic

section Isometric

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [MetricSpace A] [Algebra R A] [IsometricContinuousFunctionalCalculus R A p]

variable (R) in
open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/-- The function `f ↦ cfc f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{spectrum R a}] R`) on those functions which are continuous on
the spectrum. -/
/-
**lipschitzOnWith_cfc_fun** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_cfc_fun (a : A) : LipschitzOnWith 1 (fun f => cfc (toFun {
spectrum R a} f) a) {f | ContinuousOn (toFun {spectrum R a} f) (spectrum R a)}
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用引理 `isometry_cfcHom`：isometry_cfcHom (a : A) (ha : p a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `UniformOnFun.edist_continuousRestrict_of_singleton`：edist_continuousRest
rict_of_singleton [TopologicalSpace α] {s : Set α} {f g : α ->ᵤ[{s}] β} [Compact
Space s] (hf : ContinuousOn (toFun {s} f…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
· 使用定理 `LipschitzWith.const'`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] (b : β) {K : NNReal},   LipschitzWith K 
fun x => b

--- 原说明 ---
The function `f ↦ cfc f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{spectrum R a}] R`) on those functions which are conti
nuous on
the spectrum.
-/
lemma lipschitzOnWith_cfc_fun (a : A) :
    LipschitzOnWith 1 (fun f ↦ cfc (toFun {spectrum R a} f) a)
      {f | ContinuousOn (toFun {spectrum R a} f) (spectrum R a)} := by
  by_cases ha : p a
  · intro f hf g hg
    simp only
    rw [cfc_apply .., cfc_apply .., isometry_cfcHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [edist_continuousRestrict_of_singleton hf hg]
  · simpa [cfc_apply_of_not_predicate a ha] using LipschitzWith.const' 0 |>.lipschitzOnWith

open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/-- The function `f ↦ cfc f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{s}] R`) on those functions which are continuous on a set `s` containing
the spectrum. -/
/-
**lipschitzOnWith_cfc_fun_of_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_cfc_fun_of_subset (a : A) {s : Set R} (hs : spectrum R a s
ubseteq s) : LipschitzOnWith 1 (fun f => cfc (toFun {s} f) a) {f | ContinuousOn 
(toFun {s} f) (s)}
参数：a : A；hs : spectrum R a subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `lipschitzOnWith_cfc_fun`：lipschitzOnWith_cfc_fun (a : A) : LipschitzOnWi
th 1 (fun f => cfc (toFun {spectrum R a} f) a) {f | ContinuousOn (toFun {spectru
m R a} f) (sp…
· 使用引理 `UniformOnFun.lipschitzWith_one_ofFun_toFun'`：lipschitzWith_one_ofFun_toF
un' [Finite 𝔗] (h : ⋃₀ 𝔖 subseteq ⋃₀ 𝔗) : LipschitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (
α ->ᵤ[𝔗] β) -> (α ->ᵤ[𝔖] β))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LipschitzOnWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : P
seudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSp
ace γ] {K …
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t

--- 原说明 ---
The function `f ↦ cfc f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{s}] R`) on those functions which are continuous on a 
set `s` containing
the spectrum.
-/
lemma lipschitzOnWith_cfc_fun_of_subset (a : A) {s : Set R} (hs : spectrum R a ⊆ s) :
    LipschitzOnWith 1 (fun f ↦ cfc (toFun {s} f) a)
      {f | ContinuousOn (toFun {s} f) (s)} := by
  have h₁ := lipschitzOnWith_cfc_fun R a
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {spectrum R a}) (𝔗 := {s}) (β := R) (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s)})
  simpa using! h₁.comp h₃ (fun f hf ↦ hf.mono hs)

end Isometric

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    [ContinuousStar A]

/-- `cfcHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`. -/
/-
**continuous_cfcHomSuperset_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_cfcHomSuperset_left [TopologicalSpace X] {s : Set 𝕜} (hs : IsCo
mpact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont : Continuous a) (ha : forall x, spe
ctrum 𝕜 (a x) subseteq s) (ha' : forall x, p (a x)
参数：hs : IsCompact s；f : C(s, 𝕜)；a : X -> A；ha_cont : Continuous a；ha : forall x,
 spectrum 𝕜 (a x) subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `ContinuousMap.induction_on_of_compact`：ContinuousMap.induction_on_of_com
pact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s] {p : C(s, 𝕜) -> Prop} (
const : forall r, p (.const…
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用引理 `cfcHomSuperset_id`：cfcHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs 
: spectrum R a subseteq s) : cfcHomSuperset ha hs (.restrict s <| .id R) = a
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `Continuous.star`：Continuous.star (hf : Continuous f) : Continuous fun x 
=> star (f x)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
`cfcHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compa
ct and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy th
e predicate `p`.
-/
theorem continuous_cfcHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜))
    (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcHomSuperset (ha' x) (ha x) f) := by
  open scoped ContinuousFunctionalCalculus in
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.commutes] using! continuous_const
  | id =>
    simp only [cfcHomSuperset_id]
    fun_prop
  | star_id =>
    simp only [map_star, cfcHomSuperset_id]
    fun_prop
  | add f g hf hg => simpa using! hf.add hg
  | mul f g hf hg => simpa using! hf.mul hg
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_ofPred_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcHomSuperset_apply]
    rw [isometry_cfcHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcHom (ha' x)))]
    rw [ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

variable (A) in
/-- For `f : 𝕜 → 𝕜` continuous on a compact set `s`, `cfc f` is continuous on the set of `a : A`
satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-spectrum is contained in `s`. -/
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
For `f : 𝕜 → 𝕜` continuous on a compact set `s`, `cfc f` is continuous on the se
t of `a : A`
satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-spectrum is conta
ined in `s`.
-/
theorem continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a | p a ∧ spectrum 𝕜 a ⊆ s} :=
  continuousOn_iff_continuous_domRestrict.mpr <| by
    convert!
      continuous_cfcHomSuperset_left hs ⟨_, hf.domRestrict⟩
        ((↑) : {a | p a ∧ spectrum 𝕜 a ⊆ s} → A)
        continuous_subtype_val (fun x ↦ x.2.2) with
      x
    rw [cfcHomSuperset_apply, Set.domRestrict_apply, cfc_apply _ _ x.2.1 (hf.mono x.2.2)]
    congr!

open UniformOnFun in
/-- Let `s : Set 𝕜` be a compact set and consider pairs `(f, a) : (𝕜 → 𝕜) × A` where `f` is
continuous on `s` and `spectrum 𝕜 a ⊆ s` and `a` satisfies the predicate `p a` for the continuous
functional calculus.

Then `cfc` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
/-
**continuousOn_cfc_setProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc_setProd {s : Set 𝕜} (hs : IsCompact s) : ContinuousOn (fu
n fa : (𝕜 ->ᵤ[{s}] 𝕜) × A => cfc (toFun {s} fa.1) fa.2) ({f | ContinuousOn (toFu
n {s} f) s} ×ˢ {a | p a ∧ spectrum 𝕜 a subseteq s})
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith`：continuousOn_prod_of_
continuousOn_lipschitzOnWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) {s : S…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_cfc`：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜
 -> 𝕜) (hf : ContinuousOn f s
· 使用引理 `lipschitzOnWith_cfc_fun_of_subset`：lipschitzOnWith_cfc_fun_of_subset (a 
: A) {s : Set R} (hs : spectrum R a subseteq s) : LipschitzOnWith 1 (fun f => cf
c (toFun {s} f) a) {f |…

--- 原说明 ---
Let `s : Set 𝕜` be a compact set and consider pairs `(f, a) : (𝕜 → 𝕜) × A` where
 `f` is
continuous on `s` and `spectrum 𝕜 a ⊆ s` and `a` satisfies the predicate `p a` f
or the continuous
functional calculus.

Then `cfc` is jointly continuous in both variables (i.e., continuous in its uncu
rried form) on this
set of pairs when the function space is equipped with the topology of uniform co
nvergence on `s`.
-/
theorem continuousOn_cfc_setProd {s : Set 𝕜} (hs : IsCompact s) :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{s}] 𝕜) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | p a ∧ spectrum 𝕜 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfc A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfc_fun_of_subset a ha')

open UniformOnFun in
/-
**continuousOn_cfc_setProd_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} : Continuou
sOn (fun fa : (𝕜 ->ᵤ[{t | IsCompact t ∧ t subseteq s}] 𝕜) × A => cfc (toFun {s} 
fa.1) fa.2) ({f | ContinuousOn (toFun {t | IsCompact t ∧ t subseteq s} f) s} ×ˢ 
{a | p a ∧ s in 𝓝ˢ (spectrum 𝕜 a)})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `continuousOn_of_locally_continuousOn`：continuousOn_of_locally_continuous
On (h : forall x in s, exists t, IsOpen t ∧ x in t ∧ ContinuousOn f (s inter t))
 : ContinuousOn f s
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `ContinuousFunctionalCalculus.isCompact_spectrum`：ContinuousFunctionalCal
culus.isCompact_spectrum (a : A) : IsCompact (spectrum R a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_isCompact`：IsCompact.nhdsSet_basis_isCompact [Lo
callyCompactSpace X] {K : Set X} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun L => 
L in 𝓝ˢ K ∧ IsCompact L…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Semicontinuous.isOpen`：Semicontinuous.isOpen (h : Semicontinuous r) (b :
 β) : IsOpen {x | r x b}
· 使用引理 `upperHemicontinuous_spectrum`：upperHemicontinuous_spectrum [NormedField 
𝕜] [ProperSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] : UpperH
emicontinuous (spe…
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousOn.comp'`：ContinuousOn.comp' {g : β -> γ} {f : α -> β} {s : Se
t α} {t : Set β} (hg : ContinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo
 f s t) …
· 使用定理 `continuousOn_cfc_setProd`：continuousOn_cfc_setProd {s : Set 𝕜} (hs : IsC
ompact s) : ContinuousOn (fun fa : (𝕜 ->ᵤ[{s}] 𝕜) × A => cfc (toFun {s} fa.1) fa
.2) ({f | Cont…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `UniformOnFun.uniformContinuous_ofFun_toFun_of_mem`：uniformContinuous_ofF
un_toFun_of_mem (s : Set α) (h : s in 𝔖) : UniformContinuous (ofFun 𝔖 ∘ toFun {s
} : (α ->ᵤ[𝔖] β) -> α ->ᵤ[{s}] β)
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
（共 32 条，此处仅展示前 30 条）
-/
theorem continuousOn_cfc_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] 𝕜) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s} ×ˢ
        {a | p a ∧ s ∈ 𝓝ˢ (spectrum 𝕜 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (spectrum 𝕜 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfc _ => equals cfc (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfc_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_of_mem 𝕜 {t | IsCompact t ∧ t ⊆ s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨hf.mono hks, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` tends to `a₀ : A` along a
filter `l` (such that eventually `a x` satisfies the predicate `p` associated to `𝕜` and has
spectrum contained in `s`, as does `a₀`), then `fun x ↦ cfc f (a x)` tends to `cfc f a₀`. -/
/-
**Filter.Tendsto.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] {
s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a : X → A} {a₀ : A} {l : Filter X
},       Filter.Tendsto a l (nhds a₀) →         (∀ᶠ (x : X) in l, spectrum 𝕜 (a 
x) ⊆ s) →           (∀ᶠ (x : X) in l, p (a x)) →             spectrum 𝕜 a₀ ⊆ s →
               p a₀ →                 autoParam (ContinuousOn f s) Filter.Tendst
o.cfc._auto_1 →                   Filter.Tendsto (fun x => cfc f (a x)) l (nhds 
(cfc f a₀))
参数：f : 𝕜 → 𝕜；nhds a₀；∀ᶠ (x : X) in l, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in l, p (a
 x)；ContinuousOn f s；fun x => cfc f (a x)；nhds (cfc f a₀)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `continuousOn_cfc`：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜
 -> 𝕜) (hf : ContinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` tends to `a₀ :
 A` along a
filter `l` (such that eventually `a x` satisfies the predicate `p` associated to
 `𝕜` and has
spectrum contained in `s`, as does `a₀`), then `fun x ↦ cfc f (a x)` tends to `c
fc f a₀`.
-/
protected theorem Filter.Tendsto.cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, spectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in l, p (a x))
    (ha₀ : spectrum 𝕜 a₀ ⊆ s) (ha₀' : p a₀) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc f (a x)) l (𝓝 (cfc f a₀)) := by
  apply continuousOn_cfc A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀`, and
eventually `a x` satisfies the predicate `p` associated to `𝕜` and has spectrum contained in `s`,
then `fun x ↦ cfc f (a x)` is continuous at `x₀`. -/
/-
**ContinuousAt.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a :
 X → A} {x₀ : X},       ContinuousAt a x₀ →         (∀ᶠ (x : X) in nhds x₀, spec
trum 𝕜 (a x) ⊆ s) →           (∀ᶠ (x : X) in nhds x₀, p (a x)) →             aut
oParam (ContinuousOn f s) ContinuousAt.cfc._auto_1 → ContinuousAt (fun x => cfc 
f (a x)) x₀
参数：f : 𝕜 → 𝕜；∀ᶠ (x : X) in nhds x₀, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in nhds x₀, 
p (a x)；ContinuousOn f s；fun x => cfc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : 
A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [ins
t_3 : No…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous 
at `x₀`, and
eventually `a x` satisfies the predicate `p` associated to `𝕜` and has spectrum 
contained in `s`,
then `fun x ↦ cfc f (a x)` is continuous at `x₀`.
-/
protected theorem ContinuousAt.cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, spectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousAt (fun x ↦ cfc f (a x)) x₀ :=
  ha_cont.tendsto.cfc hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀` within
a set `t : Set X`, and eventually `a x` satisfies the predicate `p` associated to `𝕜` and has
spectrum contained in `s`, then `fun x ↦ cfc f (a x)` is continuous at `x₀` within `t`. -/
/-
**ContinuousWithinAt.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWithinAt`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a :
 X → A} {x₀ : X} {t : Set X},       x₀ ∈ t →         ContinuousWithinAt a t x₀ →
           (∀ᶠ (x : X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s) →             (
∀ᶠ (x : X) in nhdsWithin x₀ t, p (a x)) →               autoParam (ContinuousOn 
f s) ContinuousWithinAt.cfc._auto_1 →                 ContinuousWithinAt (fun x 
=> cfc f (a x)) t x₀
参数：f : 𝕜 → 𝕜；∀ᶠ (x : X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in n
hdsWithin x₀ t, p (a x)；ContinuousOn f s；fun x => cfc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : 
A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [ins
t_3 : No…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous 
at `x₀` within
a set `t : Set X`, and eventually `a x` satisfies the predicate `p` associated t
o `𝕜` and has
spectrum contained in `s`, then `fun x ↦ cfc f (a x)` is continuous at `x₀` with
in `t`.
-/
protected theorem ContinuousWithinAt.cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, spectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, p (a x)) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousWithinAt (fun x ↦ cfc f (a x)) t x₀ :=
  ha_cont.tendsto.cfc hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `a x` satisfies the predicate `p` for
all `x ∈ t`. Suppose further that `s : X → Set 𝕜` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : 𝕜 → 𝕜` is continuous on `s x`, for each `x ∈ t`, then `fun x ↦ cfc f (a x)` is
continuous on `t`. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
Suppose `a : X → Set A` is continuous on `t : Set X` and `a x` satisfies the pre
dicate `p` for
all `x ∈ t`. Suppose further that `s : X → Set 𝕜` is a family of sets with `s x`
 compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently clo
se `x ∈ t`.
If `f : 𝕜 → 𝕜` is continuous on `s x`, for each `x ∈ t`, then `fun x ↦ cfc f (a 
x)` is
continuous on `t`.
-/
protected theorem ContinuousOn.cfc [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, spectrum 𝕜 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, p (a x))
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfc (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and has spectrum contained in `s` for all
`x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`. -/
/-
**ContinuousOn.cfc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f :
 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (ha_cont : ContinuousOn a t) (ha : forall x in
 t, spectrum 𝕜 (a x) subseteq s) (ha' : forall x in t, p (a x)) (hf : Continuous
On f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜；ha_cont : ContinuousOn a t；ha : forall x in t, sp
ectrum 𝕜 (a x) subseteq s；ha' : forall x in t, p (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous 
on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and has spectrum contain
ed in `s` for all
`x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`.
-/
theorem ContinuousOn.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, spectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x ∈ t, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  refine ContinuousOn.cfc _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `a : X → A` is continuous on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood of the
spectra of `a x` for all `x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfc` since it requires `f` to be continuous on a *neighborhood* of
the spectra, but in practice it is often easier to apply because `s` is not required to be compact,
nor does it require an indexed family of compact sets. This is proven using `ContinuousOn.cfc` and
`upperHemicontinuous_spectrum` to produce the necessary family of compact sets. -/
/-
**ContinuousOn.cfc_of_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s 
: Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (hs : s in 𝓝ˢ (⋃ x in t, spectrum
 𝕜 (a x))) (ha_cont : ContinuousOn a t) (ha' : forall x in t, p (a x)
参数：f : 𝕜 -> 𝕜；hs : s in 𝓝ˢ (⋃ x in t, spectrum 𝕜 (a x))；ha_cont : ContinuousOn a
 t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_isCompact`：IsCompact.nhdsSet_basis_isCompact [Lo
callyCompactSpace X] {K : Set X} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun L => 
L in 𝓝ˢ K ∧ IsCompact L…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `spectrum.isCompact`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 
𝕜] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] [Pro
perSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `UpperHemicontinuous.upperHemicontinuousAt`：UpperHemicontinuous.upperHemi
continuousAt (h : UpperHemicontinuous f) (x : α) : UpperHemicontinuousAt f x
· 使用引理 `upperHemicontinuous_spectrum`：upperHemicontinuous_spectrum [NormedField 
𝕜] [ProperSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] : UpperH
emicontinuous (spe…
· 使用定理 `subset_of_mem_nhdsSet`：subset_of_mem_nhdsSet (h : t in 𝓝ˢ s) : s subsete
q t
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_dep_congr_ctx`：∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}
, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on `s` and `a : X → A` is continuous on `t : Set X`
,
and `a x` satisfies the predicate `p` associated to `𝕜` and `s` is a common neig
hborhood of the
spectra of `a x` for all `x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t
`.

This is weaker than `ContinuousOn.cfc` since it requires `f` to be continuous on
 a *neighborhood* of
the spectra, but in practice it is often easier to apply because `s` is not requ
ired to be compact,
nor does it require an indexed family of compact sets. This is proven using `Con
tinuousOn.cfc` and
`upperHemicontinuous_spectrum` to produce the necessary family of compact sets.
-/
theorem ContinuousOn.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, spectrum 𝕜 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, p (a x) := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), spectrum 𝕜 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      spectrum.isCompact (𝕜 := 𝕜) (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_spectrum 𝕜 A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfc (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is continuous and `a x` satisfies the predicate `p` for all `x`.
Suppose further that `s : X → Set 𝕜` is a family of compact sets `s x₀` contains the spectrum of
`a x` for all sufficiently close `x`. If `f : 𝕜 → 𝕜` is continuous on each `s x`, then
`fun x ↦ cfc f (a x)` is continuous. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
Suppose `a : X → Set A` is continuous and `a x` satisfies the predicate `p` for 
all `x`.
Suppose further that `s : X → Set 𝕜` is a family of compact sets `s x₀` contains
 the spectrum of
`a x` for all sufficiently close `x`. If `f : 𝕜 → 𝕜` is continuous on each `s x`
, then
`fun x ↦ cfc f (a x)` is continuous.
-/
protected theorem Continuous.cfc [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, spectrum 𝕜 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfc` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` varies over
elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`, and the
function `f` is continuous on the spectrum of `a`. -/
/-
**Continuous.cfc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜
 -> 𝕜) {a : X -> A} (ha_cont : Continuous a) (ha : forall x, spectrum 𝕜 (a x) su
bseteq s) (hf : ContinuousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜；ha_cont : Continuous a；ha : forall x, spectrum 𝕜 
(a x) subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc'`：ContinuousOn.cfc' [TopologicalSpace X] {s : Set 𝕜} (h
s : IsCompact s) (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (ha_cont : ContinuousOn a
 t) (ha…

--- 原说明 ---
`cfc` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` 
varies over
elements whose spectrum is contained in `s`, all of which satisfy the predicate 
`p`, and the
function `f` is continuous on the spectrum of `a`.
-/
theorem Continuous.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `a : X → A` is continuous and `a x` satisfies the
predicate `p` associated to `𝕜` and `s` is a common neighborhood of the spectra of `a x` for
all `x`, then `fun x ↦ cfc f (a x)` is continuous.

This is weaker than `Continuous.cfc` since it requires `f` to be continuous on a *neighborhood* of
the spectra, but in practice it is often easier to apply because `s` is not required to be compact,
nor does it require an indexed family of compact sets. This is proven using `Continuous.cfc` and
`upperHemicontinuous_spectrum` to produce the necessary family of compact sets. -/
/-
**Continuous.cfc_of_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : 
Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A} (hs : s in 𝓝ˢ (⋃ x, spectrum 𝕜 (a x))) (ha_cont
 : Continuous a) (ha' : forall x, p (a x)
参数：f : 𝕜 -> 𝕜；hs : s in 𝓝ˢ (⋃ x, spectrum 𝕜 (a x))；ha_cont : Continuous a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc_of_mem_nhdsSet`：ContinuousOn.cfc_of_mem_nhdsSet [Comple
teSpace A] [TopologicalSpace X] {s : Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X
} (hs : s in 𝓝ˢ (⋃ x …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on `s` and `a : X → A` is continuous and `a x` sati
sfies the
predicate `p` associated to `𝕜` and `s` is a common neighborhood of the spectra 
of `a x` for
all `x`, then `fun x ↦ cfc f (a x)` is continuous.

This is weaker than `Continuous.cfc` since it requires `f` to be continuous on a
 *neighborhood* of
the spectra, but in practice it is often easier to apply because `s` is not requ
ired to be compact,
nor does it require an indexed family of compact sets. This is proven using `Con
tinuous.cfc` and
`upperHemicontinuous_spectrum` to produce the necessary family of compact sets.
-/
theorem Continuous.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, spectrum 𝕜 (a x))) (ha_cont : Continuous a)
    (ha' : ∀ x, p (a x) := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_of_mem_nhdsSet f (by simpa) (by simpa)

end RCLike

section NNReal

variable {X A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousStar A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsSemitopologicalRing A]

variable (A) in
/-- A version of `continuousOn_cfc` over `ℝ≥0` instead of `RCLike 𝕜`. -/
/-
**continuousOn_cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc_nnreal {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 
-> Real>=0) (hf : ContinuousOn f s
参数：hs : IsCompact s；f : Real>=0 -> Real>=0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `ContinuousOn.ofReal_map_toNNReal`：∀ {f : NNReal → NNReal} {s : Set ℝ} {t
 : Set NNReal},   ContinuousOn f t → Set.MapsTo Real.toNNReal s t → ContinuousOn
 (fun x => ↑(f x.toNNR…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_image_iff`：mapsTo_image_iff {f : α -> β} {g : γ -> α} {s : Se
t γ} {t : Set β} : MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `continuousOn_cfc`：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜
 -> 𝕜) (hf : ContinuousOn f s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.eq_1`：∀ {R : Type u_3} {S : Type u_4} {A : Type u_5} [
inst : Semifield R] [inst_1 : Semifield S] [inst_2 : Ring A]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `continuousOn_cfc` over `ℝ≥0` instead of `RCLike 𝕜`.
-/
theorem continuousOn_cfc_nnreal {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a : A | 0 ≤ a ∧ spectrum ℝ≥0 a ⊆ s} := by
  have : {a : A | 0 ≤ a ∧ spectrum ℝ≥0 a ⊆ s}.EqOn (cfc f) (cfc (fun x : ℝ ↦ f x.toNNReal)) :=
    fun a ha ↦ cfc_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x ↦ f x.toNNReal : ℝ → ℝ) (NNReal.toReal '' s) := by
    apply hf.ofReal_map_toNNReal
    rw [Set.mapsTo_image_iff]
    intro x hx
    simpa
  refine continuousOn_cfc A (hs.image NNReal.continuous_coe) _ hf |>.mono fun a ha ↦ ?_
  simp only [Set.mem_ofPred_eq, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at ha ⊢
  rw [← SpectrumRestricts] at ha
  refine ⟨ha.1.1, ?_⟩
  rw [← ha.1.2.algebraMap_image]
  exact Set.image_mono ha.2

open UniformOnFun in
/-- Let `s : Set ℝ≥0` be a compact set and consider pairs `(f, a) : (ℝ≥0 → ℝ≥0) × A` where `f` is
continuous on `s` and `spectrum ℝ≥0 a ⊆ s` and `0 ≤ a`.

Then `cfc` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
/-
**continuousOn_cfc_nnreal_setProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc_nnreal_setProd {s : Set Real>=0} (hs : IsCompact s) : Con
tinuousOn (fun fa : (Real>=0 ->ᵤ[{s}] Real>=0) × A => cfc (toFun {s} fa.1) fa.2)
 ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | 0 <= a ∧ spectrum Real>=0 a subsete
q s})
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith`：continuousOn_prod_of_
continuousOn_lipschitzOnWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) {s : S…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_cfc_nnreal`：continuousOn_cfc_nnreal {s : Set Real>=0} (hs :
 IsCompact s) (f : Real>=0 -> Real>=0) (hf : ContinuousOn f s
· 使用引理 `lipschitzOnWith_cfc_fun_of_subset`：lipschitzOnWith_cfc_fun_of_subset (a 
: A) {s : Set R} (hs : spectrum R a subseteq s) : LipschitzOnWith 1 (fun f => cf
c (toFun {s} f) a) {f |…

--- 原说明 ---
Let `s : Set ℝ≥0` be a compact set and consider pairs `(f, a) : (ℝ≥0 → ℝ≥0) × A`
 where `f` is
continuous on `s` and `spectrum ℝ≥0 a ⊆ s` and `0 ≤ a`.

Then `cfc` is jointly continuous in both variables (i.e., continuous in its uncu
rried form) on this
set of pairs when the function space is equipped with the topology of uniform co
nvergence on `s`.
-/
theorem continuousOn_cfc_nnreal_setProd {s : Set ℝ≥0} (hs : IsCompact s) :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{s}] ℝ≥0) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | 0 ≤ a ∧ spectrum ℝ≥0 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfc_nnreal A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfc_fun_of_subset a ha')

open UniformOnFun in
/-
**continuousOn_cfc_nnreal_setProd_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set Real>=0
} : ContinuousOn (fun fa : (Real>=0 ->ᵤ[{t | IsCompact t ∧ t subseteq s}] Real>=
0) × A => cfc (toFun {s} fa.1) fa.2) ({f | ContinuousOn (toFun {t | IsCompact t 
∧ t subseteq s} f) s} ×ˢ {a | 0 <= a ∧ s in 𝓝ˢ (spectrum Real>=0 a)})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `continuousOn_of_locally_continuousOn`：continuousOn_of_locally_continuous
On (h : forall x in s, exists t, IsOpen t ∧ x in t ∧ ContinuousOn f (s inter t))
 : ContinuousOn f s
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `ContinuousFunctionalCalculus.isCompact_spectrum`：ContinuousFunctionalCal
culus.isCompact_spectrum (a : A) : IsCompact (spectrum R a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_isCompact`：IsCompact.nhdsSet_basis_isCompact [Lo
callyCompactSpace X] {K : Set X} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun L => 
L in 𝓝ˢ K ∧ IsCompact L…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Semicontinuous.isOpen`：Semicontinuous.isOpen (h : Semicontinuous r) (b :
 β) : IsOpen {x | r x b}
· 使用定理 `upperHemicontinuous_spectrum_nnreal`：upperHemicontinuous_spectrum_nnreal
 [NormedRing A] [NormedAlgebra Real A] [CompleteSpace A] : UpperHemicontinuous (
spectrum Real>=0 : A -> S…
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousOn.comp'`：ContinuousOn.comp' {g : β -> γ} {f : α -> β} {s : Se
t α} {t : Set β} (hg : ContinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo
 f s t) …
· 使用定理 `continuousOn_cfc_nnreal_setProd`：continuousOn_cfc_nnreal_setProd {s : Se
t Real>=0} (hs : IsCompact s) : ContinuousOn (fun fa : (Real>=0 ->ᵤ[{s}] Real>=0
) × A => cfc (toFun {…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `UniformOnFun.uniformContinuous_ofFun_toFun_of_mem`：uniformContinuous_ofF
un_toFun_of_mem (s : Set α) (h : s in 𝔖) : UniformContinuous (ofFun 𝔖 ∘ toFun {s
} : (α ->ᵤ[𝔖] β) -> α ->ᵤ[{s}] β)
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
（共 32 条，此处仅展示前 30 条）
-/
theorem continuousOn_cfc_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set ℝ≥0} :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] ℝ≥0) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s} ×ˢ
        {a | 0 ≤ a ∧ s ∈ 𝓝ˢ (spectrum ℝ≥0 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ≥0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum_nnreal A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (spectrum ℝ≥0 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfc _ => equals cfc (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfc_nnreal_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_of_mem _ {t | IsCompact t ∧ t ⊆ s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨hf.mono hks, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` tends to `a₀ : A` along a
filter `l` (such that eventually `0 ≤ a x` and has spectrum contained in `s`, as does `a₀`), then
`fun x ↦ cfc f (a x)` tends to `cfc f a₀`. -/
/-
**Filter.Tendsto.cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cfc_nnreal {s : Set Real>=0} (hs : IsCompact s) (f : Real>=
0 -> Real>=0) {a : X -> A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 
a₀)) (ha : forallᶠ x in l, spectrum Real>=0 (a x) subseteq s) (ha' : forallᶠ x i
n l, 0 <= a x) (ha₀ : spectrum Real>=0 a₀ subseteq s) (ha₀' : 0 <= a₀) (hf : Con
tinuousOn f s
参数：hs : IsCompact s；f : Real>=0 -> Real>=0；ha_tendsto : Tendsto a l (𝓝 a₀)；ha : 
forallᶠ x in l, spectrum Real>=0 (a x) subseteq s；ha' : forallᶠ x in l, 0 <= a x
；ha₀ : spectrum Real>=0 a₀ subseteq s；ha₀' : 0 <= a₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `continuousOn_cfc_nnreal`：continuousOn_cfc_nnreal {s : Set Real>=0} (hs :
 IsCompact s) (f : Real>=0 -> Real>=0) (hf : ContinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` tends to `
a₀ : A` along a
filter `l` (such that eventually `0 ≤ a x` and has spectrum contained in `s`, as
 does `a₀`), then
`fun x ↦ cfc f (a x)` tends to `cfc f a₀`.
-/
theorem Filter.Tendsto.cfc_nnreal {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, spectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in l, 0 ≤ a x)
    (ha₀ : spectrum ℝ≥0 a₀ ⊆ s) (ha₀' : 0 ≤ a₀) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc f (a x)) l (𝓝 (cfc f a₀)) := by
  apply continuousOn_cfc_nnreal A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀`, and
eventually `0 ≤ a x` and has spectrum contained in `s`, then `fun x ↦ cfc f (a x)` is continuous
at `x₀`. -/
/-
**ContinuousAt.cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.cfc_nnreal [TopologicalSpace X] {s : Set Real>=0} (hs : IsCom
pact s) (f : Real>=0 -> Real>=0) {a : X -> A} {x₀ : X} (ha_cont : ContinuousAt a
 x₀) (ha : forallᶠ x in 𝓝 x₀, spectrum Real>=0 (a x) subseteq s) (ha' : forallᶠ 
x in 𝓝 x₀, 0 <= a x) (hf : ContinuousOn f s
参数：hs : IsCompact s；f : Real>=0 -> Real>=0；ha_cont : ContinuousAt a x₀；ha : fora
llᶠ x in 𝓝 x₀, spectrum Real>=0 (a x) subseteq s；ha' : forallᶠ x in 𝓝 x₀, 0 <= a
 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Filter.Tendsto.cfc_nnreal`：Filter.Tendsto.cfc_nnreal {s : Set Real>=0} (
hs : IsCompact s) (f : Real>=0 -> Real>=0) {a : X -> A} {a₀ : A} {l : Filter X} 
(ha_tendsto : T…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continu
ous at `x₀`, and
eventually `0 ≤ a x` and has spectrum contained in `s`, then `fun x ↦ cfc f (a x
)` is continuous
at `x₀`.
-/
theorem ContinuousAt.cfc_nnreal [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, spectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousAt (fun x ↦ cfc f (a x)) x₀ :=
  ha_cont.tendsto.cfc_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀`
within a set `t : Set X`, and eventually `0 ≤ a x` and has spectrum contained in `s`, then
`fun x ↦ cfc f (a x)` is continuous at `x₀` within `t`. -/
/-
**ContinuousWithinAt.cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.cfc_nnreal [TopologicalSpace X] {s : Set Real>=0} (hs :
 IsCompact s) (f : Real>=0 -> Real>=0) {a : X -> A} {x₀ : X} {t : Set X} (hx₀ : 
x₀ in t) (ha_cont : ContinuousWithinAt a t x₀) (ha : forallᶠ x in 𝓝[t] x₀, spect
rum Real>=0 (a x) subseteq s) (ha' : forallᶠ x in 𝓝[t] x₀, 0 <= a x) (hf : Conti
nuousOn f s
参数：hs : IsCompact s；f : Real>=0 -> Real>=0；hx₀ : x₀ in t；ha_cont : ContinuousWit
hinAt a t x₀；ha : forallᶠ x in 𝓝[t] x₀, spectrum Real>=0 (a x) subseteq s；ha' : 
forallᶠ x in 𝓝[t] x₀, 0 <= a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Filter.Tendsto.cfc_nnreal`：Filter.Tendsto.cfc_nnreal {s : Set Real>=0} (
hs : IsCompact s) (f : Real>=0 -> Real>=0) {a : X -> A} {a₀ : A} {l : Filter X} 
(ha_tendsto : T…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continu
ous at `x₀`
within a set `t : Set X`, and eventually `0 ≤ a x` and has spectrum contained in
 `s`, then
`fun x ↦ cfc f (a x)` is continuous at `x₀` within `t`.
-/
theorem ContinuousWithinAt.cfc_nnreal [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, spectrum ℝ≥0 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, 0 ≤ a x) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousWithinAt (fun x ↦ cfc f (a x)) t x₀ :=
  ha_cont.tendsto.cfc_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `0 ≤ a x` for all `x ∈ t`.
Suppose further that `s : X → Set ℝ≥0` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : ℝ≥0 → ℝ≥0` is continuous on `s x`, for each `x ∈ t`, then `fun x ↦ cfc f (a x)` is
continuous on `t`. -/
/-
**ContinuousOn.cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cfc_nnreal [TopologicalSpace X] {s : X -> Set Real>=0} (f : R
eal>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : forall x in t, IsCompact (s x)
) (ha_cont : ContinuousOn a t) (ha : forall x₀ in t, forallᶠ x in 𝓝[t] x₀, spect
rum Real>=0 (a x) subseteq s x₀) (ha' : forall x in t, 0 <= a x) (hf : forall x 
in t, ContinuousOn f (s x)
参数：f : Real>=0 -> Real>=0；hs : forall x in t, IsCompact (s x)；ha_cont : Continuo
usOn a t；ha : forall x₀ in t, forallᶠ x in 𝓝[t] x₀, spectrum Real>=0 (a x) subse
teq s x₀；ha' : forall x in t, 0 <= a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc_nnreal`：ContinuousWithinAt.cfc_nnreal [Topologica
lSpace X] {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0) {a : X -
> A} {x₀ : X} {t : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
Suppose `a : X → Set A` is continuous on `t : Set X` and `0 ≤ a x` for all `x ∈ 
t`.
Suppose further that `s : X → Set ℝ≥0` is a family of sets with `s x` compact wh
en
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently clo
se `x ∈ t`.
If `f : ℝ≥0 → ℝ≥0` is continuous on `s x`, for each `x ∈ t`, then `fun x ↦ cfc f
 (a x)` is
continuous on `t`.
-/
theorem ContinuousOn.cfc_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, spectrum ℝ≥0 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfc_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continuous on
`t : Set X`, and `0 ≤ a x` and has spectrum contained in `s` for all `x ∈ t`, then
`fun x ↦ cfc f (a x)` is continuous on `t`. -/
/-
**ContinuousOn.cfc_nnreal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cfc_nnreal' [TopologicalSpace X] {s : Set Real>=0} (hs : IsCo
mpact s) (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (ha_cont : Continuous
On a t) (ha : forall x in t, spectrum Real>=0 (a x) subseteq s) (ha' : forall x 
in t, 0 <= a x) (hf : ContinuousOn f s
参数：hs : IsCompact s；f : Real>=0 -> Real>=0；ha_cont : ContinuousOn a t；ha : foral
l x in t, spectrum Real>=0 (a x) subseteq s；ha' : forall x in t, 0 <= a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.cfc_nnreal`：ContinuousOn.cfc_nnreal [TopologicalSpace X] {s
 : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : for
all x in t, I…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continu
ous on
`t : Set X`, and `0 ≤ a x` and has spectrum contained in `s` for all `x ∈ t`, th
en
`fun x ↦ cfc f (a x)` is continuous on `t`.
-/
theorem ContinuousOn.cfc_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, spectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  refine ContinuousOn.cfc_nnreal _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `a : X → A` is continuous on `t : Set X`,
and `a x` is nonnegative for all `x ∈ t` and `s` is a common neighborhood of the
spectra of `a x` for all `x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfc_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the spectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`ContinuousOn.cfc_nnreal` and `upperHemicontinuous_spectrum_nnreal` to produce the necessary family
of compact sets. -/
/-
**ContinuousOn.cfc_nnreal_of_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace
 X] {s : Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : s 
in 𝓝ˢ (⋃ x in t, spectrum Real>=0 (a x))) (ha_cont : ContinuousOn a t) (ha' : fo
rall x in t, 0 <= a x
参数：f : Real>=0 -> Real>=0；hs : s in 𝓝ˢ (⋃ x in t, spectrum Real>=0 (a x))；ha_con
t : ContinuousOn a t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsCompact.nhdsSet_basis_isCompact`：IsCompact.nhdsSet_basis_isCompact [Lo
callyCompactSpace X] {K : Set X} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun L => 
L in 𝓝ˢ K ∧ IsCompact L…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `spectrum.isCompact_nnreal`：isCompact_nnreal {A : Type*} [NormedRing A] [
NormedAlgebra Real A] (a : A) [CompactSpace (spectrum Real a)] : IsCompact (spec
trum Real>=0 a)
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `UpperHemicontinuous.upperHemicontinuousAt`：UpperHemicontinuous.upperHemi
continuousAt (h : UpperHemicontinuous f) (x : α) : UpperHemicontinuousAt f x
· 使用定理 `upperHemicontinuous_spectrum_nnreal`：upperHemicontinuous_spectrum_nnreal
 [NormedRing A] [NormedAlgebra Real A] [CompleteSpace A] : UpperHemicontinuous (
spectrum Real>=0 : A -> S…
· 使用定理 `subset_of_mem_nhdsSet`：subset_of_mem_nhdsSet (h : t in 𝓝ˢ s) : s subsete
q t
· 使用定理 `ContinuousOn.cfc_nnreal`：ContinuousOn.cfc_nnreal [TopologicalSpace X] {s
 : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : for
all x in t, I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_dep_congr_ctx`：∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}
, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `a : X → A` is continuous on `t : Se
t X`,
and `a x` is nonnegative for all `x ∈ t` and `s` is a common neighborhood of the
spectra of `a x` for all `x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t
`.

This is weaker than `ContinuousOn.cfc_nnreal` since it requires `f` to be contin
uous on a
*neighborhood* of the spectra, but in practice it is often easier to apply becau
se `s` is not
required to be compact, nor does it require an indexed family of compact sets. T
his is proven using
`ContinuousOn.cfc_nnreal` and `upperHemicontinuous_spectrum_nnreal` to produce t
he necessary family
of compact sets.
-/
theorem ContinuousOn.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, spectrum ℝ≥0 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, 0 ≤ a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), spectrum ℝ≥0 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      spectrum.isCompact_nnreal (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_spectrum_nnreal A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfc_nnreal (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is a continuous family of nonnegative elements.
Suppose further that `s : X → Set ℝ≥0` is a family of compact sets such that `s x₀` contains the
spectrum of `a x` for all sufficiently close `x`. If `f : ℝ≥0 → ℝ≥0` is continuous on each `s x`,
then `fun x ↦ cfc f (a x)` is continuous. -/
/-
**Continuous.cfc_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cfc_nnreal [TopologicalSpace X] {s : X -> Set Real>=0} (f : Rea
l>=0 -> Real>=0) {a : X -> A} (ha_cont : Continuous a) (hs : forall x, IsCompact
 (s x)) (ha : forall x₀, forallᶠ x in 𝓝 x₀, spectrum Real>=0 (a x) subseteq s x₀
) (hf : forall x, ContinuousOn f (s x)
参数：f : Real>=0 -> Real>=0；ha_cont : Continuous a；hs : forall x, IsCompact (s x)；
ha : forall x₀, forallᶠ x in 𝓝 x₀, spectrum Real>=0 (a x) subseteq s x₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc_nnreal`：ContinuousOn.cfc_nnreal [TopologicalSpace X] {s
 : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : for
all x in t, I…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
Suppose `a : X → Set A` is a continuous family of nonnegative elements.
Suppose further that `s : X → Set ℝ≥0` is a family of compact sets such that `s 
x₀` contains the
spectrum of `a x` for all sufficiently close `x`. If `f : ℝ≥0 → ℝ≥0` is continuo
us on each `s x`,
then `fun x ↦ cfc f (a x)` is continuous.
-/
theorem Continuous.cfc_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, spectrum ℝ≥0 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfc` is continuous in the variable `a : A` when `s : Set ℝ≥0` is compact and `a` varies over
nonnegative elements whose spectrum is contained in `s`, and the function `f` is
continuous on `s`. -/
/-
**Continuous.cfc_nnreal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cfc_nnreal' [TopologicalSpace X] {s : Set Real>=0} (hs : IsComp
act s) (f : Real>=0 -> Real>=0) {a : X -> A} (ha_cont : Continuous a) (ha : fora
ll x, spectrum Real>=0 (a x) subseteq s) (hf : ContinuousOn f s
参数：hs : IsCompact s；f : Real>=0 -> Real>=0；ha_cont : Continuous a；ha : forall x,
 spectrum Real>=0 (a x) subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc_nnreal'`：ContinuousOn.cfc_nnreal' [TopologicalSpace X] 
{s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0) {a : X -> A} {t : 
Set X} (ha_con…

--- 原说明 ---
`cfc` is continuous in the variable `a : A` when `s : Set ℝ≥0` is compact and `a
` varies over
nonnegative elements whose spectrum is contained in `s`, and the function `f` is
continuous on `s`.
-/
theorem Continuous.cfc_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, spectrum ℝ≥0 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `a : X → A` is continuous and `a x` is nonnegative
for all `x` and `s` is a common neighborhood of the spectra of `a x` for all `x`, then
`fun x ↦ cfc f (a x)` is continuous.

This is weaker than `Continuous.cfc_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the spectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`Continuous.cfc_nnreal` and `upperHemicontinuous_spectrum_nnreal` to produce the necessary family
of compact sets. -/
/-
**Continuous.cfc_nnreal_of_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X
] {s : Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A} (hs : s in 𝓝ˢ (⋃ x, sp
ectrum Real>=0 (a x))) (ha_cont : Continuous a) (ha' : forall x, 0 <= a x
参数：f : Real>=0 -> Real>=0；hs : s in 𝓝ˢ (⋃ x, spectrum Real>=0 (a x))；ha_cont : C
ontinuous a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`：ContinuousOn.cfc_nnreal_of_mem_n
hdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0} (f : Real>=0 -> 
Real>=0) {a : X -> A} {t : S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `a : X → A` is continuous and `a x` 
is nonnegative
for all `x` and `s` is a common neighborhood of the spectra of `a x` for all `x`
, then
`fun x ↦ cfc f (a x)` is continuous.

This is weaker than `Continuous.cfc_nnreal` since it requires `f` to be continuo
us on a
*neighborhood* of the spectra, but in practice it is often easier to apply becau
se `s` is not
required to be compact, nor does it require an indexed family of compact sets. T
his is proven using
`Continuous.cfc_nnreal` and `upperHemicontinuous_spectrum_nnreal` to produce the
 necessary family
of compact sets.
-/
theorem Continuous.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, spectrum ℝ≥0 (a x))) (ha_cont : Continuous a)
    (ha' : ∀ x, 0 ≤ a x := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

end NNReal

end Right

end Unital

section NonUnital

section Left

section Generic

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalContinuousFunctionalCalculus R A p]

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum and map zero to itself, then
`fun x ↦ cfcₙ (F x) a` tends to `cfcₙ f a`. -/
/-
**tendsto_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and al
l
these functions are continuous on the spectrum and map zero to itself, then
`fun x ↦ cfcₙ (F x) a` tends to `cfcₙ f a`.
-/
theorem tendsto_cfcₙ_fun {l : Filter X} {F : X → R → R} {f : R → R} {a : A}
    (h_tendsto : TendstoUniformlyOn F f l (quasispectrum R a))
    (hF : ∀ᶠ x in l, ContinuousOn (F x) (quasispectrum R a)) (hF0 : ∀ᶠ x in l, F x 0 = 0) :
    Tendsto (fun x ↦ cfcₙ (F x) a) l (𝓝 (cfcₙ f a)) := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  have hf0 : f 0 = 0 := Eq.symm <|
    tendsto_nhds_unique (tendsto_const_nhds.congr' <| .symm hF0) <|
    h_tendsto.tendsto_at (quasispectrum.zero_mem R a)
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (quasispectrum R a) ∧ F x 0 = 0}
    have hs : s ∈ l := hF.and hF0
    rw [← tendsto_comap'_iff (i := ((↑) : s → X)) (by simpa)]
    conv =>
      enter [1, x]
      rw [Function.comp_apply, cfcₙ_apply (hf := x.2.1) (hf0 := x.2.2)]
    rw [cfcₙ_apply ..]
    apply cfcₙHom_continuous _ |>.tendsto _ |>.comp
    rw [ContinuousMapZero.isEmbedding_toContinuousMap.isInducing.tendsto_nhds_iff]
    change Tendsto (fun x : s ↦ (⟨_, x.2.1.domRestrict⟩ : C(quasispectrum R a, R))) _
      (𝓝 ⟨_, hf.domRestrict⟩)
    rw [hf.tendsto_domRestrict_iff_tendstoUniformlyOn (fun x ↦ x.2.1)]
    intro t
    simp only [eventually_comap, Subtype.forall]
    peel h_tendsto t with ht x _
    simp_all
  · simpa [cfcₙ_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a` and maps zero to itself, then
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀`. -/
/-
**continuousAt_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `
a`,
and each `f x` is continuous on the spectrum of `a` and maps zero to itself, the
n
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀`.
-/
theorem continuousAt_cfcₙ_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (quasispectrum R a))
    (hf : ∀ᶠ x in 𝓝 x₀, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : ∀ᶠ x in 𝓝 x₀, f x 0 = 0) :
    ContinuousAt (fun x ↦ cfcₙ (f x) a) x₀ :=
  tendsto_cfcₙ_fun h_tendsto hf hf0

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝[s] x₀`) on the spectrum of `a`,
and eventually each `f x` is continuous on the spectrum of `a` and maps zero to itself, then
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀` within `s`. -/
/-
**continuousWithinAt_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝[s] x₀`) on the spectrum o
f `a`,
and eventually each `f x` is continuous on the spectrum of `a` and maps zero to 
itself, then
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀` within `s`.
-/
theorem continuousWithinAt_cfcₙ_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (quasispectrum R a))
    (hf : ∀ᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : ∀ᶠ x in 𝓝[s] x₀, f x 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x ↦ cfcₙ (f x) a) s x₀ :=
  tendsto_cfcₙ_fun h_tendsto hf hf0

open UniformOnFun in
/-- If `f : X → R → R` is continuous on `s : Set X` in the topology on
`X → R →ᵤ[{spectrum R a}] → R`, and for each `x ∈ s`, `f x` is continuous on the spectrum and
maps zero to itself, then `x ↦ cfcₙ (f x) a` is continuous on `s` also. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : X → R → R` is continuous on `s : Set X` in the topology on
`X → R →ᵤ[{spectrum R a}] → R`, and for each `x ∈ s`, `f x` is continuous on the
 spectrum and
maps zero to itself, then `x ↦ cfcₙ (f x) a` is continuous on `s` also.
-/
theorem ContinuousOn.cfcₙ_fun [TopologicalSpace X] {f : X → R → R} {a : A} {s : Set X}
    (h_cont : ContinuousOn (fun x ↦ ofFun {quasispectrum R a} (f x)) s)
    (hf : ∀ x ∈ s, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : ∀ x ∈ s, f x 0 = 0) :
    ContinuousOn (fun x ↦ cfcₙ (f x) a) s := by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx ↦ continuousWithinAt_cfcₙ_fun (h_cont x hx) ?_ ?_
  all_goals filter_upwards [self_mem_nhdsWithin] with x hx
  exacts [hf x hx, hf0 x hx]

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum and maps zero to itself, then
`x ↦ cfcₙ (f x) a` is continuous. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → 
R`,
and each `f` is continuous on the spectrum and maps zero to itself, then
`x ↦ cfcₙ (f x) a` is continuous.
-/
theorem Continuous.cfcₙ_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {quasispectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) :
    Continuous fun x ↦ cfcₙ (f x) a := by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfcₙ_fun (fun x _ ↦ hf x) (fun x _ ↦ hf0 x)

end Generic

section Isometric

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [MetricSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalIsometricContinuousFunctionalCalculus R A p]

variable (R) in
open UniformOnFun in
open scoped NonUnitalContinuousFunctionalCalculus in
/-- The function `f ↦ cfcₙ f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{quasispectrum R a}] R`) on those functions which are continuous on
the quasispectrum and map zero to itself. -/
/-
**lipschitzOnWith_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `f ↦ cfcₙ f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{quasispectrum R a}] R`) on those functions which are 
continuous on
the quasispectrum and map zero to itself.
-/
lemma lipschitzOnWith_cfcₙ_fun (a : A) :
    LipschitzOnWith 1 (fun f ↦ cfcₙ (toFun {quasispectrum R a} f) a)
      {f | ContinuousOn (toFun {quasispectrum R a} f) (quasispectrum R a) ∧ f 0 = 0} := by
  by_cases ha : p a
  · rintro f ⟨hf, hf0⟩ g ⟨hg, hg0⟩
    simp only
    rw [cfcₙ_apply .., cfcₙ_apply .., isometry_cfcₙHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [← ContinuousMapZero.isometry_toContinuousMap.edist_eq,
      edist_continuousRestrict_of_singleton hf hg]
  · simpa [cfcₙ_apply_of_not_predicate a ha] using LipschitzWith.const' 0 |>.lipschitzOnWith

open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/-- The function `f ↦ cfcₙ f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{s}] R`) on those functions which are continuous on a set `s` containing
the quasispectrum and map zero to itself. -/
/-
**lipschitzOnWith_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `f ↦ cfcₙ f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{s}] R`) on those functions which are continuous on a 
set `s` containing
the quasispectrum and map zero to itself.
-/
lemma lipschitzOnWith_cfcₙ_fun_of_subset (a : A) {s : Set R} (hs : quasispectrum R a ⊆ s) :
    LipschitzOnWith 1 (fun f ↦ cfcₙ (toFun {s} f) a)
      {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0} := by
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {quasispectrum R a}) (𝔗 := {s}) (β := R)
    (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0})
  simpa using! lipschitzOnWith_cfcₙ_fun R a |>.comp h₃ (fun f ↦ .imp_left fun hf ↦ hf.mono hs)

end Isometric

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open scoped NonUnitalContinuousFunctionalCalculus ContinuousMapZero in
/-- `cfcₙHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`. -/
/-
**continuous_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cfcₙHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is comp
act and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy th
e predicate `p`.
-/
theorem continuous_cfcₙHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) [hs0 : Fact (0 ∈ s)]
    (f : C(s, 𝕜)₀) {a : X → A} (ha_cont : Continuous a)
    (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙHomSuperset (ha' x) (ha x) f) := by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simpa [map_zero] using! continuous_const
  | id => simpa only [cfcₙHomSuperset_id]
  | star_id => simp only [map_star, cfcₙHomSuperset_id]; fun_prop
  | add f g hf hg => simpa only [map_add] using! hf.add hg
  | mul f g hf hg => simpa only [map_mul] using! hf.mul hg
  | smul r f hf => simpa only [map_smul] using! hf.const_smul r
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_ofPred_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcₙHomSuperset_apply]
    rw [isometry_cfcₙHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcₙHom (ha' x)))]
    rw [ContinuousMapZero.norm_def, ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

variable (A) in
/-- For `f : 𝕜 → 𝕜` continuous on a set `s` for which `f 0 = 0`, `cfcₙ f` is continuous on the
set of `a : A` satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-quasispectrum is
contained in `s`. -/
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
For `f : 𝕜 → 𝕜` continuous on a set `s` for which `f 0 = 0`, `cfcₙ f` is continu
ous on the
set of `a : A` satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-qu
asispectrum is
contained in `s`.
-/
theorem continuousOn_cfcₙ {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A → A) {a | p a ∧ quasispectrum 𝕜 a ⊆ s} := by
  by_cases hs0 : 0 ∈ s
  · rw [continuousOn_iff_continuous_domRestrict]
    convert!
      continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.domRestrict⟩, hf0⟩ (X :=
        {a : A | p a ∧ quasispectrum 𝕜 a ⊆ s}) continuous_subtype_val (fun x ↦ x.2.2) with
      x
    rw [cfcₙHomSuperset_apply, Set.domRestrict_apply, cfcₙ_apply _ _ (hf.mono x.2.2) hf0 x.2.1]
    congr!
  · convert! continuousOn_empty _
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun a ha ↦ hs0 <| ha.2 <| quasispectrum.zero_mem 𝕜 a

open UniformOnFun in
/-- Let `s : Set 𝕜` be a compact set and consider pairs `(f, a) : (𝕜 → 𝕜) × A` where `f` is
continuous on `s`, maps zero itself, and `quasispectrum 𝕜 a ⊆ s` and `a` satisfies the predicate
`p a` for the continuous functional calculus.

Then `cfcₙ` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
Let `s : Set 𝕜` be a compact set and consider pairs `(f, a) : (𝕜 → 𝕜) × A` where
 `f` is
continuous on `s`, maps zero itself, and `quasispectrum 𝕜 a ⊆ s` and `a` satisfi
es the predicate
`p a` for the continuous functional calculus.

Then `cfcₙ` is jointly continuous in both variables (i.e., continuous in its unc
urried form) on this
set of pairs when the function space is equipped with the topology of uniform co
nvergence on `s`.
-/
theorem continuousOn_cfcₙ_setProd {s : Set 𝕜} (hs : IsCompact s) :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{s}] 𝕜) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s ∧ f 0 = 0} ×ˢ {a | p a ∧ quasispectrum 𝕜 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfcₙ A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfcₙ_fun_of_subset a ha')

open UniformOnFun in
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuousOn_cfcₙ_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] 𝕜) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s ∧ f 0 = 0} ×ˢ
        {a | p a ∧ s ∈ 𝓝ˢ (quasispectrum 𝕜 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (quasispectrum 𝕜 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfcₙ _ =>
    equals cfcₙ (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfcₙ_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_of_mem _ {t | IsCompact t ∧ t ⊆ s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨⟨hf.1.mono hks, hf.2⟩, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` tends to
`a₀ : A` along a filter `l` (such that eventually `a x` satisfies the predicate `p` associated to
`𝕜` and has quasispectrum contained in `s`, as does `a₀`), then `fun x ↦ cfcₙ f (a x)` tends to
`cfcₙ f a₀`. -/
/-
**Filter.Tendsto.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] {
s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a : X → A} {a₀ : A} {l : Filter X
},       Filter.Tendsto a l (nhds a₀) →         (∀ᶠ (x : X) in l, spectrum 𝕜 (a 
x) ⊆ s) →           (∀ᶠ (x : X) in l, p (a x)) →             spectrum 𝕜 a₀ ⊆ s →
               p a₀ →                 autoParam (ContinuousOn f s) Filter.Tendst
o.cfc._auto_1 →                   Filter.Tendsto (fun x => cfc f (a x)) l (nhds 
(cfc f a₀))
参数：f : 𝕜 → 𝕜；nhds a₀；∀ᶠ (x : X) in l, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in l, p (a
 x)；ContinuousOn f s；fun x => cfc f (a x)；nhds (cfc f a₀)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `continuousOn_cfc`：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜
 -> 𝕜) (hf : ContinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` 
tends to
`a₀ : A` along a filter `l` (such that eventually `a x` satisfies the predicate 
`p` associated to
`𝕜` and has quasispectrum contained in `s`, as does `a₀`), then `fun x ↦ cfcₙ f 
(a x)` tends to
`cfcₙ f a₀`.
-/
protected theorem Filter.Tendsto.cfcₙ {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in l, p (a x))
    (ha₀ : quasispectrum 𝕜 a₀ ⊆ s) (ha₀' : p a₀) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x ↦ cfcₙ f (a x)) l (𝓝 (cfcₙ f a₀)) := by
  apply continuousOn_cfcₙ A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is continuous
at `x₀`, and eventually `a x` satisfies the predicate `p` associated to `𝕜` and has quasispectrum
contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀`. -/
/-
**ContinuousAt.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a :
 X → A} {x₀ : X},       ContinuousAt a x₀ →         (∀ᶠ (x : X) in nhds x₀, spec
trum 𝕜 (a x) ⊆ s) →           (∀ᶠ (x : X) in nhds x₀, p (a x)) →             aut
oParam (ContinuousOn f s) ContinuousAt.cfc._auto_1 → ContinuousAt (fun x => cfc 
f (a x)) x₀
参数：f : 𝕜 → 𝕜；∀ᶠ (x : X) in nhds x₀, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in nhds x₀, 
p (a x)；ContinuousOn f s；fun x => cfc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : 
A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [ins
t_3 : No…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` 
is continuous
at `x₀`, and eventually `a x` satisfies the predicate `p` associated to `𝕜` and 
has quasispectrum
contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀`.
-/
protected theorem ContinuousAt.cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x ↦ cfcₙ f (a x)) x₀ :=
  ha_cont.tendsto.cfcₙ hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is continuous
at `x₀` within a set `t : Set X`, and eventually `a x` satisfies the predicate `p` associated to `𝕜`
and has quasispectrum contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀`
within `t`. -/
/-
**ContinuousWithinAt.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWithinAt`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a :
 X → A} {x₀ : X} {t : Set X},       x₀ ∈ t →         ContinuousWithinAt a t x₀ →
           (∀ᶠ (x : X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s) →             (
∀ᶠ (x : X) in nhdsWithin x₀ t, p (a x)) →               autoParam (ContinuousOn 
f s) ContinuousWithinAt.cfc._auto_1 →                 ContinuousWithinAt (fun x 
=> cfc f (a x)) t x₀
参数：f : 𝕜 → 𝕜；∀ᶠ (x : X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in n
hdsWithin x₀ t, p (a x)；ContinuousOn f s；fun x => cfc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : 
A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [ins
t_3 : No…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` 
is continuous
at `x₀` within a set `t : Set X`, and eventually `a x` satisfies the predicate `
p` associated to `𝕜`
and has quasispectrum contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuou
s at `x₀`
within `t`.
-/
protected theorem ContinuousWithinAt.cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, quasispectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, p (a x)) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x ↦ cfcₙ f (a x)) t x₀ :=
  ha_cont.tendsto.cfcₙ hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `a x` satisfies the predicate `p` for
all `x ∈ t`. Suppose further that `s : X → Set 𝕜` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : 𝕜 → 𝕜` is continuous on `s x` for each `x ∈ t`, and `f 0 = 0` then `fun x ↦ cfcₙ f (a x)`
is continuous on `t`. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
Suppose `a : X → Set A` is continuous on `t : Set X` and `a x` satisfies the pre
dicate `p` for
all `x ∈ t`. Suppose further that `s : X → Set 𝕜` is a family of sets with `s x`
 compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently clo
se `x ∈ t`.
If `f : 𝕜 → 𝕜` is continuous on `s x` for each `x ∈ t`, and `f 0 = 0` then `fun 
x ↦ cfcₙ f (a x)`
is continuous on `t`.
-/
protected theorem ContinuousOn.cfcₙ [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, quasispectrum 𝕜 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, p (a x))
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfcₙ (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is continuous
on `t : Set X`, and `a x` satisfies the predicate `p` associated to `𝕜` and has quasispectrum
contained in `s` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `t`. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` 
is continuous
on `t : Set X`, and `a x` satisfies the predicate `p` associated to `𝕜` and has 
quasispectrum
contained in `s` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `
t`.
-/
theorem ContinuousOn.cfcₙ' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x ∈ t, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  refine ContinuousOn.cfcₙ _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood of the
quasispectra of `a x` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfcₙ` since it requires `f` to be continuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`ContinuousOn.cfcₙ` and `upperHemicontinuous_quasispectrum` to produce the necessary family of
compact sets. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous 
on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and `s` is a common neig
hborhood of the
quasispectra of `a x` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous
 on `t`.

This is weaker than `ContinuousOn.cfcₙ` since it requires `f` to be continuous o
n a
*neighborhood* of the quasispectra, but in practice it is often easier to apply 
because `s` is not
required to be compact, nor does it require an indexed family of compact sets. T
his is proven using
`ContinuousOn.cfcₙ` and `upperHemicontinuous_quasispectrum` to produce the neces
sary family of
compact sets.
-/
theorem ContinuousOn.cfcₙ_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, quasispectrum 𝕜 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, p (a x) := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), quasispectrum 𝕜 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      quasispectrum.isCompact (𝕜 := 𝕜) (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_quasispectrum 𝕜 A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfcₙ (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is continuous and `a x` satisfies the predicate `p` for all `x`.
Suppose further that `s : X → Set 𝕜` is a family of compact sets `s x₀` contains the spectrum of
`a x` for all sufficiently close `x`. If `f : 𝕜 → 𝕜` is continuous on each `s x` and `f 0 = 0`, then
`fun x ↦ cfc f (a x)` is continuous. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
Suppose `a : X → Set A` is continuous and `a x` satisfies the predicate `p` for 
all `x`.
Suppose further that `s : X → Set 𝕜` is a family of compact sets `s x₀` contains
 the spectrum of
`a x` for all sufficiently close `x`. If `f : 𝕜 → 𝕜` is continuous on each `s x`
 and `f 0 = 0`, then
`fun x ↦ cfc f (a x)` is continuous.
-/
protected theorem Continuous.cfcₙ [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, quasispectrum 𝕜 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfcₙ` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` varies over
elements whose quasispectrum is contained in `s`, all of which satisfy the predicate `p`, and the
function `f` is continuous `s` and `f 0 = 0`. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
`cfcₙ` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
 varies over
elements whose quasispectrum is contained in `s`, all of which satisfy the predi
cate `p`, and the
function `f` is continuous `s` and `f 0 = 0`.
-/
theorem Continuous.cfcₙ' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous and `a x`
satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood of the quasispectra
of `a x` for all `x`, then `fun x ↦ cfcₙ f (a x)` is continuous.

This is weaker than `Continuous.cfcₙ` since it requires `f` to be continuous on a *neighborhood* of
the quasispectra, but in practice it is often easier to apply because `s` is not required to be
compact, nor does it require an indexed family of compact sets. This is proven using
`Continuous.cfcₙ` and `upperHemicontinuous_quasispectrum` to produce the necessary family of
compact sets. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If `f : 𝕜 → 𝕜` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous 
and `a x`
satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood o
f the quasispectra
of `a x` for all `x`, then `fun x ↦ cfcₙ f (a x)` is continuous.

This is weaker than `Continuous.cfcₙ` since it requires `f` to be continuous on 
a *neighborhood* of
the quasispectra, but in practice it is often easier to apply because `s` is not
 required to be
compact, nor does it require an indexed family of compact sets. This is proven u
sing
`Continuous.cfcₙ` and `upperHemicontinuous_quasispectrum` to produce the necessa
ry family of
compact sets.
-/
theorem Continuous.cfcₙ_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, quasispectrum 𝕜 (a x))) (ha_cont : Continuous a)
    (ha' : ∀ x, p (a x) := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_of_mem_nhdsSet f (by simpa) (by simpa)

end RCLike

section NNReal

variable {X A : Type*} [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsSemitopologicalRing A]

variable (A) in
/-- A version of `continuousOn_cfcₙ` over `ℝ≥0` instead of `RCLike 𝕜`. -/
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
A version of `continuousOn_cfcₙ` over `ℝ≥0` instead of `RCLike 𝕜`.
-/
theorem continuousOn_cfcₙ_nnreal {s : Set ℝ≥0} (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A → A) {a : A | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s} := by
  have : {a : A | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s}.EqOn (cfcₙ f)
      (cfcₙ (fun x : ℝ ↦ f x.toNNReal)) :=
    fun a ha ↦ cfcₙ_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x ↦ f x.toNNReal : ℝ → ℝ) (NNReal.toReal '' s) := by
    apply hf.ofReal_map_toNNReal
    rw [Set.mapsTo_image_iff]
    intro x hx
    simpa
  refine continuousOn_cfcₙ A (hs.image NNReal.continuous_coe) _ hf |>.mono fun a ha ↦ ?_
  simp only [Set.mem_ofPred_eq, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at ha ⊢
  refine ⟨ha.1.1, ?_⟩
  rw [← ha.1.2.algebraMap_image]
  exact Set.image_mono ha.2

open UniformOnFun in
/-- Let `s : Set ℝ≥0` be a compact set and consider pairs `(f, a) : (ℝ≥0 → ℝ≥0) × A` where `f` is
continuous on `s`, maps zero to itself, `spectrum ℝ≥0 a ⊆ s` and `0 ≤ a`.

Then `cfcₙ` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
Let `s : Set ℝ≥0` be a compact set and consider pairs `(f, a) : (ℝ≥0 → ℝ≥0) × A`
 where `f` is
continuous on `s`, maps zero to itself, `spectrum ℝ≥0 a ⊆ s` and `0 ≤ a`.

Then `cfcₙ` is jointly continuous in both variables (i.e., continuous in its unc
urried form) on this
set of pairs when the function space is equipped with the topology of uniform co
nvergence on `s`.
-/
theorem continuousOn_cfcₙ_nnreal_setProd {s : Set ℝ≥0} (hs : IsCompact s) :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{s}] ℝ≥0) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s ∧ f 0 = 0} ×ˢ {a | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfcₙ_nnreal A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfcₙ_fun_of_subset a ha')

open UniformOnFun in
/-
**continuousOn_cfc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜) (hf : Continu
ousOn f s
参数：hs : IsCompact s；f : 𝕜 -> 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcHomSuperset_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [in
st : CommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : 
IsTopologi…
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `continuous_cfcHomSuperset_left`：continuous_cfcHomSuperset_left [Topologi
calSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜)) (a : X -> A) (ha_cont :
 Continuous a) (ha :…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuousOn_cfcₙ_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set ℝ≥0} :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] ℝ≥0) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s ∧ f 0 = 0} ×ˢ
        {a | 0 ≤ a ∧ s ∈ 𝓝ˢ (quasispectrum ℝ≥0 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℝ≥0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum_nnreal A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (quasispectrum ℝ≥0 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfcₙ _ =>
    equals cfcₙ (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfcₙ_nnreal_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_of_mem _ {t | IsCompact t ∧ t ⊆ s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨⟨hf.1.mono hks, hf.2⟩, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` tends to
`a₀ : A` along a filter `l` (such that eventually `0 ≤ a x` and has quasispectrum contained in `s`,
as does `a₀`), then `fun x ↦ cfcₙ f (a x)` tends to `cfcₙ f a₀`. -/
/-
**Filter.Tendsto.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] {
s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a : X → A} {a₀ : A} {l : Filter X
},       Filter.Tendsto a l (nhds a₀) →         (∀ᶠ (x : X) in l, spectrum 𝕜 (a 
x) ⊆ s) →           (∀ᶠ (x : X) in l, p (a x)) →             spectrum 𝕜 a₀ ⊆ s →
               p a₀ →                 autoParam (ContinuousOn f s) Filter.Tendst
o.cfc._auto_1 →                   Filter.Tendsto (fun x => cfc f (a x)) l (nhds 
(cfc f a₀))
参数：f : 𝕜 → 𝕜；nhds a₀；∀ᶠ (x : X) in l, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in l, p (a
 x)；ContinuousOn f s；fun x => cfc f (a x)；nhds (cfc f a₀)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `continuousOn_cfc`：continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜
 -> 𝕜) (hf : ContinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X →
 A` tends to
`a₀ : A` along a filter `l` (such that eventually `0 ≤ a x` and has quasispectru
m contained in `s`,
as does `a₀`), then `fun x ↦ cfcₙ f (a x)` tends to `cfcₙ f a₀`.
-/
theorem Filter.Tendsto.cfcₙ_nnreal {s : Set ℝ≥0} (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, quasispectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in l, 0 ≤ a x)
    (ha₀ : quasispectrum ℝ≥0 a₀ ⊆ s) (ha₀' : 0 ≤ a₀) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x ↦ cfcₙ f (a x)) l (𝓝 (cfcₙ f a₀)) := by
  apply continuousOn_cfcₙ_nnreal A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is
continuous at `x₀`, and eventually `0 ≤ a x` and has quasispectrum contained in `s`, then
`fun x ↦ cfcₙ f (a x)` is continuous at `x₀`. -/
/-
**ContinuousAt.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a :
 X → A} {x₀ : X},       ContinuousAt a x₀ →         (∀ᶠ (x : X) in nhds x₀, spec
trum 𝕜 (a x) ⊆ s) →           (∀ᶠ (x : X) in nhds x₀, p (a x)) →             aut
oParam (ContinuousOn f s) ContinuousAt.cfc._auto_1 → ContinuousAt (fun x => cfc 
f (a x)) x₀
参数：f : 𝕜 → 𝕜；∀ᶠ (x : X) in nhds x₀, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in nhds x₀, 
p (a x)；ContinuousOn f s；fun x => cfc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : 
A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [ins
t_3 : No…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X →
 A` is
continuous at `x₀`, and eventually `0 ≤ a x` and has quasispectrum contained in 
`s`, then
`fun x ↦ cfcₙ f (a x)` is continuous at `x₀`.
-/
theorem ContinuousAt.cfcₙ_nnreal [TopologicalSpace X] {s : Set ℝ≥0}
    (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, quasispectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x ↦ cfcₙ f (a x)) x₀ :=
  ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is
continuous at `x₀` within a set `t : Set X`, and eventually `0 ≤ a x` and has quasispectrum
contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀` within `t`. -/
/-
**ContinuousWithinAt.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWithinAt`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : Set 𝕜},   IsCompact s →     ∀ (f : 𝕜 → 𝕜) {a :
 X → A} {x₀ : X} {t : Set X},       x₀ ∈ t →         ContinuousWithinAt a t x₀ →
           (∀ᶠ (x : X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s) →             (
∀ᶠ (x : X) in nhdsWithin x₀ t, p (a x)) →               autoParam (ContinuousOn 
f s) ContinuousWithinAt.cfc._auto_1 →                 ContinuousWithinAt (fun x 
=> cfc f (a x)) t x₀
参数：f : 𝕜 → 𝕜；∀ᶠ (x : X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s；∀ᶠ (x : X) in n
hdsWithin x₀ t, p (a x)；ContinuousOn f s；fun x => cfc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Filter.Tendsto.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : 
A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [ins
t_3 : No…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X →
 A` is
continuous at `x₀` within a set `t : Set X`, and eventually `0 ≤ a x` and has qu
asispectrum
contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀` within `t`.
-/
theorem ContinuousWithinAt.cfcₙ_nnreal [TopologicalSpace X] {s : Set ℝ≥0}
    (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, quasispectrum ℝ≥0 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, 0 ≤ a x) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x ↦ cfcₙ f (a x)) t x₀ :=
  ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `0 ≤ a x` for all `x ∈ t`.
Suppose further that `s : X → Set ℝ≥0` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : ℝ≥0 → ℝ≥0` is continuous on `s x` for each `x ∈ t` and `f 0 = 0`, then
`fun x ↦ cfc f (a x)` is continuous on `t`. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
Suppose `a : X → Set A` is continuous on `t : Set X` and `0 ≤ a x` for all `x ∈ 
t`.
Suppose further that `s : X → Set ℝ≥0` is a family of sets with `s x` compact wh
en
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently clo
se `x ∈ t`.
If `f : ℝ≥0 → ℝ≥0` is continuous on `s x` for each `x ∈ t` and `f 0 = 0`, then
`fun x ↦ cfc f (a x)` is continuous on `t`.
-/
theorem ContinuousOn.cfcₙ_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, quasispectrum ℝ≥0 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfcₙ_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is
continuous on `t : Set X`, and `0 ≤ a x` and has quasispectrum contained in `s` for all `x ∈ t`,
then `fun x ↦ cfcₙ f (a x)` is continuous on `t`. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X →
 A` is
continuous on `t : Set X`, and `0 ≤ a x` and has quasispectrum contained in `s` 
for all `x ∈ t`,
then `fun x ↦ cfcₙ f (a x)` is continuous on `t`.
-/
theorem ContinuousOn.cfcₙ_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, quasispectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  refine ContinuousOn.cfcₙ_nnreal _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous on
`t : Set X`, and `a x` is nonnegative for all `x ∈ t` and `s` is a common neighborhood of the
quasispectra of `a x` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfcₙ_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`ContinuousOn.cfcₙ_nnreal` and `upperHemicontinuous_quasispectrum_nnreal` to produce the necessary
family of compact sets. -/
/-
**ContinuousOn.cfc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A} {t : Set X}
,   (∀ x ∈ t, IsCompact (s x)) →     ContinuousOn a t →       (∀ x₀ ∈ t, ∀ᶠ (x :
 X) in nhdsWithin x₀ t, spectrum 𝕜 (a x) ⊆ s x₀) →         (∀ x ∈ t, p (a x)) → 
          autoParam (∀ x ∈ t, ContinuousOn f (s x)) ContinuousOn.cfc._auto_1 → C
ontinuousOn (fun x => cfc f (a x)) t
参数：f : 𝕜 → 𝕜；∀ x ∈ t, IsCompact (s x)；∀ x₀ ∈ t, ∀ᶠ (x : X) in nhdsWithin x₀ t, s
pectrum 𝕜 (a x) ⊆ s x₀；∀ x ∈ t, p (a x)；∀ x ∈ t, ContinuousOn f (s x)；fun x => c
fc f (a x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `ContinuousWithinAt.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {
p : A → Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] 
[inst_3 : No…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `f 0 = 0` and `a : X → A` is continu
ous on
`t : Set X`, and `a x` is nonnegative for all `x ∈ t` and `s` is a common neighb
orhood of the
quasispectra of `a x` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous
 on `t`.

This is weaker than `ContinuousOn.cfcₙ_nnreal` since it requires `f` to be conti
nuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply 
because `s` is not
required to be compact, nor does it require an indexed family of compact sets. T
his is proven using
`ContinuousOn.cfcₙ_nnreal` and `upperHemicontinuous_quasispectrum_nnreal` to pro
duce the necessary
family of compact sets.
-/
theorem ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, quasispectrum ℝ≥0 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, 0 ≤ a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), quasispectrum ℝ≥0 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      quasispectrum.isCompact_nnreal (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_quasispectrum_nnreal A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfcₙ_nnreal (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is a continuous family of nonnegative elements.
Suppose further that `s : X → Set ℝ≥0` is a family of compact sets such that `s x₀` contains the
spectrum of `a x` for all sufficiently close `x`. If `f : ℝ≥0 → ℝ≥0` is continuous on each `s x`
and `f 0 = 0`, then `fun x ↦ cfc f (a x)` is continuous. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
Suppose `a : X → Set A` is a continuous family of nonnegative elements.
Suppose further that `s : X → Set ℝ≥0` is a family of compact sets such that `s 
x₀` contains the
spectrum of `a x` for all sufficiently close `x`. If `f : ℝ≥0 → ℝ≥0` is continuo
us on each `s x`
and `f 0 = 0`, then `fun x ↦ cfc f (a x)` is continuous.
-/
theorem Continuous.cfcₙ_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, quasispectrum ℝ≥0 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfcₙ` is continuous in the variable `a : A` when `s : Set ℝ≥0` is compact and `a` varies over
nonnegative elements whose quasispectrum is contained in `s`, and the function `f` is
continuous on `s` and `f 0 = 0`. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
`cfcₙ` is continuous in the variable `a : A` when `s : Set ℝ≥0` is compact and `
a` varies over
nonnegative elements whose quasispectrum is contained in `s`, and the function `
f` is
continuous on `s` and `f 0 = 0`.
-/
theorem Continuous.cfcₙ_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, quasispectrum ℝ≥0 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous and `a x` is
nonnegative for all `x` and `s` is a common neighborhood of the quasispectra of `a x` for all `x`,
then `fun x ↦ cfcₙ f (a x)` is continuous.

This is weaker than `Continuous.cfcₙ_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`Continuous.cfcₙ_nnreal` and `upperHemicontinuous_quasispectrum_nnreal` to produce the necessary
family of compact sets. -/
/-
**Continuous.cfc** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A → Prop} [inst : RCLi
ke 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_3 : NormedAlgebra 𝕜 
A] [inst_4 : IsometricContinuousFunctionalCalculus 𝕜 A p]   [ContinuousStar A] [
inst_6 : TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A},   Continuo
us a →     (∀ (x : X), IsCompact (s x)) →       (∀ (x₀ : X), ∀ᶠ (x : X) in nhds 
x₀, spectrum 𝕜 (a x) ⊆ s x₀) →         autoParam (∀ (x : X), ContinuousOn f (s x
)) Continuous.cfc._auto_1 →           autoParam (∀ (x : X), p (a x)) Continuous.
cfc._auto_3 → Continuous fun x => cfc f (a x)
参数：f : 𝕜 → 𝕜；∀ (x : X), IsCompact (s x)；∀ (x₀ : X), ∀ᶠ (x : X) in nhds x₀, spect
rum 𝕜 (a x) ⊆ s x₀；∀ (x : X), ContinuousOn f (s x)；∀ (x : X), p (a x)；a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.cfc`：∀ {X : Type u_1} {𝕜 : Type u_2} {A : Type u_3} {p : A 
→ Prop} [inst : RCLike 𝕜] [inst_1 : NormedRing A]   [inst_2 : StarRing A] [inst_
3 : No…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a

--- 原说明 ---
If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `f 0 = 0` and `a : X → A` is continu
ous and `a x` is
nonnegative for all `x` and `s` is a common neighborhood of the quasispectra of 
`a x` for all `x`,
then `fun x ↦ cfcₙ f (a x)` is continuous.

This is weaker than `Continuous.cfcₙ_nnreal` since it requires `f` to be continu
ous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply 
because `s` is not
required to be compact, nor does it require an indexed family of compact sets. T
his is proven using
`Continuous.cfcₙ_nnreal` and `upperHemicontinuous_quasispectrum_nnreal` to produ
ce the necessary
family of compact sets.
-/
theorem Continuous.cfcₙ_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, quasispectrum ℝ≥0 (a x)))
    (ha_cont : Continuous a) (ha' : ∀ x, 0 ≤ a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

end NNReal

end Right

end NonUnital

