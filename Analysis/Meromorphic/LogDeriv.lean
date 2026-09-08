/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus using Claude Code
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic API for the Logarithmic Derivative
-/

@[expose] public section

open Filter Function Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 → 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-!
## Arithmetic on Codiscrete Sets

The pointwise lemma `logDeriv_mul` requires differentiability and nonvanishing of the factors at the
point in question. For meromorphic functions whose order is nowhere `⊤`, both conditions hold away
from a codiscrete set, turning the pointwise arithmetic into arithmetic of codiscrete equivalence
classes.
-/

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun MeromorphicOn.logDeriv_fun_mul_eventuallyEq]
/-
**MeromorphicOn.logDeriv_mul_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : Mer
omorphicOn g U) (h'f : forall x in U, meromorphicOrderAt f x != ⊤) (h'g : forall
 x in U, meromorphicOrderAt g x != ⊤) : logDeriv (f * g) =ᶠ[codiscreteWithin U] 
logDeriv f + logDeriv g
参数：hf : MeromorphicOn f U；hg : MeromorphicOn g U；h'f : forall x in U, meromorphi
cOrderAt f x != ⊤；h'g : forall x in U, meromorphicOrderAt g x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero`：MeromorphicOn.e
ventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜 -> E} (hf : Meromorp
hicOn f U) (h'f : forall x in U, meromorphicO…
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.mul_def`：mul_def (f g : forall i, M i) : f * g = fun i => f i * g i
· 使用定理 `logDeriv_mul`：logDeriv_mul {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg :
 g x != 0) (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) : logDe
ri…
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `U`, the
logarithmic derivative of a product of two meromorphic functions is the sum of t
he logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h'f : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x ∈ U, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscreteWithin U] logDeriv f + logDeriv g := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply, Pi.mul_def]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun Meromorphic.logDeriv_fun_mul_eventuallyEq]
/-
**Meromorphic.logDeriv_mul_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorph
ic g) (h'f : forall x, meromorphicOrderAt f x != ⊤) (h'g : forall x, meromorphic
OrderAt g x != ⊤) : logDeriv (f * g) =ᶠ[codiscrete 𝕜] logDeriv f + logDeriv g
参数：hf : Meromorphic f；hg : Meromorphic g；h'f : forall x, meromorphicOrderAt f x 
!= ⊤；h'g : forall x, meromorphicOrderAt g x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.logDeriv_mul_eventuallyEq`：MeromorphicOn.logDeriv_mul_even
tuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (h'f : forall x in U,
 meromorphicOrderAt f x != ⊤)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `𝕜`, the
logarithmic derivative of a product of two meromorphic functions is the sum of t
he logarithmic
derivatives.
-/
theorem Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : ∀ x, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscrete 𝕜] logDeriv f + logDeriv g :=
  (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ ↦ h'f x) (fun x _ ↦ h'g x)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun MeromorphicOn.logDeriv_fun_prod_eventuallyEq]
/-
**MeromorphicOn.logDeriv_prod_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι
 -> 𝕜 -> 𝕜'} (h : forall i in s, MeromorphicOn (F i) U) (h' : forall i in s, for
all x in U, meromorphicOrderAt (F i) x != ⊤) : logDeriv (∏ i in s, F i) =ᶠ[codis
creteWithin U] ∑ i in s, logDeriv (F i)
参数：h : forall i in s, MeromorphicOn (F i) U；h' : forall i in s, forall x in U, m
eromorphicOrderAt (F i) x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero`：MeromorphicOn.e
ventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜 -> E} (hf : Meromorp
hicOn f U) (h'f : forall x in U, meromorphicO…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.prod_fn`：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall 
a, CommMonoid (M a)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = f
un a…
· 使用定理 `logDeriv_prod`：logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜
'} {x : 𝕜} (hf : forall i in s, f i x != 0) (hd : forall i in s, DifferentiableA
t 𝕜…
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum o
f the logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, MeromorphicOn (F i) U)
    (h' : ∀ i ∈ s, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscreteWithin U] ∑ i ∈ s, logDeriv (F i) := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, F i y ≠ 0 :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).eventually_codiscreteWithin_apply_ne_zero
      (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply, Finset.prod_fn]
  exact logDeriv_prod h₂y fun i hi ↦ (h₁y i hi).differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun Meromorphic.logDeriv_fun_prod_eventuallyEq]
/-
**Meromorphic.logDeriv_prod_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Meromorphic.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι -
> 𝕜 -> 𝕜'} (h : forall i in s, Meromorphic (F i)) (h' : forall i in s, forall x,
 meromorphicOrderAt (F i) x != ⊤) : logDeriv (∏ i in s, F i) =ᶠ[codiscrete 𝕜] ∑ 
i in s, logDeriv (F i)
参数：h : forall i in s, Meromorphic (F i)；h' : forall i in s, forall x, meromorphi
cOrderAt (F i) x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.logDeriv_prod_eventuallyEq`：MeromorphicOn.logDeriv_prod_ev
entuallyEq {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'} (h : forall i in s, Mer
omorphicOn (F i) U) (h' : fora…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum o
f the logarithmic
derivatives.
-/
theorem Meromorphic.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, Meromorphic (F i)) (h' : ∀ i ∈ s, ∀ x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscrete 𝕜] ∑ i ∈ s, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi ↦ meromorphicOn_univ.mpr (h i hi))
  aesop

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
/-
**MeromorphicOn.logDeriv_finprod_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'}
 (hF : (mulSupport F).Finite) (h : forall i, MeromorphicOn (F i) U) (h' : forall
 i, forall x in U, meromorphicOrderAt (F i) x != ⊤) : logDeriv (∏ᶠ i, F i) =ᶠ[co
discreteWithin U] ∑ᶠ i, logDeriv (F i)
参数：hF : (mulSupport F).Finite；h : forall i, MeromorphicOn (F i) U；h' : forall i,
 forall x in U, meromorphicOrderAt (F i) x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `logDeriv_const`：logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 => a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `MeromorphicOn.logDeriv_prod_eventuallyEq`：MeromorphicOn.logDeriv_prod_ev
entuallyEq {ι : Type*} {s : Finset ι} {F : ι -> 𝕜 -> 𝕜'} (h : forall i in s, Mer
omorphicOn (F i) U) (h' : fora…

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum o
f the logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscreteWithin U] ∑ᶠ i, logDeriv (F i) := by
  have hsub : support (fun i ↦ logDeriv (F i)) ⊆ hF.toFinset := by
    simp +contextual [Set.subset_def, not_imp_not, Pi.one_def]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ ↦ h i) (fun i _ ↦ h' i)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
/-
**Meromorphic.logDeriv_finprod_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Meromorphic.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} (
hF : (mulSupport F).Finite) (h : forall i, Meromorphic (F i)) (h' : forall i x, 
meromorphicOrderAt (F i) x != ⊤) : logDeriv (∏ᶠ i, F i) =ᶠ[codiscrete 𝕜] ∑ᶠ i, l
ogDeriv (F i)
参数：hF : (mulSupport F).Finite；h : forall i, Meromorphic (F i)；h' : forall i x, m
eromorphicOrderAt (F i) x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.logDeriv_finprod_eventuallyEq`：MeromorphicOn.logDeriv_finp
rod_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} (hF : (mulSupport F).Finite) (h 
: forall i, MeromorphicOn (F i) U…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum o
f the logarithmic
derivatives.
-/
theorem Meromorphic.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscrete 𝕜] ∑ᶠ i, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i ↦ meromorphicOn_univ.mpr (h i))
  aesop

/--
Away from a codiscrete subset of `U`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
-/
@[to_fun MeromorphicOn.logDeriv_fun_zpow_eventuallyEq]
/-
**MeromorphicOn.logDeriv_zpow_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : Int
) : logDeriv (f ^ n) =ᶠ[codiscreteWithin U] n • logDeriv f
参数：hf : MeromorphicOn f U；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用引理 `logDeriv_fun_zpow`：logDeriv_fun_zpow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : Differ
entiableAt 𝕜 f x) (n : Int) : logDeriv (f · ^ n) x = n * logDeriv f x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […

--- 原说明 ---
Away from a codiscrete subset of `U`, the logarithmic derivative of the `n`-th p
ower of a
meromorphic function is `n` times the logarithmic derivative.
-/
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscreteWithin U] n • logDeriv f := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply, zsmul_eq_mul, show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

/--
Away from a codiscrete subset of `𝕜`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
-/
@[to_fun Meromorphic.logDeriv_fun_zpow_eventuallyEq]
/-
**Meromorphic.logDeriv_zpow_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Meromorphic.logDeriv_zpow_eventuallyEq (hf : Meromorphic f) (n : Int) : lo
gDeriv (f ^ n) =ᶠ[codiscrete 𝕜] n • logDeriv f
参数：hf : Meromorphic f；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.logDeriv_zpow_eventuallyEq`：MeromorphicOn.logDeriv_zpow_ev
entuallyEq (hf : MeromorphicOn f U) (n : Int) : logDeriv (f ^ n) =ᶠ[codiscreteWi
thin U] n • logDeriv f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f

--- 原说明 ---
Away from a codiscrete subset of `𝕜`, the logarithmic derivative of the `n`-th p
ower of a
meromorphic function is `n` times the logarithmic derivative.
-/
theorem Meromorphic.logDeriv_zpow_eventuallyEq (hf : Meromorphic f) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscrete 𝕜] n • logDeriv f := by
  apply MeromorphicOn.logDeriv_zpow_eventuallyEq (meromorphicOn_univ.mpr hf)


/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor.
-/
/-
**MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -
> 𝕜'} {d : ι -> Int} (hd : (support d).Finite) (h : forall i, MeromorphicOn (F i
) U) (h' : forall i, forall x in U, meromorphicOrderAt (F i) x != ⊤) : logDeriv 
(∏ᶠ i, F i ^ d i) =ᶠ[codiscreteWithin U] fun z => ∑ᶠ i, d i • logDeriv (F i) z
参数：hd : (support d).Finite；h : forall i, MeromorphicOn (F i) U；h' : forall i, fo
rall x in U, meromorphicOrderAt (F i) x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `MeromorphicOn.analyticAt_mem_codiscreteWithin`：analyticAt_mem_codiscrete
Within (hf : MeromorphicOn f U) : { x | AnalyticAt 𝕜 f x } in Filter.codiscreteW
ithin U
· 使用定理 `MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero`：MeromorphicOn.e
ventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜 -> E} (hf : Meromorp
hicOn f U) (h'f : forall x in U, meromorphicO…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.prod_fn`：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall 
a, CommMonoid (M a)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = f
un a…
· 使用定理 `logDeriv_prod`：logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜
'} {x : 𝕜} (hf : forall i in s, f i x != 0) (hd : forall i in s, DifferentiableA
t 𝕜…
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用引理 `AnalyticAt.zpow`：AnalyticAt.zpow {f : E -> 𝕝} {z : E} {n : Int} (h₁f : A
nalyticAt 𝕜 f z) (h₂f : f z != 0) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Pi.pow_def`：pow_def (f : forall i, M i) (a : α) : f ^ a = fun i => f i ^
 a
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `U`, the
logarithmic derivative of a finite product of integer powers of meromorphic func
tions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of stat
ement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a diviso
r.
-/
theorem MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscreteWithin U] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, F i y ≠ 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).eventually_codiscreteWithin_apply_ne_zero
      (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i ∈ hd.toFinset, F i ^ d i :=
    finprod_eq_prod_of_mulSupport_subset _ <| by simp +contextual [Set.subset_def, not_imp_not]
  have hsub : support (fun i ↦ d i • logDeriv (F i) y) ⊆ hd.toFinset := by
    simp +contextual [-support_mul, -mul_eq_zero, Set.subset_def, not_imp_not]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (fun z ↦ ∏ i ∈ hd.toFinset, (F i ^ d i) z) y := by rw [h₀, Finset.prod_fn]
    _ = ∑ i ∈ hd.toFinset, logDeriv (F i ^ d i) y :=
        logDeriv_prod (fun i hi ↦ zpow_ne_zero _ (h₂y i hi))
          (fun i hi ↦ ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i ∈ hd.toFinset, d i • logDeriv (F i) y := by
        congr! with i hi
        rw [zsmul_eq_mul, Pi.pow_def]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor.
-/
/-
**Meromorphic.logDeriv_finprod_zpow_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Meromorphic.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 
𝕜'} {d : ι -> Int} (hd : (support d).Finite) (h : forall i, Meromorphic (F i)) (
h' : forall i x, meromorphicOrderAt (F i) x != ⊤) : logDeriv (∏ᶠ i, F i ^ d i) =
ᶠ[codiscrete 𝕜] fun z => ∑ᶠ i, d i • logDeriv (F i) z
参数：hd : (support d).Finite；h : forall i, Meromorphic (F i)；h' : forall i x, mero
morphicOrderAt (F i) x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq`：MeromorphicOn.logDeriv
_finprod_zpow_eventuallyEq {ι : Type*} {F : ι -> 𝕜 -> 𝕜'} {d : ι -> Int} (hd : (
support d).Finite) (h : forall i, Mero…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The logarithmic derivative converts products into sums: away from a codiscrete s
ubset of `𝕜`, the
logarithmic derivative of a finite product of integer powers of meromorphic func
tions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of stat
ement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a diviso
r.
-/
theorem Meromorphic.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscrete 𝕜] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  apply MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i ↦ meromorphicOn_univ.mpr (h i))
  aesop
