/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Super-Polynomial Function Decay

This file defines a predicate `Asymptotics.SuperpolynomialDecay f` for a function satisfying
one of the following equivalent definitions (the definition is in terms of the first condition):

* `x ^ n * f` tends to `𝓝 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `𝓝 0` for all naturals `n` (`superpolynomialDecay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomialDecay_iff_abs_isBoundedUnder`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomialDecay_iff_isLittleO`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomialDecay_iff_isBigO`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.natDegree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : α → β` is relative to a parameter `k : α → β`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : β[X]`.
The definition is also relative to a filter `l : Filter α` where the decay rate is compared.

When the map `k` is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

## Main statements

* `SuperpolynomialDecay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomialDecay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/

@[expose] public section


namespace Asymptotics

open Topology Polynomial

open Filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
/-
**Asymptotics.SuperpolynomialDecay** 是 Mathlib 中的一个定义，位于命名空间 `Asymptotics`。
形式化陈述：SuperpolynomialDecay {α β : Type*} [TopologicalSpace β] [CommSemiring β] (
l : Filter α) (k : α -> β) (f : α -> β)
参数：l : Filter α；k : α -> β；f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n`
-/
def SuperpolynomialDecay {α β : Type*} [TopologicalSpace β] [CommSemiring β] (l : Filter α)
    (k : α → β) (f : α → β) :=
  ∀ n : ℕ, Tendsto (fun a : α => k a ^ n * f a) l (𝓝 0)

variable {α β : Type*} {l : Filter α} {k : α → β} {f g g' : α → β}

section CommSemiring

variable [TopologicalSpace β] [CommSemiring β]

/-
**Asymptotics.SuperpolynomialDecay.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : Top
ologicalSpace β] [inst_1 : CommSemiring β],   Asymptotics.SuperpolynomialDecay l
 k f → f =ᶠ[l] g → Asymptotics.SuperpolynomialDecay l k g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem SuperpolynomialDecay.congr' (hf : SuperpolynomialDecay l k f) (hfg : f =ᶠ[l] g) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr' (EventuallyEq.mul (EventuallyEq.refl l _) hfg)
/-
**Asymptotics.SuperpolynomialDecay.congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : Top
ologicalSpace β] [inst_1 : CommSemiring β],   Asymptotics.SuperpolynomialDecay l
 k f → (∀ (x : α), f x = g x) → Asymptotics.SuperpolynomialDecay l k g
参数：∀ (x : α), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem SuperpolynomialDecay.congr (hf : SuperpolynomialDecay l k f) (hfg : ∀ x, f x = g x) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr fun x => (congr_arg fun a => k x ^ z * a) <| hfg x

@[simp]
/-
**Asymptotics.superpolynomialDecay_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：superpolynomialDecay_zero (l : Filter α) (k : α -> β) : SuperpolynomialDec
ay l k 0
参数：l : Filter α；k : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem superpolynomialDecay_zero (l : Filter α) (k : α → β) : SuperpolynomialDecay l k 0 :=
  fun z => by simpa only [Pi.zero_apply, mul_zero] using tendsto_const_nhds
/-
**Asymptotics.SuperpolynomialDecay.add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Su
perpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : Top
ologicalSpace β] [inst_1 : CommSemiring β]   [ContinuousAdd β],   Asymptotics.Su
perpolynomialDecay l k f →     Asymptotics.SuperpolynomialDecay l k g → Asymptot
ics.SuperpolynomialDecay l k (f + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
-/
theorem SuperpolynomialDecay.add [ContinuousAdd β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f + g) := fun z => by
  simpa only [mul_add, add_zero, Pi.add_apply] using (hf z).add (hg z)
/-
**Asymptotics.SuperpolynomialDecay.mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Su
perpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : Top
ologicalSpace β] [inst_1 : CommSemiring β]   [ContinuousMul β],   Asymptotics.Su
perpolynomialDecay l k f →     Asymptotics.SuperpolynomialDecay l k g → Asymptot
ics.SuperpolynomialDecay l k (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
-/
theorem SuperpolynomialDecay.mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f * g) := fun z => by
  simpa only [mul_assoc, one_mul, mul_zero, pow_zero] using! (hf z).mul (hg 0)
/-
**Asymptotics.SuperpolynomialDecay.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β]   [ContinuousMul β],   Asymptotics.Supe
rpolynomialDecay l k f → ∀ (c : β), Asymptotics.SuperpolynomialDecay l k fun n =
> f n * c
参数：c : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
-/
theorem SuperpolynomialDecay.mul_const [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => f n * c := fun z => by
  simpa only [← mul_assoc, zero_mul] using Tendsto.mul_const c (hf z)
/-
**Asymptotics.SuperpolynomialDecay.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β]   [ContinuousMul β],   Asymptotics.Supe
rpolynomialDecay l k f → ∀ (c : β), Asymptotics.SuperpolynomialDecay l k fun n =
> c * f n
参数：c : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.mul_const`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β]   [ContinuousMul β],   As…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem SuperpolynomialDecay.const_mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => c * f n :=
  (hf.mul_const c).congr fun _ => mul_comm _ _
/-
**Asymptotics.SuperpolynomialDecay.param_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β],   Asymptotics.SuperpolynomialDecay l k
 f → Asymptotics.SuperpolynomialDecay l k (k * f)
参数：k * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhds`：tendsto_nhds {f : α -> X} {l : Filter α} : Tendsto f l (𝓝 
x) ↔ forall s, IsOpen s -> x in s -> f ⁻¹' s in l
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem SuperpolynomialDecay.param_mul (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (k * f) := fun z =>
  tendsto_nhds.2 fun s hs hs0 =>
    l.sets_of_superset ((tendsto_nhds.1 (hf <| z + 1)) s hs hs0) fun x hx => by
      simpa only [Set.mem_preimage, Pi.mul_apply, ← mul_assoc, ← pow_succ] using hx
/-
**Asymptotics.SuperpolynomialDecay.mul_param** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β],   Asymptotics.SuperpolynomialDecay l k
 f → Asymptotics.SuperpolynomialDecay l k (f * k)
参数：f * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_mul`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β],   Asymptotics.Superpolyn…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem SuperpolynomialDecay.mul_param (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (f * k) :=
  hf.param_mul.congr fun _ => mul_comm _ _
/-
**Asymptotics.SuperpolynomialDecay.param_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β],   Asymptotics.SuperpolynomialDecay l k
 f → ∀ (n : ℕ), Asymptotics.SuperpolynomialDecay l k (k ^ n * f)
参数：n : ℕ；k ^ n * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_mul`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β],   Asymptotics.Superpolyn…
-/
theorem SuperpolynomialDecay.param_pow_mul (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) := by
  induction n with
  | zero => simpa only [one_mul, pow_zero] using hf
  | succ n hn => simpa only [pow_succ', mul_assoc] using hn.param_mul
/-
**Asymptotics.SuperpolynomialDecay.mul_param_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β],   Asymptotics.SuperpolynomialDecay l k
 f → ∀ (n : ℕ), Asymptotics.SuperpolynomialDecay l k (f * k ^ n)
参数：n : ℕ；f * k ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_pow_mul`：∀ {α : Type u_1} {β : Ty
pe u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommS
emiring β],   Asymptotics.Superpolyn…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem SuperpolynomialDecay.mul_param_pow (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_comm _ _
/-
**Asymptotics.SuperpolynomialDecay.polynomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asy
mptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β]   [ContinuousAdd β] [ContinuousMul β], 
  Asymptotics.SuperpolynomialDecay l k f →     ∀ (p : Polynomial β), Asymptotics
.SuperpolynomialDecay l k fun x => Polynomial.eval (k x) p * f x
参数：p : Polynomial β；k x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Asymptotics.SuperpolynomialDecay.add`：∀ {α : Type u_1} {β : Type u_2} {l
 : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemiring 
β]   [ContinuousAdd β],   …
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Asymptotics.SuperpolynomialDecay.const_mul`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β]   [ContinuousMul β],   As…
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_pow_mul`：∀ {α : Type u_1} {β : Ty
pe u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommS
emiring β],   Asymptotics.Superpolyn…
-/
theorem SuperpolynomialDecay.polynomial_mul [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => (p.eval <| k x) * f x :=
  Polynomial.induction_on' p (fun p q hp hq => by simpa [add_mul] using! hp.add hq) fun n c => by
    simpa [mul_assoc] using! (hf.param_pow_mul n).const_mul c
/-
**Asymptotics.SuperpolynomialDecay.mul_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Asy
mptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : CommSemiring β]   [ContinuousAdd β] [ContinuousMul β], 
  Asymptotics.SuperpolynomialDecay l k f →     ∀ (p : Polynomial β), Asymptotics
.SuperpolynomialDecay l k fun x => f x * Polynomial.eval (k x) p
参数：p : Polynomial β；k x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.polynomial_mul`：∀ {α : Type u_1} {β : T
ype u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : Comm
Semiring β]   [ContinuousAdd β] [Cont…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem SuperpolynomialDecay.mul_polynomial [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => f x * (p.eval <| k x) :=
  (hf.polynomial_mul p).congr fun _ => mul_comm _ _

end CommSemiring

section OrderedCommSemiring

variable [TopologicalSpace β] [CommSemiring β] [PartialOrder β] [IsOrderedRing β] [OrderTopology β]

/-
**Asymptotics.SuperpolynomialDecay.trans_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 
`Asymptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g g' : α → β} [inst : 
TopologicalSpace β] [inst_1 : CommSemiring β]   [inst_2 : PartialOrder β] [IsOrd
eredRing β] [OrderTopology β],   0 ≤ᶠ[l] k →     Asymptotics.SuperpolynomialDeca
y l k g →       Asymptotics.SuperpolynomialDecay l k g' → g ≤ᶠ[l] f → f ≤ᶠ[l] g'
 → Asymptotics.SuperpolynomialDecay l k f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
theorem SuperpolynomialDecay.trans_eventuallyLE (hk : 0 ≤ᶠ[l] k) (hg : SuperpolynomialDecay l k g)
    (hg' : SuperpolynomialDecay l k g') (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') :
    SuperpolynomialDecay l k f := fun z =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
    (by filter_upwards [hfg, hk] with x hx (hx' : 0 ≤ k x) using by gcongr)
    (by filter_upwards [hfg', hk] with x hx (hx' : 0 ≤ k x) using by gcongr)

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace β] [CommRing β] [LinearOrder β] [IsStrictOrderedRing β] [OrderTopology β]
variable (l k f)

/-
**Asymptotics.superpolynomialDecay_iff_abs_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Asymptotics`。
形式化陈述：superpolynomialDecay_iff_abs_tendsto_zero : SuperpolynomialDecay l k f ↔ f
orall n : Nat, Tendsto (fun a : α => |k a ^ n * f a|) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_zero_iff_abs_tendsto_zero`：∀ {G : Type u_1} [inst : TopologicalS
pace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G
]   [OrderTopology G] {…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem superpolynomialDecay_iff_abs_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => |k a ^ n * f a|) l (𝓝 0) :=
  ⟨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z =>
    (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩
/-
**Asymptotics.superpolynomialDecay_iff_superpolynomialDecay_abs** 是 Mathlib 中的一个
定理，位于命名空间 `Asymptotics`。
形式化陈述：superpolynomialDecay_iff_superpolynomialDecay_abs : SuperpolynomialDecay l
 k f ↔ SuperpolynomialDecay l (fun a => |k a|) fun a => |f a|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.superpolynomialDecay_iff_abs_tendsto_zero`：superpolynomialDe
cay_iff_abs_tendsto_zero : SuperpolynomialDecay l k f ↔ forall n : Nat, Tendsto 
(fun a : α => |k a ^ n * f a|) l (𝓝 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem superpolynomialDecay_iff_superpolynomialDecay_abs :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => |k a|) fun a => |f a| :=
  (superpolynomialDecay_iff_abs_tendsto_zero l k f).trans
    (by simp_rw [SuperpolynomialDecay, abs_mul, abs_pow])

variable {l k f}
/-
**Asymptotics.SuperpolynomialDecay.trans_eventually_abs_le** 是 Mathlib 中的一个定理，位于
命名空间 `Asymptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : Top
ologicalSpace β] [inst_1 : CommRing β]   [inst_2 : LinearOrder β] [IsStrictOrder
edRing β] [OrderTopology β],   Asymptotics.SuperpolynomialDecay l k f → abs ∘ g 
≤ᶠ[l] abs ∘ f → Asymptotics.SuperpolynomialDecay l k g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.superpolynomialDecay_iff_abs_tendsto_zero`：superpolynomialDe
cay_iff_abs_tendsto_zero : SuperpolynomialDecay l k f ↔ forall n : Nat, Tendsto 
(fun a : α => |k a ^ n * f a|) l (𝓝 0)
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SuperpolynomialDecay.trans_eventually_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : abs ∘ g ≤ᶠ[l] abs ∘ f) : SuperpolynomialDecay l k g := by
  rw [superpolynomialDecay_iff_abs_tendsto_zero] at hf ⊢
  refine fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z)
      (Eventually.of_forall fun x => abs_nonneg _) (hfg.mono fun x hx => ?_)
  calc
    |k x ^ z * g x| = |k x ^ z| * |g x| := abs_mul (k x ^ z) (g x)
    _ ≤ |k x ^ z| * |f x| := by gcongr _ * ?_; exact hx
    _ = |k x ^ z * f x| := (abs_mul (k x ^ z) (f x)).symm
/-
**Asymptotics.SuperpolynomialDecay.trans_abs_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : Top
ologicalSpace β] [inst_1 : CommRing β]   [inst_2 : LinearOrder β] [IsStrictOrder
edRing β] [OrderTopology β],   Asymptotics.SuperpolynomialDecay l k f → (∀ (x : 
α), |g x| ≤ |f x|) → Asymptotics.SuperpolynomialDecay l k g
参数：∀ (x : α), |g x| ≤ |f x|。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.trans_eventually_abs_le`：∀ {α : Type u_
1} {β : Type u_2} {l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [in
st_1 : CommRing β]   [inst_2 : LinearOrder β] …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem SuperpolynomialDecay.trans_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : ∀ x, |g x| ≤ |f x|) : SuperpolynomialDecay l k g :=
  hf.trans_eventually_abs_le (Eventually.of_forall hfg)

end LinearOrderedCommRing

section Field

variable [TopologicalSpace β] [Field β] (l k f)

/-
**Asymptotics.superpolynomialDecay_mul_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics`。
形式化陈述：superpolynomialDecay_mul_const_iff [ContinuousMul β] {c : β} (hc0 : c != 0
) : (SuperpolynomialDecay l k fun n => f n * c) ↔ SuperpolynomialDecay l k f
参数：hc0 : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.mul_const`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β]   [ContinuousMul β],   As…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem superpolynomialDecay_mul_const_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => f n * c) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.mul_const c⁻¹).congr fun x => by simp [mul_assoc, mul_inv_cancel₀ hc0], fun h =>
    h.mul_const c⟩
/-
**Asymptotics.superpolynomialDecay_const_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics`。
形式化陈述：superpolynomialDecay_const_mul_iff [ContinuousMul β] {c : β} (hc0 : c != 0
) : (SuperpolynomialDecay l k fun n => c * f n) ↔ SuperpolynomialDecay l k f
参数：hc0 : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.const_mul`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β]   [ContinuousMul β],   As…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem superpolynomialDecay_const_mul_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => c * f n) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.const_mul c⁻¹).congr fun x => by simp [← mul_assoc, inv_mul_cancel₀ hc0], fun h =>
    h.const_mul c⟩

end Field

section LinearOrderedField

variable [TopologicalSpace β] [Field β] [LinearOrder β] [IsStrictOrderedRing β] [OrderTopology β]
variable (f)

/-
**Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder** 是 Mathlib 中的一个定理，位于命
名空间 `Asymptotics`。
形式化陈述：superpolynomialDecay_iff_abs_isBoundedUnder (hk : Tendsto k l atTop) : Sup
erpolynomialDecay l k f ↔ forall z : Nat, IsBoundedUnder (· <= ·) l fun a : α =>
 |k a ^ z * f a|
参数：hk : Tendsto k l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.Tendsto.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1
 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopol
ogy G] {…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.superpolynomialDecay_iff_abs_tendsto_zero`：superpolynomialDe
cay_iff_abs_tendsto_zero : SuperpolynomialDecay l k f ↔ forall n : Nat, Tendsto 
(fun a : α => |k a ^ n * f a|) l (𝓝 0)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_zero_iff_abs_tendsto_zero`：∀ {G : Type u_1} [inst : TopologicalS
pace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G
]   [OrderTopology G] {…
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
（共 43 条，此处仅展示前 30 条）
-/
theorem superpolynomialDecay_iff_abs_isBoundedUnder (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔
    ∀ z : ℕ, IsBoundedUnder (· ≤ ·) l fun a : α => |k a ^ z * f a| := by
  refine
    ⟨fun h z => Tendsto.isBoundedUnder_le (Tendsto.abs (h z)), fun h =>
      (superpolynomialDecay_iff_abs_tendsto_zero l k f).2 fun z => ?_⟩
  obtain ⟨m, hm⟩ := h (z + 1)
  have h1 : Tendsto (fun _ : α => (0 : β)) l (𝓝 0) := tendsto_const_nhds
  have h2 : Tendsto (fun a : α => |(k a)⁻¹| * m) l (𝓝 0) :=
    zero_mul m ▸
      Tendsto.mul_const m ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_atTop)
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (Eventually.of_forall fun x => abs_nonneg _)
      ((eventually_map.1 hm).mp ?_)
  refine (hk.eventually_ne_atTop 0).mono fun x hk0 hx => ?_
  refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left hx <| abs_nonneg (k x)⁻¹)
  rw [← abs_mul, ← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
/-
**Asymptotics.superpolynomialDecay_iff_zpow_tendsto_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Asymptotics`。
形式化陈述：superpolynomialDecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) : Supe
rpolynomialDecay l k f ↔ forall z : Int, Tendsto (fun a : α => k a ^ z * f a) l 
(𝓝 0)
参数：hk : Tendsto k l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_zpow_atTop_zero`：tendsto_zpow_atTop_zero {n : Int} (hn : n < 0) 
: Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem superpolynomialDecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, Tendsto (fun a : α => k a ^ z * f a) l (𝓝 0) := by
  refine ⟨fun h z => ?_, fun h n => by simpa only [zpow_natCast] using! h (n : ℤ)⟩
  by_cases! hz : 0 ≤ z
  · unfold Tendsto
    lift z to ℕ using hz
    simpa using! h z
  · have : Tendsto (fun a => k a ^ z) l (𝓝 0) :=
      Tendsto.comp (tendsto_zpow_atTop_zero hz) hk
    have h : Tendsto f l (𝓝 0) := by simpa using! h 0
    exact zero_mul (0 : β) ▸ this.mul h

variable {f}
/-
**Asymptotics.SuperpolynomialDecay.param_zpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asy
mptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : Field β]   [inst_2 : LinearOrder β] [IsStrictOrderedRin
g β] [OrderTopology β],   Filter.Tendsto k l Filter.atTop →     Asymptotics.Supe
rpolynomialDecay l k f → ∀ (z : ℤ), Asymptotics.SuperpolynomialDecay l k fun a =
> k a ^ z * f a
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.superpolynomialDecay_iff_zpow_tendsto_zero`：superpolynomialD
ecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) : SuperpolynomialDecay l k f
 ↔ forall z : Int, Tendsto (fun a : α => k a…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SuperpolynomialDecay.param_zpow_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) :
    SuperpolynomialDecay l k fun a => k a ^ z * f a := by
  rw [superpolynomialDecay_iff_zpow_tendsto_zero _ hk] at hf ⊢
  refine fun z' => (hf <| z' + z).congr' ((hk.eventually_ne_atTop 0).mono fun x hx => ?_)
  simp [zpow_add₀ hx, mul_assoc]
/-
**Asymptotics.SuperpolynomialDecay.mul_param_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Asy
mptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : Field β]   [inst_2 : LinearOrder β] [IsStrictOrderedRin
g β] [OrderTopology β],   Filter.Tendsto k l Filter.atTop →     Asymptotics.Supe
rpolynomialDecay l k f → ∀ (z : ℤ), Asymptotics.SuperpolynomialDecay l k fun a =
> f a * k a ^ z
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_zpow_mul`：∀ {α : Type u_1} {β : T
ype u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : Fiel
d β]   [inst_2 : LinearOrder β] [IsSt…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem SuperpolynomialDecay.mul_param_zpow (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) : SuperpolynomialDecay l k fun a => f a * k a ^ z :=
  (hf.param_zpow_mul hk z).congr fun _ => mul_comm _ _
/-
**Asymptotics.SuperpolynomialDecay.inv_param_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : Field β]   [inst_2 : LinearOrder β] [IsStrictOrderedRin
g β] [OrderTopology β],   Filter.Tendsto k l Filter.atTop →     Asymptotics.Supe
rpolynomialDecay l k f → Asymptotics.SuperpolynomialDecay l k (k⁻¹ * f)
参数：k⁻¹ * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_zpow_mul`：∀ {α : Type u_1} {β : T
ype u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : Fiel
d β]   [inst_2 : LinearOrder β] [IsSt…
-/
theorem SuperpolynomialDecay.inv_param_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (k⁻¹ * f) := by
  simpa using! hf.param_zpow_mul hk (-1)
/-
**Asymptotics.SuperpolynomialDecay.param_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics.SuperpolynomialDecay`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {k f : α → β} [inst : Topol
ogicalSpace β] [inst_1 : Field β]   [inst_2 : LinearOrder β] [IsStrictOrderedRin
g β] [OrderTopology β],   Filter.Tendsto k l Filter.atTop →     Asymptotics.Supe
rpolynomialDecay l k f → Asymptotics.SuperpolynomialDecay l k (f * k⁻¹)
参数：f * k⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr`：∀ {α : Type u_1} {β : Type u_2} 
{l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemirin
g β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.inv_param_mul`：∀ {α : Type u_1} {β : Ty
pe u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : Field
 β]   [inst_2 : LinearOrder β] [IsSt…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem SuperpolynomialDecay.param_inv_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (f * k⁻¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_comm _ _

variable (f)
/-
**Asymptotics.superpolynomialDecay_param_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics`。
形式化陈述：superpolynomialDecay_param_mul_iff (hk : Tendsto k l atTop) : Superpolynom
ialDecay l k (k * f) ↔ SuperpolynomialDecay l k f
参数：hk : Tendsto k l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.SuperpolynomialDecay.congr'`：∀ {α : Type u_1} {β : Type u_2}
 {l : Filter α} {k f g : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemiri
ng β],   Asymptotics.Superpol…
· 使用定理 `Asymptotics.SuperpolynomialDecay.inv_param_mul`：∀ {α : Type u_1} {β : Ty
pe u_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : Field
 β]   [inst_2 : LinearOrder β] [IsSt…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.SuperpolynomialDecay.param_mul`：∀ {α : Type u_1} {β : Type u
_2} {l : Filter α} {k f : α → β} [inst : TopologicalSpace β] [inst_1 : CommSemir
ing β],   Asymptotics.Superpolyn…
-/
theorem superpolynomialDecay_param_mul_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (k * f) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h =>
    (h.inv_param_mul hk).congr'
      ((hk.eventually_ne_atTop 0).mono fun x hx => by simp [← mul_assoc, inv_mul_cancel₀ hx]),
    fun h => h.param_mul⟩
/-
**Asymptotics.superpolynomialDecay_mul_param_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics`。
形式化陈述：superpolynomialDecay_mul_param_iff (hk : Tendsto k l atTop) : Superpolynom
ialDecay l k (f * k) ↔ SuperpolynomialDecay l k f
参数：hk : Tendsto k l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Asymptotics.superpolynomialDecay_param_mul_iff`：superpolynomialDecay_par
am_mul_iff (hk : Tendsto k l atTop) : SuperpolynomialDecay l k (k * f) ↔ Superpo
lynomialDecay l k f
-/
theorem superpolynomialDecay_mul_param_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (f * k) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm k] using superpolynomialDecay_param_mul_iff f hk
/-
**Asymptotics.superpolynomialDecay_param_pow_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Asymptotics`。
形式化陈述：superpolynomialDecay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : Nat) 
: SuperpolynomialDecay l k (k ^ n * f) ↔ SuperpolynomialDecay l k f
参数：hk : Tendsto k l atTop；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Asymptotics.superpolynomialDecay_param_mul_iff`：superpolynomialDecay_par
am_mul_iff (hk : Tendsto k l atTop) : SuperpolynomialDecay l k (k * f) ↔ Superpo
lynomialDecay l k f
-/
theorem superpolynomialDecay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) ↔ SuperpolynomialDecay l k f := by
  induction n with
  | zero => simp
  | succ n hn =>
    simpa [pow_succ, ← mul_comm k, mul_assoc,
      superpolynomialDecay_param_mul_iff (k ^ n * f) hk] using hn
/-
**Asymptotics.superpolynomialDecay_mul_param_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Asymptotics`。
形式化陈述：superpolynomialDecay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : Nat) 
: SuperpolynomialDecay l k (f * k ^ n) ↔ SuperpolynomialDecay l k f
参数：hk : Tendsto k l atTop；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Asymptotics.superpolynomialDecay_param_pow_mul_iff`：superpolynomialDecay
_param_pow_mul_iff (hk : Tendsto k l atTop) (n : Nat) : SuperpolynomialDecay l k
 (k ^ n * f) ↔ SuperpolynomialDecay l k …
-/
theorem superpolynomialDecay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm f] using superpolynomialDecay_param_pow_mul_iff f hk n

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedField β]
variable (l k f)

/-
**Asymptotics.superpolynomialDecay_iff_norm_tendsto_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Asymptotics`。
形式化陈述：superpolynomialDecay_iff_norm_tendsto_zero : SuperpolynomialDecay l k f ↔ 
forall n : Nat, Tendsto (fun a : α => ‖k a ^ n * f a‖) l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem superpolynomialDecay_iff_norm_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => ‖k a ^ n * f a‖) l (𝓝 0) :=
  ⟨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z =>
    tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩
/-
**Asymptotics.superpolynomialDecay_iff_superpolynomialDecay_norm** 是 Mathlib 中的一
个定理，位于命名空间 `Asymptotics`。
形式化陈述：superpolynomialDecay_iff_superpolynomialDecay_norm : SuperpolynomialDecay 
l k f ↔ SuperpolynomialDecay l (fun a => ‖k a‖) fun a => ‖f a‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.superpolynomialDecay_iff_norm_tendsto_zero`：superpolynomialD
ecay_iff_norm_tendsto_zero : SuperpolynomialDecay l k f ↔ forall n : Nat, Tendst
o (fun a : α => ‖k a ^ n * f a‖) l (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem superpolynomialDecay_iff_superpolynomialDecay_norm :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => ‖k a‖) fun a => ‖f a‖ :=
  (superpolynomialDecay_iff_norm_tendsto_zero l k f).trans (by simp [SuperpolynomialDecay])

variable {l k}
variable [LinearOrder β] [IsStrictOrderedRing β] [OrderTopology β]
/-
**Asymptotics.superpolynomialDecay_iff_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asympto
tics`。
形式化陈述：superpolynomialDecay_iff_isBigO (hk : Tendsto k l atTop) : Superpolynomial
Decay l k f ↔ forall z : Int, f =O[l] fun a : α => k a ^ z
参数：hk : Tendsto k l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.superpolynomialDecay_iff_zpow_tendsto_zero`：superpolynomialD
ecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) : SuperpolynomialDecay l k f
 ↔ forall z : Int, Tendsto (fun a : α => k a…
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Asymptotics.isBigO_of_div_tendsto_nhds`：isBigO_of_div_tendsto_nhds {α : 
Type*} {l : Filter α} {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) 
(c : 𝕜) (H : Filter.Tendsto …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsBigO.of_bound'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 (∀ᶠ (x : α) in l,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `add_neg_cancel_comm_assoc`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b
 : G), a + (b + -a) = b
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
（共 34 条，此处仅展示前 30 条）
-/
theorem superpolynomialDecay_iff_isBigO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =O[l] fun a : α => k a ^ z := by
  refine (superpolynomialDecay_iff_zpow_tendsto_zero f hk).trans ?_
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_atTop 0
  refine ⟨fun h z => ?_, fun h z => ?_⟩
  · refine isBigO_of_div_tendsto_nhds (hk0.mono fun x hx hxz ↦ absurd hxz (zpow_ne_zero _ hx)) 0 ?_
    have : (fun a : α => k a ^ z)⁻¹ = fun a : α => k a ^ (-z) := funext fun x => by simp
    rw [div_eq_mul_inv, mul_comm f, this]
    exact h (-z)
  · suffices (fun a : α => k a ^ z * f a) =O[l] fun a : α => (k a)⁻¹ from
      IsBigO.trans_tendsto this hk.inv_tendsto_atTop
    refine ((isBigO_refl (fun a => k a ^ z) l).mul (h (-(z + 1)))).trans ?_
    refine .of_bound' <| hk0.mono fun a ha0 => ?_
    simp [← zpow_add₀ ha0]
/-
**Asymptotics.superpolynomialDecay_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics`。
形式化陈述：superpolynomialDecay_iff_isLittleO (hk : Tendsto k l atTop) : Superpolynom
ialDecay l k f ↔ forall z : Int, f =o[l] fun a : α => k a ^ z
参数：hk : Tendsto k l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Asymptotics.isLittleO_of_tendsto'`：∀ {α : Type u_1} {𝕜 : Type u_15} [ins
t : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ᶠ (x : α) in l, g x 
= 0 → f x = 0) → Filter…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.superpolynomialDecay_iff_isBigO`：superpolynomialDecay_iff_is
BigO (hk : Tendsto k l atTop) : SuperpolynomialDecay l k f ↔ forall z : Int, f =
O[l] fun a : α => k a ^ z
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsBigO.of_bound'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 (∀ᶠ (x : α) in l,…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_one_add₀`：zpow_one_add₀ (h : a != 0) (i : Int) : a ^ (1 + i) = a * 
a ^ i
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 31 条，此处仅展示前 30 条）
-/
theorem superpolynomialDecay_iff_isLittleO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =o[l] fun a : α => k a ^ z := by
  refine ⟨fun h z => ?_, fun h => (superpolynomialDecay_iff_isBigO f hk).2 fun z => (h z).isBigO⟩
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_atTop 0
  have : (fun _ : α => (1 : β)) =o[l] k :=
    isLittleO_of_tendsto' (hk0.mono fun x hkx hkx' => absurd hkx' hkx)
      (by simpa using! hk.inv_tendsto_atTop)
  have : f =o[l] fun x : α => k x * k x ^ (z - 1) := by
    simpa using! this.mul_isBigO ((superpolynomialDecay_iff_isBigO f hk).1 h <| z - 1)
  refine this.trans_isBigO <| IsBigO.of_bound' <| hk0.mono fun x hkx => le_of_eq ?_
  simp [← zpow_one_add₀ hkx]

end NormedLinearOrderedField

end Asymptotics

