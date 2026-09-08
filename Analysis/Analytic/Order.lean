/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing Order of Analytic Functions

This file defines the order of vanishing of an analytic function `f` at a point `z₀`, as an element
of `ℕ∞`.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

section NormedSpace
variable {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

open scoped Classical in
/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderAt f z₀` returns a junk value of `0`. -/
/-
**analyticOrderAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：analyticOrderAt (f : 𝕜 -> E) (z₀ : 𝕜) : Nat∞
参数：f : 𝕜 -> E；z₀ : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀
`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, w
here `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderAt f z₀` returns a junk value 
of `0`.
-/
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞ :=
  if hf : AnalyticAt 𝕜 f z₀ then
    if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ`.

The order is defined to be `0` if `f` is identically zero on a neighbourhood of `z₀`,
and is otherwise the unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`,
where `g` is analytic and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderNatAt f z₀` returns a junk value of `0`. -/
/-
**analyticOrderNatAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：analyticOrderNatAt (f : 𝕜 -> E) (z₀ : 𝕜) : Nat
参数：f : 𝕜 -> E；z₀ : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of vanishing of `f` at `z₀`, as an element of `ℕ`.

The order is defined to be `0` if `f` is identically zero on a neighbourhood of 
`z₀`,
and is otherwise the unique `n` such that `f` can locally be written as `f z = (
z - z₀) ^ n • g z`,
where `g` is analytic and does not vanish at `z₀`. See `AnalyticAt.analyticOrder
At_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderNatAt f z₀` returns a junk val
ue of `0`.
-/
noncomputable def analyticOrderNatAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ := (analyticOrderAt f z₀).toNat

@[simp]
/-
**analyticOrderAt_of_not_analyticAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : analyticOrd
erAt f z₀ = 0
参数：hf : ¬ AnalyticAt 𝕜 f z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma analyticOrderAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0 :=
  dif_neg hf

@[simp]
/-
**analyticOrderNatAt_of_not_analyticAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderNatAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : analytic
OrderNatAt f z₀ = 0
参数：hf : ¬ AnalyticAt 𝕜 f z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma analyticOrderNatAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) :
    analyticOrderNatAt f z₀ = 0 := by simp [analyticOrderNatAt, hf]
/-
**Nat.cast_analyticOrderNatAt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {z₀ : 𝕜},   an
alyticOrderAt f z₀ ≠ ⊤ → ↑(analyticOrderNatAt f z₀) = analyticOrderAt f z₀
参数：analyticOrderNatAt f z₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
-/
@[simp] lemma Nat.cast_analyticOrderNatAt (hf : analyticOrderAt f z₀ ≠ ⊤) :
    analyticOrderNatAt f z₀ = analyticOrderAt f z₀ := ENat.natCast_toNat hf

/-- The order of a function `f` at a `z₀` is infinity iff `f` vanishes locally around `z₀`. -/
/-
**analyticOrderAt_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_eq_top : analyticOrderAt f z₀ = ⊤ ↔ forallᶠ z in 𝓝 z₀, f z
 = 0 where mp hf
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `analyticAt_congr`：analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x 
↔ AnalyticAt 𝕜 g x
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The order of a function `f` at a `z₀` is infinity iff `f` vanishes locally aroun
d `z₀`.
-/
lemma analyticOrderAt_eq_top : analyticOrderAt f z₀ = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 where
  mp hf := by unfold analyticOrderAt at hf; split_ifs at hf with h <;> simp [*] at *
  mpr hf := by unfold analyticOrderAt; simp [hf, analyticAt_congr hf, analyticAt_const]
/-
**eventuallyConst_iff_analyticOrderAt_sub_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventuallyConst_iff_analyticOrderAt_sub_eq_top : EventuallyConst f (𝓝 z₀) 
↔ analyticOrderAt (f · - f z₀) z₀ = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
lemma eventuallyConst_iff_analyticOrderAt_sub_eq_top :
    EventuallyConst f (𝓝 z₀) ↔ analyticOrderAt (f · - f z₀) z₀ = ⊤ := by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ ↦ (show f z₀ = c from hc.self_of_nhds) ▸ hc, fun h ↦ ⟨_, h⟩⟩

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
/-
**AnalyticAt.analyticOrderAt_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) : analyticO
rderAt f z₀ = n ↔ exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z
 in 𝓝 z₀, f z = (z - z₀) ^ n • g z
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`：exists_eventuallyEq
_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) : (exists (n : Nat), exists (g : 
𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_inj`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用引理 `AnalyticAt.unique_eventuallyEq_pow_smul_nonzero`：unique_eventuallyEq_pow
_smul_nonzero {m n : Nat} (hm : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forall
ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m • g z…

--- 原说明 ---
The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f
` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not van
ish at `z₀`.
-/
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_natCast, false_iff]
    contrapose h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn ↦ (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' ↦ ?_⟩
    rw [AnalyticAt.unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
/-
**AnalyticAt.analyticOrderNatAt_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.analyticOrderNatAt_eq_iff (hf : AnalyticAt 𝕜 f z₀) (hf' : analy
ticOrderAt f z₀ != ⊤) {n : Nat} : analyticOrderNatAt f z₀ = n ↔ exists (g : 𝕜 ->
 E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z
参数：hf : AnalyticAt 𝕜 f z₀；hf' : analyticOrderAt f z₀ != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.cast_analyticOrderNatAt`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Non
triviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {f : 𝕜 → E} …
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f
` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not van
ish at `z₀`.
-/
lemma AnalyticAt.analyticOrderNatAt_eq_iff (hf : AnalyticAt 𝕜 f z₀) (hf' : analyticOrderAt f z₀ ≠ ⊤)
    {n : ℕ} :
    analyticOrderNatAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  simp [← Nat.cast_inj (R := ℕ∞), Nat.cast_analyticOrderNatAt hf', hf.analyticOrderAt_eq_natCast]

/-- The order of an analytic function `f` at `z₀` is finite iff `f` can locally be written as `f z =
  (z - z₀) ^ analyticOrderNatAt f z₀ • g z`, where `g` is analytic and does not vanish at `z₀`.

See `MeromorphicNFAt.order_eq_zero_iff` for an analogous statement about meromorphic functions in
normal form.
-/
/-
**AnalyticAt.analyticOrderAt_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.analyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) : analyticOrder
At f z₀ != ⊤ ↔ exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ f =ᶠ[𝓝 z₀] f
un z => (z - z₀) ^ analyticOrderNatAt f z₀ • g z
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The order of an analytic function `f` at `z₀` is finite iff `f` can locally be w
ritten as `f z =
  (z - z₀) ^ analyticOrderNatAt f z₀ • g z`, where `g` is analytic and does not 
vanish at `z₀`.

See `MeromorphicNFAt.order_eq_zero_iff` for an analogous statement about meromor
phic functions in
normal form.
-/
lemma AnalyticAt.analyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ ≠ ⊤ ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
        f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ analyticOrderNatAt f z₀ • g z := by
  simp only [← ENat.natCast_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.analyticOrderAt_eq_natCast,
    analyticOrderNatAt]
/-
**analyticOrderAt_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_eq_zero : analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨
 f z₀ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_zero`：natCast_zero : ((0 : Nat) : Nat∞) = 0
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma analyticOrderAt_eq_zero : analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ ≠ 0 := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · rw [← ENat.natCast_zero, hf.analyticOrderAt_eq_natCast]
    constructor
    · intro ⟨g, _, _, hg⟩
      simpa [hf, hg.self_of_nhds]
    · exact fun hz ↦ ⟨f, hf, hz.resolve_left <| not_not_intro hf, by simp⟩
  · simp [hf]
/-
**analyticOrderAt_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_ne_zero : analyticOrderAt f z₀ != 0 ↔ AnalyticAt 𝕜 f z₀ ∧ 
f z₀ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma analyticOrderAt_ne_zero : analyticOrderAt f z₀ ≠ 0 ↔ AnalyticAt 𝕜 f z₀ ∧ f z₀ = 0 := by
  simp [analyticOrderAt_eq_zero]

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
/-
**AnalyticAt.analyticOrderAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {z₀ : 𝕜}, Anal
yticAt 𝕜 f z₀ → (analyticOrderAt f z₀ = 0 ↔ f z₀ ≠ 0)
参数：analyticOrderAt f z₀ = 0 ↔ f z₀ ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at
 `z₀`.
-/
protected lemma AnalyticAt.analyticOrderAt_eq_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = 0 ↔ f z₀ ≠ 0 := by simp [hf, analyticOrderAt_eq_zero]

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
/-
**AnalyticAt.analyticOrderAt_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticAt`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {z₀ : 𝕜}, Anal
yticAt 𝕜 f z₀ → (analyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0)
参数：analyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …

--- 原说明 ---
The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at
 `z₀`.
-/
protected lemma AnalyticAt.analyticOrderAt_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0 := hf.analyticOrderAt_eq_zero.not_left

/-- A function vanishes at a point if its analytic order is nonzero in `ℕ∞`. -/
/-
**apply_eq_zero_of_analyticOrderAt_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：apply_eq_zero_of_analyticOrderAt_ne_zero (hf : analyticOrderAt f z₀ != 0) 
: f z₀ = 0
参数：hf : analyticOrderAt f z₀ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A function vanishes at a point if its analytic order is nonzero in `ℕ∞`.
-/
lemma apply_eq_zero_of_analyticOrderAt_ne_zero (hf : analyticOrderAt f z₀ ≠ 0) :
    f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderAt_eq_zero]

/-- A function vanishes at a point if its analytic order is nonzero when converted to ℕ. -/
/-
**apply_eq_zero_of_analyticOrderNatAt_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：apply_eq_zero_of_analyticOrderNatAt_ne_zero (hf : analyticOrderNatAt f z₀ 
!= 0) : f z₀ = 0
参数：hf : analyticOrderNatAt f z₀ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A function vanishes at a point if its analytic order is nonzero when converted t
o ℕ.
-/
lemma apply_eq_zero_of_analyticOrderNatAt_ne_zero (hf : analyticOrderNatAt f z₀ ≠ 0) :
    f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderNatAt, analyticOrderAt_eq_zero]

/-- Characterization of which natural numbers are `≤ hf.order`. Useful for avoiding case splits,
since it applies whether or not the order is `∞`. -/
/-
**natCast_le_analyticOrderAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natCast_le_analyticOrderAt (hf : AnalyticAt 𝕜 f z₀) {n : Nat} : n <= analy
ticOrderAt f z₀ ↔ exists g, AnalyticAt 𝕜 g z₀ ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀
) ^ n • g z
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`：exists_eventuallyEq
_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) : (exists (n : Nat), exists (g : 
𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `AnalyticAt.fun_pow`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Characterization of which natural numbers are `≤ hf.order`. Useful for avoiding 
case splits,
since it applies whether or not the order is `∞`.
-/
lemma natCast_le_analyticOrderAt (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} :
    n ≤ analyticOrderAt f z₀ ↔
      ∃ g, AnalyticAt 𝕜 g z₀ ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simpa using ⟨0, analyticAt_const .., by simpa⟩
  · let m := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
    obtain ⟨g, hg, hg_ne, hm⟩ := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose_spec
    rw [ENat.natCast_le_natCast]
    refine ⟨fun hmn ↦ ⟨fun z ↦ (z - z₀) ^ (m - n) • g z, by fun_prop, ?_⟩, fun ⟨h, hh, hfh⟩ ↦ ?_⟩
    · filter_upwards [hm] with z hz using by rwa [← mul_smul, ← pow_add, Nat.add_sub_of_le hmn]
    · contrapose! hg_ne
      have : ContinuousAt (fun z ↦ (z - z₀) ^ (n - m) • h z) z₀ := by fun_prop
      rw [tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z₀)
        hg.continuousAt.continuousWithinAt this.continuousWithinAt ?_]
      · simp [m, Nat.sub_ne_zero_of_lt hg_ne]
      · filter_upwards [self_mem_nhdsWithin, hm.filter_mono nhdsWithin_le_nhds,
          hfh.filter_mono nhdsWithin_le_nhds] with z hz hf' hf''
        rw [← inv_smul_eq_iff₀ (pow_ne_zero _ <| sub_ne_zero_of_ne hz), hf'', smul_comm,
          ← mul_smul] at hf'
        rw [pow_sub₀ _ (sub_ne_zero_of_ne hz) (by lia), ← hf']

/-- If two functions agree in a neighborhood of `z₀`, then their orders at `z₀` agree. -/
/-
**analyticOrderAt_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_congr (hfg : f =ᶠ[𝓝 z₀] g) : analyticOrderAt f z₀ = analyt
icOrderAt g z₀
参数：hfg : f =ᶠ[𝓝 z₀] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.eq_of_forall_natCast_le_iff`：eq_of_forall_natCast_le_iff (hm : fora
ll a : Nat, a <= m ↔ a <= n) : m = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.EventuallyEq.congr_left`：∀ {α : Type u} {β : Type v} {l : Filter 
α} {f g h : α → β}, f =ᶠ[l] g → (f =ᶠ[l] h ↔ g =ᶠ[l] h)
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If two functions agree in a neighborhood of `z₀`, then their orders at `z₀` agre
e.
-/
lemma analyticOrderAt_congr (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderAt f z₀ = analyticOrderAt g z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.congr hfg]
    congr! 3
    exact hfg.congr_left
  · rw [analyticOrderAt_of_not_analyticAt hf,
      analyticOrderAt_of_not_analyticAt fun hg ↦ hf <| hg.congr hfg.symm]
/-
**analyticOrderAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜], analyticOrderAt id 0 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma analyticOrderAt_id : analyticOrderAt (𝕜 := 𝕜) id 0 = 1 :=
  analyticAt_id.analyticOrderAt_eq_natCast.mpr ⟨fun _ ↦ 1, by fun_prop, by simp, by simp⟩
/-
**analyticOrderAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {z₀ : 𝕜}, anal
yticOrderAt (-f) z₀ = analyticOrderAt f z₀
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.eq_of_forall_natCast_le_iff`：eq_of_forall_natCast_le_iff (hm : fora
ll a : Nat, a <= m ↔ a <= n) : m = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AnalyticAt.neg`：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-
f) x
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `analyticAt_neg`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {E :
 Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 …
-/
@[simp] lemma analyticOrderAt_neg : analyticOrderAt (-f) z₀ = analyticOrderAt f z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.neg]
    exact (Equiv.neg _).exists_congr <| by simp [neg_eq_iff_eq_neg]
  · rw [analyticOrderAt_of_not_analyticAt hf,
      analyticOrderAt_of_not_analyticAt <| analyticAt_neg.not.2 hf]

/-- The order of a sum is at least the minimum of the orders of the summands. -/
/-
**le_analyticOrderAt_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_analyticOrderAt_add : min (analyticOrderAt f z₀) (analyticOrderAt g z₀)
 <= analyticOrderAt (f + g) z₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.forall_natCast_le_iff_le`：forall_natCast_le_iff_le : (forall a : Na
t, a <= m -> a <= n) ↔ m <= n
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a

--- 原说明 ---
The order of a sum is at least the minimum of the orders of the summands.
-/
theorem le_analyticOrderAt_add :
    min (analyticOrderAt f z₀) (analyticOrderAt g z₀) ≤ analyticOrderAt (f + g) z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · by_cases hg : AnalyticAt 𝕜 g z₀
    · refine ENat.forall_natCast_le_iff_le.mp fun n ↦ ?_
      simp only [le_min_iff, natCast_le_analyticOrderAt, hf, hg, hf.add hg]
      refine fun ⟨⟨F, hF, hF'⟩, ⟨G, hG, hG'⟩⟩ ↦ ⟨F + G, hF.add hG, ?_⟩
      filter_upwards [hF', hG'] with z using by simp +contextual
    · simp [*]
  · simp [*]
/-
**le_analyticOrderAt_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_analyticOrderAt_sub : min (analyticOrderAt f z₀) (analyticOrderAt g z₀)
 <= analyticOrderAt (f - g) z₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `analyticOrderAt_neg`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f 
: 𝕜 → E} …
· 使用定理 `le_analyticOrderAt_add`：le_analyticOrderAt_add : min (analyticOrderAt f 
z₀) (analyticOrderAt g z₀) <= analyticOrderAt (f + g) z₀
-/
lemma le_analyticOrderAt_sub :
    min (analyticOrderAt f z₀) (analyticOrderAt g z₀) ≤ analyticOrderAt (f - g) z₀ := by
  simpa [sub_eq_add_neg] using le_analyticOrderAt_add (f := f) (g := -g)
/-
**analyticOrderAt_add_eq_left_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_add_eq_left_of_lt (hfg : analyticOrderAt f z₀ < analyticOr
derAt g z₀) : analyticOrderAt (f + g) z₀ = analyticOrderAt f z₀
参数：hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `le_analyticOrderAt_sub`：le_analyticOrderAt_sub : min (analyticOrderAt f 
z₀) (analyticOrderAt g z₀) <= analyticOrderAt (f - g) z₀
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_analyticOrderAt_add`：le_analyticOrderAt_add : min (analyticOrderAt f 
z₀) (analyticOrderAt g z₀) <= analyticOrderAt (f + g) z₀
-/
lemma analyticOrderAt_add_eq_left_of_lt (hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt f z₀ :=
  le_antisymm (by simpa [hfg.not_ge] using le_analyticOrderAt_sub (f := f + g) (g := g) (z₀ := z₀))
    (by simpa [hfg.le] using le_analyticOrderAt_add (f := f) (g := g) (z₀ := z₀))
/-
**analyticOrderAt_add_eq_right_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_add_eq_right_of_lt (hgf : analyticOrderAt g z₀ < analyticO
rderAt f z₀) : analyticOrderAt (f + g) z₀ = analyticOrderAt g z₀
参数：hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `analyticOrderAt_add_eq_left_of_lt`：analyticOrderAt_add_eq_left_of_lt (hf
g : analyticOrderAt f z₀ < analyticOrderAt g z₀) : analyticOrderAt (f + g) z₀ = 
analyticOrderAt f z₀
-/
lemma analyticOrderAt_add_eq_right_of_lt (hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt g z₀ := by
  rw [add_comm, analyticOrderAt_add_eq_left_of_lt hgf]

/-- If two functions have unequal orders, then the order of their sum is exactly the minimum
of the orders of the summands. -/
/-
**analyticOrderAt_add_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_add_of_ne (hfg : analyticOrderAt f z₀ != analyticOrderAt g
 z₀) : analyticOrderAt (f + g) z₀ = min (analyticOrderAt f z₀) (analyticOrderAt 
g z₀)
参数：hfg : analyticOrderAt f z₀ != analyticOrderAt g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `analyticOrderAt_add_eq_left_of_lt`：analyticOrderAt_add_eq_left_of_lt (hf
g : analyticOrderAt f z₀ < analyticOrderAt g z₀) : analyticOrderAt (f + g) z₀ = 
analyticOrderAt f z₀
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用引理 `analyticOrderAt_add_eq_right_of_lt`：analyticOrderAt_add_eq_right_of_lt (
hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀) : analyticOrderAt (f + g) z₀ 
= analyticOrderAt g z₀

--- 原说明 ---
If two functions have unequal orders, then the order of their sum is exactly the
 minimum
of the orders of the summands.
-/
lemma analyticOrderAt_add_of_ne (hfg : analyticOrderAt f z₀ ≠ analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = min (analyticOrderAt f z₀) (analyticOrderAt g z₀) := by
  obtain hfg | hgf := hfg.lt_or_gt
  · simpa [hfg.le] using analyticOrderAt_add_eq_left_of_lt hfg
  · simpa [hgf.le] using analyticOrderAt_add_eq_right_of_lt hgf
/-
**analyticOrderAt_smul_eq_top_of_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_smul_eq_top_of_left {f : 𝕜 -> 𝕜} (hf : analyticOrderAt f z
₀ = ⊤) : analyticOrderAt (f • g) z₀ = ⊤
参数：hf : analyticOrderAt f z₀ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma analyticOrderAt_smul_eq_top_of_left {f : 𝕜 → 𝕜} (hf : analyticOrderAt f z₀ = ⊤) :
     analyticOrderAt (f • g) z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hf
  exact ⟨t, fun y hy ↦ by simp [h₁t y hy], h₂t, h₃t⟩
/-
**analyticOrderAt_smul_eq_top_of_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_smul_eq_top_of_right {f : 𝕜 -> 𝕜} (hg : analyticOrderAt g 
z₀ = ⊤) : analyticOrderAt (f • g) z₀ = ⊤
参数：hg : analyticOrderAt g z₀ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma analyticOrderAt_smul_eq_top_of_right {f : 𝕜 → 𝕜} (hg : analyticOrderAt g z₀ = ⊤) :
    analyticOrderAt (f • g) z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hg
  exact ⟨t, fun y hy ↦ by simp [h₁t y hy], h₂t, h₃t⟩

/-- The order is additive when scalar multiplying analytic functions. -/
/-
**analyticOrderAt_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_smul {f : 𝕜 -> 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticA
t 𝕜 g z₀) : analyticOrderAt (f • g) z₀ = analyticOrderAt f z₀ + analyticOrderAt 
g z₀
参数：hf : AnalyticAt 𝕜 f z₀；hg : AnalyticAt 𝕜 g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `analyticOrderAt_smul_eq_top_of_left`：analyticOrderAt_smul_eq_top_of_left
 {f : 𝕜 -> 𝕜} (hf : analyticOrderAt f z₀ = ⊤) : analyticOrderAt (f • g) z₀ = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用引理 `analyticOrderAt_smul_eq_top_of_right`：analyticOrderAt_smul_eq_top_of_rig
ht {f : 𝕜 -> 𝕜} (hg : analyticOrderAt g z₀ = ⊤) : analyticOrderAt (f • g) z₀ = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AnalyticAt.analyticOrderAt_ne_top`：AnalyticAt.analyticOrderAt_ne_top (hf
 : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ != ⊤ ↔ exists (g : 𝕜 -> E), Analyti
cAt 𝕜 g z₀ ∧ g z₀ != 0 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_analyticOrderNatAt`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Non
triviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {f : 𝕜 → E} …
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The order is additive when scalar multiplying analytic functions.
-/
lemma analyticOrderAt_smul {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f • g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : analyticOrderAt f z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_left, *]
  by_cases hg' : analyticOrderAt g z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_right, *]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨f', h₁f', h₂f', h₃f'⟩ := hf.analyticOrderAt_ne_top.1 hf'
  obtain ⟨g', h₁g', h₂g', h₃g'⟩ := hg.analyticOrderAt_ne_top.1 hg'
  rw [← Nat.cast_analyticOrderNatAt hf', ← Nat.cast_analyticOrderNatAt hg', ← ENat.natCast_add,
      (hf.smul hg).analyticOrderAt_eq_natCast]
  refine ⟨f' • g', h₁f'.smul h₁g', ?_, ?_⟩
  · simp
    tauto
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃f'
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := eventually_nhds_iff.1 h₃g'
    exact eventually_nhds_iff.2
      ⟨t ∩ s, fun y hy ↦ (by simp [h₁t y hy.1, h₁s y hy.2]; module), h₂t.inter h₂s, h₃t, h₃s⟩
/-
**AnalyticAt.analyticOrderAt_deriv_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.analyticOrderAt_deriv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x) [
CompleteSpace E] [CharZero 𝕜] : analyticOrderAt (deriv f) x + 1 = analyticOrderA
t (f · - f x) x
参数：hf : AnalyticAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `ENat.natCast_zero`：natCast_zero : ((0 : Nat) : Nat∞) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.exists_add_one_eq`：∀ {a : ℕ}, (∃ n, n + 1 = a) ↔ 0 < a
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `AnalyticAt.eventually_analyticAt`：AnalyticAt.eventually_analyticAt (h : 
AnalyticAt 𝕜 f x) : forallᶠ y in 𝓝 x, AnalyticAt 𝕜 f y
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 75 条，此处仅展示前 30 条）
-/
theorem AnalyticAt.analyticOrderAt_deriv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    [CompleteSpace E] [CharZero 𝕜] :
    analyticOrderAt (deriv f) x + 1 = analyticOrderAt (f · - f x) x := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    suffices analyticOrderAt (deriv f) x = ⊤ by simp_all
    simp only [analyticOrderAt_eq_top, sub_eq_zero] at h ⊢
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp h
    filter_upwards [hUo.mem_nhds hUx] with y hy
    simp [(eventuallyEq_of_mem (hUo.mem_nhds hy) hUf).deriv_eq]
  | coe r =>
    have hrne : r ≠ 0 := by
      intro hr
      rw [hr, ENat.natCast_zero, AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)] at h
      grind
    obtain ⟨s, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.pos_of_ne_zero hrne)
    rw [Nat.cast_succ]
    congr 1
    rw [analyticOrderAt_eq_natCast (by fun_prop)] at h
    obtain ⟨F, hFa, hFne, hfF⟩ := h
    simp only [sub_eq_iff_eq_add] at hfF
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp (hfF.and hFa.eventually_analyticAt)
    have : ∀ y ∈ U, deriv f y =
        (y - x) ^ (s + 1) • deriv F y + (s + 1) • (y - x) ^ s • F y := by
      intro y hy
      rw [EventuallyEq.deriv_eq (eventually_of_mem (hUo.mem_nhds hy) (fun u hu ↦ (hUf u hu).1)),
        deriv_add_const, deriv_fun_smul (by fun_prop) (hUf y hy).2.differentiableAt]
      simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]
    rw [analyticOrderAt_congr (eventually_of_mem (hUo.mem_nhds hUx) this)]
    have : analyticOrderAt (fun y ↦ (s + 1) • (y - x) ^ s • F y) x = s := by
      rw [analyticOrderAt_eq_natCast]
      · refine ⟨fun z ↦ (↑(s + 1) : 𝕜) • F z, hFa.fun_const_smul, ?_, .of_forall fun y ↦ ?_⟩
        · simpa using ⟨by norm_cast, hFne⟩
        · simpa only [Nat.cast_smul_eq_nsmul] using smul_comm ..
      · simp_rw [← Nat.cast_smul_eq_nsmul 𝕜]
        fun_prop
    rwa [← Pi.add_def, analyticOrderAt_add_eq_right_of_lt]
    rw [this, ← ENat.add_one_le_iff (ENat.natCast_ne_top _), ← Nat.cast_add_one,
      natCast_le_analyticOrderAt (by fun_prop)]
    exact ⟨deriv F, hFa.deriv, by simp⟩
/-
**AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : Analy
ticAt 𝕜 f x) (hf' : deriv f x != 0) : analyticOrderAt (f · - f x) x = 1
参数：hf : AnalyticAt 𝕜 f x；hf' : deriv f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_const`：deriv_const : deriv (fun _ => c) x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `eq_of_ge_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤ 
a → a ≤ b → a = b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `deriv_add_const`：deriv_add_const (c : F) : deriv (fun y => f y + c) x = 
deriv f x
· 使用定理 `deriv_fun_smul`：deriv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : Diffe
rentiableAt 𝕜 f x) : deriv (fun y => c y • f y) x = c x • deriv f x + deriv c x 
• f …
· 使用定理 `DifferentiableAt.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
（共 38 条，此处仅展示前 30 条）
-/
theorem AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hf' : deriv f x ≠ 0) : analyticOrderAt (f · - f x) x = 1 := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h, deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (analyticOrderAt_eq_natCast (by fun_prop)).mp h
    apply eq_of_ge_of_le
    · by_contra! hr
      have := hfF.self_of_nhds
      simp_all
    · contrapose! hf'
      simp_rw [sub_eq_iff_eq_add] at hfF
      rw [EventuallyEq.deriv_eq hfF, deriv_add_const, deriv_fun_smul (by fun_prop) (by fun_prop),
        deriv_fun_pow (by fun_prop), sub_self, zero_pow (by lia), zero_pow (by lia),
        mul_zero, zero_mul, zero_smul, zero_smul, add_zero]

/-- At a zero with nonvanishing derivative, the analytic order is 1.
This is a variant of `analyticOrderAt_sub_eq_one_of_deriv_ne_zero` with `f z₀ = 0`
replacing the subtraction. -/
/-
**AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero {x : 𝕜} (hf : Anal
yticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x != 0) : analyticOrderAt f x = 1
参数：hf : AnalyticAt 𝕜 f x；hfx : f x = 0；hf' : deriv f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`：AnalyticAt.analy
ticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : de
riv f x != 0) : analyticOrderAt (f · - f x) …

--- 原说明 ---
At a zero with nonvanishing derivative, the analytic order is 1.
This is a variant of `analyticOrderAt_sub_eq_one_of_deriv_ne_zero` with `f z₀ = 
0`
replacing the subtraction.
-/
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    analyticOrderAt f x = 1 := by
  simpa [hfx] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'
/-
**natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [Complet
eSpace E] (hf : AnalyticAt 𝕜 f z₀) : n <= analyticOrderAt f z₀ ↔ forall i < n, i
teratedDeriv i f z₀ = 0
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AnalyticAt.analyticOrderAt_deriv_add_one`：AnalyticAt.analyticOrderAt_der
iv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x) [CompleteSpace E] [CharZero 𝕜] : anal
yticOrderAt (deriv f) x + 1 = …
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ'`：iteratedDeriv_succ' : iteratedDeriv (n + 1) f = ite
ratedDeriv n (deriv f)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `analyticOrderAt_eq_zero`：analyticOrderAt_eq_zero : analyticOrderAt f z₀ 
= 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ != 0
（共 33 条，此处仅展示前 30 条）
-/
lemma natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [CompleteSpace E]
    (hf : AnalyticAt 𝕜 f z₀) :
    n ≤ analyticOrderAt f z₀ ↔ ∀ i < n, iteratedDeriv i f z₀ = 0 := by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    by_cases hfz : f z₀ = 0; swap
    · simpa [analyticOrderAt_eq_zero.mpr (.inr hfz)] using ⟨0, by simp, by simpa⟩
    have : analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f z₀ := by
      simpa [hfz] using hf.analyticOrderAt_deriv_add_one
    simp [← this, IH hf.deriv, iteratedDeriv_succ',
      -Order.lt_add_one_iff, Nat.forall_lt_succ_left, hfz]
/-
**analyticOrderAt_deriv_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_deriv_of_pos {𝕜 : Type*} {E : Type*} [NontriviallyNormedFi
eld 𝕜] [CharZero 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {
f : 𝕜 -> E} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) {n : Nat} (horder : analyticOrderA
t f z₀ = n + 1) : analyticOrderAt (deriv f) z₀ = n
参数：hf : AnalyticAt 𝕜 f z₀；horder : analyticOrderAt f z₀ = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AnalyticAt.analyticOrderAt_deriv_add_one`：AnalyticAt.analyticOrderAt_der
iv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x) [CompleteSpace E] [CharZero 𝕜] : anal
yticOrderAt (deriv f) x + 1 = …
-/
lemma analyticOrderAt_deriv_of_pos {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} (horder : analyticOrderAt f z₀ = n + 1) :
    analyticOrderAt (deriv f) z₀ = n := by
  have ⟨g, hg, hg₀, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).1 horder
  have hz₀ : f z₀ = 0 := by
    simpa [sub_self, zero_pow, zero_smul] using Filter.Eventually.self_of_nhds hfg
  simpa [hz₀, sub_zero, horder] using hf.analyticOrderAt_deriv_add_one
/-
**analyticOrderAt_iterated_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_iterated_deriv {𝕜 : Type*} {E : Type*} [NontriviallyNormed
Field 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 -> E}
 {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) {k n : Nat} [CharZero 𝕜] : n = analyticOrderA
t f z₀ -> n != 0 -> k <= n -> analyticOrderAt (deriv^[k] f) z₀ = (n - k : Nat)
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `analyticOrderAt_deriv_of_pos`：analyticOrderAt_deriv_of_pos {𝕜 : Type*} {
E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E] [Norm
edSpace 𝕜 E] [Comp…
· 使用定理 `AnalyticAt.iterated_deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F]
 {f : 𝕜 → F} {x…
-/
lemma analyticOrderAt_iterated_deriv {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {k n : ℕ} [CharZero 𝕜] :
    n = analyticOrderAt f z₀ → n ≠ 0 → k ≤ n → analyticOrderAt (deriv^[k] f) z₀ = (n - k : ℕ) := by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk ↦ Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    rw [Function.iterate_succ']
    have horder : analyticOrderAt (deriv^[n'] f) z₀ = (n - n'.succ) + 1 := by
      refine (hk Hn Hpos (by lia)).trans ?_
      have : (n - n'.succ) + 1 = n - n' := by grind
      rw [← this]
      simp
    simpa using (analyticOrderAt_deriv_of_pos (hf := AnalyticAt.iterated_deriv hf n')
      (n := n - n'.succ) horder)

attribute [local simp] Nat.factorial_ne_zero in
/-- A version of **Taylor's theorem** for analytic functions in one variable, with the error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eq_sum_add_pow_mul` for a version asserting global equality rather than
just on a neighbourhood of 0.) -/
/-
**AnalyticAt.exists_eventuallyEq_sum_add_pow_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.exists_eventuallyEq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace
 E] {f : 𝕜 -> E} (hf : AnalyticAt 𝕜 f 0) (n : Nat) : exists F : 𝕜 -> E, Analytic
At 𝕜 F 0 ∧ forallᶠ z in 𝓝 0, f z = (∑ i in .range n, (z ^ i / i.factorial) • ite
ratedDeriv i f 0) + z ^ n • F z
参数：hf : AnalyticAt 𝕜 f 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.analyticAt_fun_sum`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_3} {F : Type u_4}   [inst_1 : NormedAddCommGro
up E] [inst_2 :…
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用引理 `AnalyticAt.div_const`：AnalyticAt.div_const {f : E -> 𝕝} (hf : AnalyticAt
 𝕜 f x) {c : 𝕝} : AnalyticAt 𝕜 (f · / c) x
· 使用定理 `AnalyticAt.fun_pow`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `natCast_le_analyticOrderAt`：natCast_le_analyticOrderAt (hf : AnalyticAt 
𝕜 f z₀) {n : Nat} : n <= analyticOrderAt f z₀ ↔ exists g, AnalyticAt 𝕜 g z₀ ∧ fo
rallᶠ z in 𝓝 z₀,…
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`：natCast_le_analyti
cOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [CompleteSpace E] (hf : Analytic
At 𝕜 f z₀) : n <= analyticOrderAt f z₀ ↔ f…
· 使用定理 `iteratedDeriv_fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {
n : ℕ} {x :…
· 使用定理 `AnalyticAt.contDiffAt`：AnalyticAt.contDiffAt [CompleteSpace F] (h : Anal
yticAt 𝕜 f x) : ContDiffAt 𝕜 n f x
· 使用引理 `iteratedDeriv_fun_sum`：iteratedDeriv_fun_sum (hf : forall i in I, ContDi
ffAt 𝕜 n (f i) x) : iteratedDeriv n (fun z => ∑ i in I, f i z) x = ∑ i in I, ite
ratedDeriv …
· 使用定理 `ContDiffAt.smul_const`：ContDiffAt.smul_const {f : E -> A} {x : E} (hf : 
ContDiffAt 𝕜 n f x) (v : F) : ContDiffAt 𝕜 n (fun y => f y • v) x
· 使用定理 `ContDiffAt.div_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x 
: E} {𝕜' :…
· 使用定理 `ContDiffAt.pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {
n : …
· 使用定理 `contDiffAt_fun_id`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyN
ormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {n : 
WithTop…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iteratedDeriv_smul_const`：iteratedDeriv_smul_const {f : 𝕜 -> 𝔸} (hf : Co
ntDiffAt 𝕜 n f x) (v : F) : iteratedDeriv n (fun y => f y • v) x = iteratedDeriv
 n f x • v
· 使用定理 `iteratedDeriv_div_const`：iteratedDeriv_div_const {n : Nat} (f : 𝕜 -> 𝕜')
 (c : 𝕜') : iteratedDeriv n (f · / c) x = iteratedDeriv n f x / c
· 使用引理 `iteratedDeriv_fun_pow_zero`：iteratedDeriv_fun_pow_zero {n m : Nat} : ite
ratedDeriv n (· ^ m) (0 : 𝕜) = if n = m then m.factorial else 0
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A version of **Taylor's theorem** for analytic functions in one variable, with t
he error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eq_sum_add_pow_mul` for a version asserting global equal
ity rather than
just on a neighbourhood of 0.)
-/
lemma AnalyticAt.exists_eventuallyEq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) (n : ℕ) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F 0 ∧ ∀ᶠ z in 𝓝 0,
      f z = (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  simp only [← sub_eq_iff_eq_add']
  have : AnalyticAt 𝕜
      (fun z : 𝕜 ↦ ∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i hi ↦ ?_
    fun_prop
  convert! (natCast_le_analyticOrderAt (hf.fun_sub this)).mp ?_
  · simp
  · rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.fun_sub this)]
    intro i hi
    rw [iteratedDeriv_fun_sub (AnalyticAt.contDiffAt <| by fun_prop) this.contDiffAt]
    simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_smul_const,
      iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
    simp [ite_div, Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr hi)]

attribute [local simp] Nat.factorial_ne_zero in
/-- A version of **Taylor's theorem** for analytic functions in one variable, with the error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` for a version asserting equality on a
neighbourhood of `0` rather than globally.) -/
/-
**AnalyticAt.exists_eq_sum_add_pow_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.exists_eq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E] {f : 𝕜
 -> E} (hf : AnalyticAt 𝕜 f 0) (n : Nat) : exists F : 𝕜 -> E, AnalyticAt 𝕜 F 0 ∧
 forall z, f z = (∑ i in .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 
+ z ^ n • F z
参数：hf : AnalyticAt 𝕜 f 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul`：AnalyticAt.exists_eventu
allyEq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E] {f : 𝕜 -> E} (hf : Analyti
cAt 𝕜 f 0) (n : Nat) : exists F : 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `AnalyticAt.congr`：AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 
x] g) : AnalyticAt 𝕜 g x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pow_eq_zero_iff'`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} 
{n : ℕ} [IsReduced M₀] [Nontrivial M₀], a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
A version of **Taylor's theorem** for analytic functions in one variable, with t
he error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` for a version asserting eq
uality on a
neighbourhood of `0` rather than globally.)
-/
lemma AnalyticAt.exists_eq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) (n : ℕ) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F 0 ∧ ∀ z,
      f z = (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  classical
  obtain ⟨F, hFa, hF⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  obtain ⟨U, hU0, hU'⟩ := by rwa [eventually_iff_exists_mem] at hF
  refine ⟨fun z ↦ if z ∈ U then F z else (z ^ n)⁻¹ • (f z
      - (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0)), ?_, fun z ↦ ?_⟩
  · exact hFa.congr (by filter_upwards [hU0] using by simp +contextual)
  · by_cases hz : z ∈ U
    · simpa [hz] using hU' z hz
    · simp only [if_neg hz]
      rw [smul_inv_smul₀]
      · module
      · contrapose hz
        exact (pow_eq_zero_iff'.mp hz).1 ▸ mem_of_mem_nhds hU0

variable [CharZero 𝕜] [CompleteSpace E] {z₀ : 𝕜} {f : 𝕜 → E}
  (hf : AnalyticAt 𝕜 f z₀) (hzero : f z₀ = 0)

include hf hzero

/-- If an analytic function `f` vanishes at `z₀`, then the analytic order of its derivative
at `z₀` is at least `n` if and only if the analytic order of `f` at `z₀` is at least `n + 1`. -/
/-
**analyticOrderAt_deriv_ge_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_deriv_ge_iff {n : Nat} : n <= analyticOrderAt (deriv f) z₀
 ↔ n + 1 <= analyticOrderAt f z₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`：natCast_le_analyti
cOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [CompleteSpace E] (hf : Analytic
At 𝕜 f z₀) : n <= analyticOrderAt f z₀ ↔ f…
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f

--- 原说明 ---
If an analytic function `f` vanishes at `z₀`, then the analytic order of its der
ivative
at `z₀` is at least `n` if and only if the analytic order of `f` at `z₀` is at l
east `n + 1`.
-/
lemma analyticOrderAt_deriv_ge_iff {n : ℕ} :
    n ≤ analyticOrderAt (deriv f) z₀ ↔ n + 1 ≤ analyticOrderAt f z₀ := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf.deriv,
    ← Nat.cast_add_one, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [← iteratedDeriv_succ']
  refine ⟨fun h k hk ↦ ?_, fun h k hk ↦ h (k + 1) <| by lia⟩
  cases k with
  | zero => simpa
  | succ k => exact h k <| by lia

/-- The derivative of an analytic function `f` has infinite analytic order at a zero `z₀` if and
only if `f` has infinite analytic order at `z₀`. -/
/-
**analyticOrderAt_deriv_eq_top_iff_of_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_deriv_eq_top_iff_of_eq_zero : analyticOrderAt (deriv f) z₀
 = ⊤ ↔ analyticOrderAt f z₀ = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `analyticOrderAt_deriv_ge_iff`：analyticOrderAt_deriv_ge_iff {n : Nat} : n
 <= analyticOrderAt (deriv f) z₀ ↔ n + 1 <= analyticOrderAt f z₀
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞

--- 原说明 ---
The derivative of an analytic function `f` has infinite analytic order at a zero
 `z₀` if and
only if `f` has infinite analytic order at `z₀`.
-/
lemma analyticOrderAt_deriv_eq_top_iff_of_eq_zero :
    analyticOrderAt (deriv f) z₀ = ⊤ ↔ analyticOrderAt f z₀ = ⊤ := by
  simp_rw [ENat.eq_top_iff_forall_ge, analyticOrderAt_deriv_ge_iff hf hzero]
  exact ⟨fun h m ↦ le_self_add.trans (h m), fun h m ↦ h (m + 1)⟩

/-- If an analytic function `f` vanishes at `z₀`, then its derivative has finite analytic order `n`
at `z₀` if and only if `f` has analytic order `n + 1` at `z₀`. -/
/-
**analyticOrderAt_deriv_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_deriv_eq_iff {n : Nat} : analyticOrderAt f z₀ = n + 1 ↔ an
alyticOrderAt (deriv f) z₀ = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用引理 `analyticOrderAt_deriv_ge_iff`：analyticOrderAt_deriv_ge_iff {n : Nat} : n
 <= analyticOrderAt (deriv f) z₀ ↔ n + 1 <= analyticOrderAt f z₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If an analytic function `f` vanishes at `z₀`, then its derivative has finite ana
lytic order `n`
at `z₀` if and only if `f` has analytic order `n + 1` at `z₀`.
-/
lemma analyticOrderAt_deriv_eq_iff {n : ℕ} :
    analyticOrderAt f z₀ = n + 1 ↔ analyticOrderAt (deriv f) z₀ = n := by
  have H {m : ℕ} {n : ℕ∞} : n = m ↔ m ≤ n ∧ ¬ m + 1 ≤ n := by
    cases n with | top => simp | coe _ => norm_cast; lia
  rw [← Nat.cast_add_one n, H, H, analyticOrderAt_deriv_ge_iff hf hzero, ← Nat.cast_add_one n,
    analyticOrderAt_deriv_ge_iff hf hzero]

omit hzero in
/-- An analytic function `f` has finite analytic order `n` at `z₀` if and only if its first
`n` iterated derivatives (including `f` itself) vanish at `z₀` and the `n`-th iterated derivative is
non-zero. -/
/-
**analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero {n : Nat} : analyticOrder
At f z₀ = n ↔ (forall k < n, iteratedDeriv k f z₀ = 0) ∧ iteratedDeriv n f z₀ !=
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AnalyticAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {x…
· 使用引理 `analyticOrderAt_deriv_of_pos`：analyticOrderAt_deriv_of_pos {𝕜 : Type*} {
E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E] [Norm
edSpace 𝕜 E] [Comp…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.analyticOrderAt_ne_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Nat.cast_add_one_ne_zero`：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) !
= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `analyticOrderAt_deriv_eq_iff`：analyticOrderAt_deriv_eq_iff {n : Nat} : a
nalyticOrderAt f z₀ = n + 1 ↔ analyticOrderAt (deriv f) z₀ = n

--- 原说明 ---
An analytic function `f` has finite analytic order `n` at `z₀` if and only if it
s first
`n` iterated derivatives (including `f` itself) vanish at `z₀` and the `n`-th it
erated derivative is
non-zero.
-/
lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero {n : ℕ} :
    analyticOrderAt f z₀ = n ↔ (∀ k < n, iteratedDeriv k f z₀ = 0) ∧ iteratedDeriv n f z₀ ≠ 0 := by
  induction n generalizing f with
  | zero => simp [hf.analyticOrderAt_eq_zero]
  | succ n IH =>
    specialize IH hf.deriv
    simp_rw [← iteratedDeriv_succ'] at IH
    refine ⟨fun ho ↦ ?_, fun ⟨hz, hnz⟩ ↦ ?_⟩
    · have ⟨h_zero, h_nz⟩ := IH.mp (analyticOrderAt_deriv_of_pos hf ho)
      refine ⟨fun k hk ↦ ?_, h_nz⟩
      match k with
      | 0 => rw [iteratedDeriv_zero, ← hf.analyticOrderAt_ne_zero, ho, Nat.cast_add_one]
             exact Nat.cast_add_one_ne_zero _
      | k + 1 => exact h_zero k (by lia)
    · exact (analyticOrderAt_deriv_eq_iff hf <| by simpa using hz 0 (by lia)).mpr <|
        IH.mpr ⟨fun j _ ↦ hz (j + 1) (by lia), hnz⟩

end NormedSpace

/-!
## Vanishing Order at a Point: Elementary Computations
-/

/-- Simplifier lemma for the order of a centered monomial -/
@[simp]
/-
**analyticOrderAt_centeredMonomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_centeredMonomial {z₀ : 𝕜} {n : Nat} : analyticOrderAt ((· 
- z₀) ^ n) z₀ = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Simplifier lemma for the order of a centered monomial
-/
lemma analyticOrderAt_centeredMonomial {z₀ : 𝕜} {n : ℕ} :
    analyticOrderAt ((· - z₀) ^ n) z₀ = n := by
  rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)]
  exact ⟨1, by simp [Pi.one_def, analyticAt_const]⟩

/-- The analytic order of the function `(· - c)` at `x` is one if `x = c`. -/
/-
**analyticOrderAt_id_sub_const_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {c : 𝕜}, analyticOrder
At (fun x => x - c) c = 1
参数：fun x => x - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticOrderAt_centeredMonomial`：analyticOrderAt_centeredMonomial {z₀ :
 𝕜} {n : Nat} : analyticOrderAt ((· - z₀) ^ n) z₀ = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The analytic order of the function `(· - c)` at `x` is one if `x = c`.
-/
@[simp] theorem analyticOrderAt_id_sub_const_self {c : 𝕜} :
    analyticOrderAt (· - c) c = 1 := by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := c)
  simp_all [pow_one]

/-- The analytic order of the function `(· - c)` at `x` is zero if `x ≠ c`. -/
/-
**analyticOrderAt_id_sub_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {c x : 𝕜}, x ≠ c → ana
lyticOrderAt (fun x => x - c) x = 0
参数：fun x => x - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `analyticOrderAt_eq_zero`：analyticOrderAt_eq_zero : analyticOrderAt f z₀ 
= 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ != 0

--- 原说明 ---
The analytic order of the function `(· - c)` at `x` is zero if `x ≠ c`.
-/
@[simp] theorem analyticOrderAt_id_sub_const_of_ne {c x : 𝕜} (h : x ≠ c) :
    analyticOrderAt (· - c) x = 0 := by
  apply analyticOrderAt_eq_zero.2
  grind

section NontriviallyNormedField
variable {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-
**analyticOrderAt_mul_eq_top_of_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_mul_eq_top_of_left (hf : analyticOrderAt f z₀ = ⊤) : analy
ticOrderAt (f * g) z₀ = ⊤
参数：hf : analyticOrderAt f z₀ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticOrderAt_smul_eq_top_of_left`：analyticOrderAt_smul_eq_top_of_left
 {f : 𝕜 -> 𝕜} (hf : analyticOrderAt f z₀ = ⊤) : analyticOrderAt (f • g) z₀ = ⊤
-/
lemma analyticOrderAt_mul_eq_top_of_left (hf : analyticOrderAt f z₀ = ⊤) :
    analyticOrderAt (f * g) z₀ = ⊤ := analyticOrderAt_smul_eq_top_of_left hf
/-
**analyticOrderAt_mul_eq_top_of_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_mul_eq_top_of_right (hg : analyticOrderAt g z₀ = ⊤) : anal
yticOrderAt (f * g) z₀ = ⊤
参数：hg : analyticOrderAt g z₀ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticOrderAt_smul_eq_top_of_right`：analyticOrderAt_smul_eq_top_of_rig
ht {f : 𝕜 -> 𝕜} (hg : analyticOrderAt g z₀ = ⊤) : analyticOrderAt (f • g) z₀ = ⊤
-/
lemma analyticOrderAt_mul_eq_top_of_right (hg : analyticOrderAt g z₀ = ⊤) :
    analyticOrderAt (f * g) z₀ = ⊤ := analyticOrderAt_smul_eq_top_of_right hg

/-- The order is additive when multiplying analytic functions. -/
/-
**analyticOrderAt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : an
alyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀
参数：hf : AnalyticAt 𝕜 f z₀；hg : AnalyticAt 𝕜 g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticOrderAt_smul`：analyticOrderAt_smul {f : 𝕜 -> 𝕜} (hf : AnalyticAt
 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : analyticOrderAt (f • g) z₀ = analyticOrderAt
 f z₀ + an…

--- 原说明 ---
The order is additive when multiplying analytic functions.
-/
theorem analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ :=
  analyticOrderAt_smul hf hg

/-- The order is additive when multiplying analytic functions. -/
/-
**analyticOrderNatAt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOrderNatAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) (
hf' : analyticOrderAt f z₀ != ⊤) (hg' : analyticOrderAt g z₀ != ⊤) : analyticOrd
erNatAt (f * g) z₀ = analyticOrderNatAt f z₀ + analyticOrderNatAt g z₀
参数：hf : AnalyticAt 𝕜 f z₀；hg : AnalyticAt 𝕜 g z₀；hf' : analyticOrderAt f z₀ != ⊤
；hg' : analyticOrderAt g z₀ != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `analyticOrderAt_mul`：analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : 
AnalyticAt 𝕜 g z₀) : analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyti
cOrderAt …
· 使用定理 `ENat.toNat_add`：toNat_add {m n : Nat∞} (hm : m != ⊤) (hn : n != ⊤) : toN
at (m + n) = toNat m + toNat n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The order is additive when multiplying analytic functions.
-/
theorem analyticOrderNatAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hf' : analyticOrderAt f z₀ ≠ ⊤) (hg' : analyticOrderAt g z₀ ≠ ⊤) :
    analyticOrderNatAt (f * g) z₀ = analyticOrderNatAt f z₀ + analyticOrderNatAt g z₀ := by
  simp [analyticOrderNatAt, analyticOrderAt_mul, ENat.toNat_add, *]

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
/-
**analyticOrderAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {z₀ : 𝕜}, 
  AnalyticAt 𝕜 f z₀ → ∀ (n : ℕ), analyticOrderAt (f ^ n) z₀ = n • analyticOrderA
t f z₀
参数：n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order multiplies by `n` when taking an analytic function to its `n`th power.
-/
theorem analyticOrderAt_pow (hf : AnalyticAt 𝕜 f z₀) :
    ∀ n, analyticOrderAt (f ^ n) z₀ = n • analyticOrderAt f z₀
  | 0 => by simp [analyticOrderAt_eq_zero]
  | n + 1 => by simp [add_mul, pow_add, analyticOrderAt_mul (hf.pow n), analyticOrderAt_pow, hf]

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
/-
**analyticOrderNatAt_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOrderNatAt_pow (hf : AnalyticAt 𝕜 f z₀) (n : Nat) : analyticOrderN
atAt (f ^ n) z₀ = n • analyticOrderNatAt f z₀
参数：hf : AnalyticAt 𝕜 f z₀；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `analyticOrderAt_pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {f : 𝕜 → 𝕜} {z₀ : 𝕜},   AnalyticAt 𝕜 f z₀ → ∀ (n : ℕ), analyticOrderAt (f ^ n) 
z₀ = n • …
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `ENat.toNat_mul`：∀ (a b : ℕ∞), (a * b).toNat = a.toNat * b.toNat
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The order multiplies by `n` when taking an analytic function to its `n`th power.
-/
theorem analyticOrderNatAt_pow (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    analyticOrderNatAt (f ^ n) z₀ = n • analyticOrderNatAt f z₀ := by
  simp [analyticOrderNatAt, analyticOrderAt_pow, hf]

end NontriviallyNormedField

section comp

/-!
## Vanishing Order at a Point: Composition
-/
variable {f : 𝕜 → E} {g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- Analytic order of a composition of analytic functions. -/
/-
**AnalyticAt.analyticOrderAt_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g z₀)) (hg : Analyti
cAt 𝕜 g z₀) : analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) * analyticOr
derAt (g · - g z₀) z₀
参数：hf : AnalyticAt 𝕜 f (g z₀)；hg : AnalyticAt 𝕜 g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.comp`：comp (h : EventuallyConst f l) (g : β -> γ)
 : EventuallyConst (g ∘ f) l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eventuallyConst_iff_analyticOrderAt_sub_eq_top`：eventuallyConst_iff_anal
yticOrderAt_sub_eq_top : EventuallyConst f (𝓝 z₀) ↔ analyticOrderAt (f · - f z₀)
 z₀ = ⊤
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Filter.EventuallyEq.comp_tendsto`：Filter.EventuallyEq.comp_tendsto {l : 
Filter α} {f : α -> β} {f' : α -> β} (H : f =ᶠ[l] f') {g : γ -> α} {lc : Filter 
γ} (hg : Tendsto g lc …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ENat.top_mul`：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
· 使用定理 `AnalyticAt.analyticOrderAt_ne_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `AnalyticAt.fun_sub`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `ENat.ne_top_iff_exists`：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m 
= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_mul`：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
· 使用引理 `AnalyticAt.analyticOrderAt_eq_natCast`：AnalyticAt.analyticOrderAt_eq_nat
Cast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ exists (g : 𝕜 -> E), 
AnalyticAt 𝕜 g z₀ ∧ g z₀ !=…
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AnalyticAt.fun_smul`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 …
· 使用定理 `AnalyticAt.fun_pow`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {A :
 Type u_…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Analytic order of a composition of analytic functions.
-/
lemma AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) * analyticOrderAt (g · - g z₀) z₀ := by
  by_cases hg_nc : EventuallyConst g (𝓝 z₀)
  · -- If `g` is eventually constant, both sides are either `⊤` or `0`.
    have := hg_nc.comp f
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc this
    rw [hg_nc]
    by_cases hf' : f (g z₀) = 0
    · simpa [hf', show analyticOrderAt f (g z₀) ≠ 0 by grind [analyticOrderAt_ne_zero]]
    · rw [show analyticOrderAt f (g z₀) = 0 from ?_, zero_mul] <;>
      grind [hf.comp hg, AnalyticAt.analyticOrderAt_eq_zero]
  by_cases hf' : analyticOrderAt f (g z₀) = ⊤
  · -- If `f` is eventually constant but `g` is not, we have `⊤ = ⊤ * (non-zero thing)`
    rw [hf', analyticOrderAt_eq_top.mpr
      (EventuallyEq.comp_tendsto (analyticOrderAt_eq_top.mp hf') hg.continuousAt), ENat.top_mul]
    rw [AnalyticAt.analyticOrderAt_ne_zero (by fun_prop), sub_eq_zero]
  · -- The interesting case: both orders are finite. First unpack the data:
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hf'
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hg_nc
    rw [← hr, ← hs, ← ENat.natCast_mul, (hf.comp hg).analyticOrderAt_eq_natCast]
    rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hr
    rcases hr with ⟨F, hFa, hFne, hfF⟩
    rw [Eq.comm, AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)] at hs
    rcases hs with ⟨G, hGa, hGne, hgG⟩
    -- Now write `f ∘ g` locally as the product of `(z - z₀) ^ (r * s)` and the
    -- non-vanishing analytic function `fun z ↦ (G z) ^ r • F (g z)`.
    refine ⟨fun z ↦ (G z) ^ r • F (g z), by fun_prop, by aesop, ?_⟩
    filter_upwards [EventuallyEq.comp_tendsto hfF hg.continuousAt, hgG] with z hfz hgz
    simp only [hfz, Function.comp_def, hgz, smul_eq_mul, mul_pow, mul_smul, mul_comm r s, pow_mul]

/-- If `g` is analytic at `x`, and `g' x ≠ 0`, then the analytic order of
`f ∘ g` at `x` is the analytic order of `f` at `g x` (even if `f` is not analytic). -/
/-
**analyticOrderAt_comp_of_deriv_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g z₀) (hg' : deri
v g z₀ != 0) [CompleteSpace 𝕜] [CharZero 𝕜] : analyticOrderAt (f ∘ g) z₀ = analy
ticOrderAt f (g z₀)
参数：hg : AnalyticAt 𝕜 g z₀；hg' : deriv g z₀ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AnalyticAt.analyticOrderAt_comp`：AnalyticAt.analyticOrderAt_comp (hf : A
nalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀) : analyticOrderAt (f ∘ g) z₀ = an
alyticOrderAt f (g z₀…
· 使用定理 `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`：AnalyticAt.analy
ticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hf' : de
riv f x != 0) : analyticOrderAt (f · - f x) …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `analyticOrderAt_of_not_analyticAt`：analyticOrderAt_of_not_analyticAt (hf
 : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0
· 使用引理 `analyticAt_comp_iff_of_deriv_ne_zero`：analyticAt_comp_iff_of_deriv_ne_ze
ro (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0) : AnalyticAt 𝕜 (g ∘ f) x ↔ Ana
lyticAt 𝕜 g (f x)

--- 原说明 ---
If `g` is analytic at `x`, and `g' x ≠ 0`, then the analytic order of
`f ∘ g` at `x` is the analytic order of `f` at `g x` (even if `f` is not analyti
c).
-/
lemma analyticOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g z₀) (hg' : deriv g z₀ ≠ 0)
    [CompleteSpace 𝕜] [CharZero 𝕜] :
    analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) := by
  by_cases hf : AnalyticAt 𝕜 f (g z₀)
  · simp [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg']
  · rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt]
    rwa [analyticAt_comp_iff_of_deriv_ne_zero hg hg']

end comp

/-!
## Level Sets of the Order Function
-/

namespace AnalyticOnNhd

variable {U : Set 𝕜} {f : 𝕜 → E}

/-- The set where an analytic function has infinite order is clopen in its domain of analyticity. -/
/-
**AnalyticOnNhd.isClopen_setOfPred_analyticOrderAt_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `AnalyticOnNhd`。
形式化陈述：isClopen_setOfPred_analyticOrderAt_eq_top (hf : AnalyticOnNhd 𝕜 f U) : IsC
lopen {u : U | analyticOrderAt f u = ⊤}
参数：hf : AnalyticOnNhd 𝕜 f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`：eventually_eq_zero_
or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ∨ 
forallᶠ z in 𝓝[!=] z₀, f z != 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `ENat.zero_ne_top`：0 ≠ ⊤
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
The set where an analytic function has infinite order is clopen in its domain of
 analyticity.
-/
theorem isClopen_setOfPred_analyticOrderAt_eq_top (hf : AnalyticOnNhd 𝕜 f U) :
    IsClopen {u : U | analyticOrderAt f u = ⊤} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← analyticOrderAt_eq_top] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ ∈ _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [(hf _ w.2).analyticOrderAt_eq_zero.2 ((h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w))]
          exact ENat.zero_ne_top
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [analyticOrderAt_eq_top, eventually_nhds_iff]
    simp only [mem_ofPred_eq] at hz
    rw [analyticOrderAt_eq_top, eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [isOpen_induced h₂t', mem_preimage, h₃t', and_self, and_true]
    grind

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_analyticOrderAt_eq_top := isClopen_setOfPred_analyticOrderAt_eq_top

/-- On a connected set, there exists a point where a meromorphic function `f` has finite order iff
`f` has finite order at every point. -/
/-
**AnalyticOnNhd.exists_analyticOrderAt_ne_top_iff_forall** 是 Mathlib 中的一个定理，位于命名
空间 `AnalyticOnNhd`。
形式化陈述：exists_analyticOrderAt_ne_top_iff_forall (hf : AnalyticOnNhd 𝕜 f U) (hU : 
IsConnected U) : (exists u : U, analyticOrderAt f u != ⊤) ↔ (forall u : U, analy
ticOrderAt f u != ⊤)
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsConnected U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.connectedSpace`：Subtype.connectedSpace {s : Set α} (h : IsConnec
ted s) : ConnectedSpace s where toPreconnectedSpace
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff`：isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen 
s ↔ s = ∅ ∨ s = univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `AnalyticOnNhd.isClopen_setOfPred_analyticOrderAt_eq_top`：isClopen_setOfP
red_analyticOrderAt_eq_top (hf : AnalyticOnNhd 𝕜 f U) : IsClopen {u : U | analyt
icOrderAt f u = ⊤}

--- 原说明 ---
On a connected set, there exists a point where a meromorphic function `f` has fi
nite order iff
`f` has finite order at every point.
-/
theorem exists_analyticOrderAt_ne_top_iff_forall (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U) :
    (∃ u : U, analyticOrderAt f u ≠ ⊤) ↔ (∀ u : U, analyticOrderAt f u ≠ ⊤) := by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (∀ (u : U), analyticOrderAt f u ≠ ⊤) ∨ ∀ (u : U), analyticOrderAt f u = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf.isClopen_setOfPred_analyticOrderAt_eq_top

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
/-
**AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected** 是 Mathlib 中的一个定理，位于命名
空间 `AnalyticOnNhd`。
形式化陈述：analyticOrderAt_ne_top_of_isPreconnected {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f
 U) (hU : IsPreconnected U) (h₁x : x in U) (hy : y in U) (h₂x : analyticOrderAt 
f x != ⊤) : analyticOrderAt f y != ⊤
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsPreconnected U；h₁x : x in U；hy : y in U；h₂x :
 analyticOrderAt f x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AnalyticOnNhd.exists_analyticOrderAt_ne_top_iff_forall`：exists_analyticO
rderAt_ne_top_iff_forall (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U) : (exis
ts u : U, analyticOrderAt f u != ⊤) ↔ (foral…
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty

--- 原说明 ---
On a preconnected set, a meromorphic function has finite order at one point if i
t has finite
order at another point.
-/
theorem analyticOrderAt_ne_top_of_isPreconnected {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U) (h₂x : analyticOrderAt f x ≠ ⊤) :
    analyticOrderAt f y ≠ ⊤ :=
  (hf.exists_analyticOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩)
    ⟨y, hy⟩

/-- The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity. -/
/-
**AnalyticOnNhd.codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top** 是 Mathlib 
中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 
f U) : {u : U | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} in Filter.cod
iscrete U
参数：hf : AnalyticOnNhd 𝕜 f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`：eventually_eq_zero_
or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ∨ 
forallᶠ z in 𝓝[!=] z₀, f z != 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The set where an analytic function has zero or infinite order is discrete within
 its domain of
analyticity.
-/
theorem codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : U | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} ∈ Filter.codiscrete U := by
  simp_rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin,
    disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_analyticOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top

/--
The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity.
-/
/-
**AnalyticOnNhd.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top** 是 Ma
thlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOn
Nhd 𝕜 f U) : {u : 𝕜 | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} in codi
screteWithin U
参数：hf : AnalyticOnNhd 𝕜 f U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`：eventually_eq_zero_
or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ∨ 
forallᶠ z in 𝓝[!=] z₀, f z != 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `Filter.Eventually.eventually_nhds`：Filter.Eventually.eventually_nhds {p 
: X -> Prop} (h : forallᶠ y in 𝓝 x, p y) : forallᶠ y in 𝓝 x, forallᶠ x in 𝓝 y, p
 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The set where an analytic function has zero or infinite order is discrete within
 its domain of
analyticity.
-/
theorem codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : 𝕜 | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} ∈ codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top

/--
If an analytic function `f` is not constantly zero on a connected set `U`, then its set of zeros is
codiscrete within `U`.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement in preimages of
codiscrete sets.
-/
/-
**AnalyticOnNhd.preimage_zero_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 `An
alyticOnNhd`。
形式化陈述：preimage_zero_mem_codiscreteWithin {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂
f : f x != 0) (hx : x in U) (hU : IsConnected U) : f ⁻¹' {0}ᶜ in codiscreteWithi
n U
参数：h₁f : AnalyticOnNhd 𝕜 f U；h₂f : f x != 0；hx : x in U；hU : IsConnected U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`：eqOn_zero
_or_eventually_ne_zero_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) : EqOn f 0 U ∨ forallᶠ x in codiscreteWit…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s

--- 原说明 ---
If an analytic function `f` is not constantly zero on a connected set `U`, then 
its set of zeros is
codiscrete within `U`.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement i
n preimages of
codiscrete sets.
-/
theorem preimage_zero_mem_codiscreteWithin {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x ≠ 0)
    (hx : x ∈ U) (hU : IsConnected U) :
    f ⁻¹' {0}ᶜ ∈ codiscreteWithin U := by
  rcases h₁f.eqOn_zero_or_eventually_ne_zero_of_preconnected hU.isPreconnected with hzero | hne
  · exact (h₂f (hzero hx)).elim
  · exact hne

/--
If an analytic function `f` is not constantly zero on `𝕜`, then its set of zeros is codiscrete.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement in preimages of
codiscrete sets.
-/
/-
**AnalyticOnNhd.preimage_zero_mem_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 `Analytic
OnNhd`。
形式化陈述：preimage_zero_mem_codiscrete [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNh
d 𝕜 f Set.univ) (hx : f x != 0) : f ⁻¹' {0}ᶜ in codiscrete 𝕜
参数：hf : AnalyticOnNhd 𝕜 f Set.univ；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`：preimage_zero_mem_codi
screteWithin {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x != 0) (hx : x in U) 
(hU : IsConnected U) : f ⁻¹' {0}ᶜ in c…
· 使用定理 `trivial`：True
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)

--- 原说明 ---
If an analytic function `f` is not constantly zero on `𝕜`, then its set of zeros
 is codiscrete.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement i
n preimages of
codiscrete sets.
-/
theorem preimage_zero_mem_codiscrete [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f Set.univ)
    (hx : f x ≠ 0) :
    f ⁻¹' {0}ᶜ ∈ codiscrete 𝕜 :=
  hf.preimage_zero_mem_codiscreteWithin hx trivial isConnected_univ
/-
**AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `An
alyticOnNhd`。
形式化陈述：analyticOrderAt_eq_top_iff_eq_zero [PreconnectedSpace 𝕜] {f : 𝕜 -> E} (z :
 𝕜) (hf : forall z₀, AnalyticAt 𝕜 f z₀) : analyticOrderAt f z = ⊤ ↔ f = 0
参数：z : 𝕜；hf : forall z₀, AnalyticAt 𝕜 f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `analyticOrderAt_eq_top`：analyticOrderAt_eq_top : analyticOrderAt f z₀ = 
⊤ ↔ forallᶠ z in 𝓝 z₀, f z = 0 where mp hf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eqOn_univ`：eqOn_univ (f₁ f₂ : α -> β) : EqOn f₁ f₂ univ ↔ f₁ = f₂
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`：eqOn_zero
_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] …
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AnalyticAt.frequently_eq_iff_eventually_eq`：frequently_eq_iff_eventually
_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : (existsᶠ z in 𝓝[!=] z₀, 
f z = g z) ↔ forallᶠ z in 𝓝 z₀, …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma analyticOrderAt_eq_top_iff_eq_zero [PreconnectedSpace 𝕜] {f : 𝕜 → E} (z : 𝕜)
    (hf : ∀ z₀, AnalyticAt 𝕜 f z₀) : analyticOrderAt f z = ⊤ ↔ f = 0 := by
  refine analyticOrderAt_eq_top.trans ⟨fun h ↦ eqOn_univ .. |>.mp ?_, by simp +contextual⟩
  apply eqOn_zero_of_preconnected_of_frequently_eq_zero (fun z _ ↦ hf z) isPreconnected_univ trivial
  exact hf z |>.frequently_eq_iff_eventually_eq analyticAt_const |>.mpr h
/-
**AnalyticOnNhd._root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero** 是 Ma
thlib 中的一个引理，位于命名空间 `AnalyticOnNhd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero {s : Set 𝕜} (hs : IsOpen s)
    (f : 𝕜 → E) : (∀ z ∈ s, analyticOrderAt f z = ⊤) ↔ EqOn f 0 s := by
  refine ⟨(EventuallyEq.eq_of_nhds <| analyticOrderAt_eq_top.mp <| · · ·), fun hzero z hz ↦ ?_⟩
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hs.mem_nhds hz]
  exact fun _ ↦ hzero.eq_of_mem

end AnalyticOnNhd

