/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points; exact formulae involving the
Euler-Mascheroni constant will follow in a subsequent PR.

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`

For special-value formulae expressing `ζ (2 * k)` and `ζ (1 - 2 * k)` in terms of Bernoulli numbers
see `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`. For computation of the constant term as
`s → 1`, see `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`.
-/

@[expose] public section


open CharZero Set Filter HurwitzZeta

open Complex hiding exp continuous_exp

open scoped Topology Real

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
/-
**completedRiemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completedRiemannZeta (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / 
(s - 1)`.
-/
def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
/-
**completedRiemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completedRiemannZeta (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`).
-/
def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s
/-
**HurwitzZeta.completedHurwitzZetaEven_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HurwitzZeta.completedHurwitzZetaEven_zero (s : Complex) : completedHurwitz
ZetaEven 0 s = completedRiemannZeta s
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ) :
    completedHurwitzZetaEven 0 s = completedRiemannZeta s := rfl
/-
**HurwitzZeta.completedHurwitzZetaEven** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedHurwitzZetaEven (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := rfl
/-
**HurwitzZeta.completedCosZeta_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HurwitzZeta.completedCosZeta_zero (s : Complex) : completedCosZeta 0 s = c
ompletedRiemannZeta s
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completedRiemannZeta.eq_1`：∀ (s : ℂ), completedRiemannZeta s = HurwitzZe
ta.completedHurwitzZetaEven 0 s
· 使用定理 `HurwitzZeta.completedHurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle) (s : ℂ)
,   HurwitzZeta.completedHurwitzZetaEven a s = (HurwitzZeta.hurwitzEvenFEPair a)
.Λ (s / 2) / 2
· 使用定理 `HurwitzZeta.completedCosZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), Hurwit
zZeta.completedCosZeta a s = (HurwitzZeta.hurwitzEvenFEPair a).symm.Λ (s / 2) / 
2
· 使用引理 `HurwitzZeta.hurwitzEvenFEPair_zero_symm`：hurwitzEvenFEPair_zero_symm : (
hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0
-/
lemma HurwitzZeta.completedCosZeta_zero (s : ℂ) :
    completedCosZeta 0 s = completedRiemannZeta s := by
  rw [completedRiemannZeta, completedHurwitzZetaEven, completedCosZeta, hurwitzEvenFEPair_zero_symm]
/-
**HurwitzZeta.completedCosZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, completedCosZeta₀,
    hurwitzEvenFEPair_zero_symm]
/-
**completedRiemannZeta_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completedRiemannZeta_eq (s : Complex) : completedRiemannZeta s = completed
RiemannZeta₀ s - 1 / s - 1 / (1 - s)
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_eq`：completedHurwitzZetaEven_eq (a 
: UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a s = completedHurwitz
ZetaEven₀ a s - (if a = 0 the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
-/
lemma completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s + 1 / (1 - s)` is entire. -/
/-
**differentiable_completedZeta** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modified completed Riemann zeta function `Λ(s) + 1 / s + 1 / (1 - s)` is ent
ire.
-/
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`. -/
/-
**differentiableAt_completedZeta** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_completedZeta {s : Complex} (hs : s != 0) (hs' : s != 1) 
: DifferentiableAt Complex completedRiemannZeta s
参数：hs : s != 0；hs' : s != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HurwitzZeta.differentiableAt_completedHurwitzZetaEven`：differentiableAt_
completedHurwitzZetaEven (a : UnitAddCircle) {s : Complex} (hs : s != 0 ∨ a != 0
) (hs' : s != 1) : DifferentiableAt Complex…

--- 原说明 ---
The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` a
nd `s = 1`.
-/
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
/-
**completedRiemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completedRiemannZeta (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we ha
ve
`Λ₀(1 - s) = Λ₀ s`.
-/
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
/-
**completedRiemannZeta_one_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completedRiemannZeta_one_sub (s : Complex) : completedRiemannZeta (1 - s) 
= completedRiemannZeta s
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_zero`：HurwitzZeta.completedHurwitzZ
etaEven_zero (s : Complex) : completedHurwitzZetaEven 0 s = completedRiemannZeta
 s
· 使用引理 `HurwitzZeta.completedCosZeta_zero`：HurwitzZeta.completedCosZeta_zero (s 
: Complex) : completedCosZeta 0 s = completedRiemannZeta s
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_one_sub`：completedHurwitzZetaEven_o
ne_sub (a : UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a (1 - s) = 
completedCosZeta a s

--- 原说明 ---
Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we hav
e
`Λ (1 - s) = Λ s`.
-/
theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]

/-- The residue of `Λ(s)` at `s = 1` is equal to `1`. -/
/-
**completedRiemannZeta_residue_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completedRiemannZeta_residue_one : Tendsto (fun s => (s - 1) * completedRi
emannZeta s) (𝓝[!=] 1) (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_residue_one`：completedHurwitzZetaEv
en_residue_one (a : UnitAddCircle) : Tendsto (fun s => (s - 1) * completedHurwit
zZetaEven a s) (𝓝[!=] 1) (𝓝 1)

--- 原说明 ---
The residue of `Λ(s)` at `s = 1` is equal to `1`.
-/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. -/
@[wikidata Q187235]
/-
**riemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZeta
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Riemann zeta function `ζ(s)`.
-/
def riemannZeta := hurwitzZetaEven 0
/-
**HurwitzZeta.hurwitzZetaEven_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl
/-
**HurwitzZeta.cosZeta_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.completedCosZeta_zero`：HurwitzZeta.completedCosZeta_zero (s 
: Complex) : completedCosZeta 0 s = completedRiemannZeta s
-/
lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]
/-
**HurwitzZeta.hurwitzZeta_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `HurwitzZeta.hurwitzZetaOdd_neg`：hurwitzZetaOdd_neg (a : UnitAddCircle) (
s : Complex) : hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s
-/
lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s
/-
**HurwitzZeta.expZeta_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.expZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.exp
Zeta a s = HurwitzZeta.cosZeta a s + Complex.I * HurwitzZeta.sinZeta a s
· 使用引理 `HurwitzZeta.cosZeta_zero`：HurwitzZeta.cosZeta_zero : cosZeta 0 = riemann
Zeta
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `eq_false_intro`：eq_false_intro {a : Prop} (h : ¬a) : a = False
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharZero.eq_neg_self_iff`：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZe
roDivisors R] [CharZero R] {a : R}, a = -a ↔ a = 0
· 使用引理 `HurwitzZeta.sinZeta_neg`：sinZeta_neg (a : UnitAddCircle) (s : Complex) :
 sinZeta (-a) s = -sinZeta a s
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
  ext1 s
  rw [expZeta, cosZeta_zero, add_eq_left, mul_eq_zero, eq_false_intro I_ne_zero, false_or,
    ← eq_neg_self_iff, ← sinZeta_neg, neg_zero]

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
/-
**differentiableAt_riemannZeta** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_riemannZeta {s : Complex} (hs' : s != 1) : Differentiable
At Complex riemannZeta s
参数：hs' : s != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZetaEven`：differentiableAt_hurwitzZe
taEven (a : UnitAddCircle) {s : Complex} (hs' : s != 1) : DifferentiableAt Compl
ex (hurwitzZetaEven a) s

--- 原说明 ---
The Riemann zeta function is differentiable away from `s = 1`.
-/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_hurwitzZetaEven _ hs'
/-
**differentiableOn_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableOn_riemannZeta : DifferentiableOn Complex riemannZeta {1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_riemannZeta`：differentiableAt_riemannZeta {s : Complex}
 (hs' : s != 1) : DifferentiableAt Complex riemannZeta s
-/
lemma differentiableOn_riemannZeta :
    DifferentiableOn ℂ riemannZeta {1}ᶜ :=
  fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt
/-
**analyticOn_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_riemannZeta : AnalyticOnNhd Complex riemannZeta {1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `differentiableOn_riemannZeta`：differentiableOn_riemannZeta : Differentia
bleOn Complex riemannZeta {1}ᶜ
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma analyticOn_riemannZeta :
    AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton

/-- We have `ζ(0) = -1 / 2`. -/
/-
**riemannZeta_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_zero : riemannZeta 0 = -1 / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t

--- 原说明 ---
We have `ζ(0) = -1 / 2`.
-/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_self, if_true]
/-
**riemannZeta_def_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_def_of_ne_zero {s : Complex} (hs : s != 0) : riemannZeta s = c
ompletedRiemannZeta s / GammaReal s
参数：hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `riemannZeta.eq_1`：riemannZeta = HurwitzZeta.hurwitzZetaEven 0
· 使用定理 `HurwitzZeta.hurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.h
urwitzZetaEven a =     Function.update (fun s => HurwitzZeta.completedHurwitzZet
aEven a s / s.Gammaℝ) …
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_zero`：HurwitzZeta.completedHurwitzZ
etaEven_zero (s : Complex) : completedHurwitzZetaEven 0 s = completedRiemannZeta
 s
-/
lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
  rw [riemannZeta, hurwitzZetaEven, Function.update_of_ne hs, completedHurwitzZetaEven_zero]

/-- Definition of the zeta function in terms of `completedRiemannZeta₀`. -/
/-
**riemannZeta_eq_completedRiemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of the zeta function in terms of `completedRiemannZeta₀`.
-/
lemma riemannZeta_eq_completedRiemannZeta₀ {s : ℂ} (hs : s ≠ 0) : riemannZeta s =
    (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) / (π ^ (-s / 2) * Gamma (s / 2)) := by
  rw [riemannZeta_def_of_ne_zero hs, completedRiemannZeta_eq, Gammaℝ]

/-- Version of `completedRiemannZeta₀` that avoids `s ≠ 0` -/
/-
**riemannZeta_eq_mul_completedRiemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `completedRiemannZeta₀` that avoids `s ≠ 0`
-/
lemma riemannZeta_eq_mul_completedRiemannZeta₀ (s : ℂ) :
    riemannZeta s = (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
      (2 * π ^ (-s / 2) * Gamma (s / 2 + 1)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [riemannZeta_zero]
  · rw [riemannZeta_eq_completedRiemannZeta₀ hs, Gamma_add_one (s / 2) (by grind)]
    field

/-- The trivial zeroes of the zeta function. -/
/-
**riemannZeta_neg_two_mul_nat_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_neg_two_mul_nat_add_one (n : Nat) : riemannZeta (-2 * (n + 1))
 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HurwitzZeta.hurwitzZetaEven_neg_two_mul_nat_add_one`：hurwitzZetaEven_neg
_two_mul_nat_add_one (a : UnitAddCircle) (n : Nat) : hurwitzZetaEven a (-2 * (n 
+ 1)) = 0

--- 原说明 ---
The trivial zeroes of the zeta function.
-/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

/-- Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we have
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`. -/
/-
**riemannZeta_one_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_one_sub {s : Complex} (hs : forall n : Nat, s != -n) (hs' : s 
!= 1) : riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * r
iemannZeta s
参数：hs : forall n : Nat, s != -n；hs' : s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `riemannZeta.eq_1`：riemannZeta = HurwitzZeta.hurwitzZetaEven 0
· 使用引理 `HurwitzZeta.hurwitzZetaEven_one_sub`：hurwitzZetaEven_one_sub (a : UnitAd
dCircle) {s : Complex} (hs : forall (n : Nat), s != -n) (hs' : a != 0 ∨ s != 1) 
: hurwitzZetaEven a (1 - …
· 使用引理 `HurwitzZeta.cosZeta_zero`：HurwitzZeta.cosZeta_zero : cosZeta 0 = riemann
Zeta
· 使用引理 `HurwitzZeta.hurwitzZetaEven_zero`：HurwitzZeta.hurwitzZetaEven_zero : hur
witzZetaEven 0 = riemannZeta

--- 原说明 ---
Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we ha
ve
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`.
-/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta, hurwitzZetaEven_one_sub 0 hs (Or.inr hs'), cosZeta_zero, hurwitzZetaEven_zero]

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
@[wikidata Q205966]
/-
**RiemannHypothesis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RiemannHypothesis : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A formal statement of the **Riemann hypothesis** – constructing a term of this t
ype is worth a
million dollars.
-/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2

/-!
## Relating the Mellin transform to the Dirichlet series
-/

/-
**completedZeta_eq_tsum_of_one_lt_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completedZeta_eq_tsum_of_one_lt_re {s : Complex} (hs : 1 < re s) : complet
edRiemannZeta s = (π : Complex) ^ (-s / 2) * Gamma (s / 2) * ∑' n : Nat, 1 / (n 
: Complex) ^ s
参数：hs : 1 < re s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HurwitzZeta.hasSum_nat_completedCosZeta`：hasSum_nat_completedCosZeta (a 
: Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Nat => if n = 0 then 0 e
lse GammaReal s * Real.cos (2…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HurwitzZeta.completedCosZeta_zero`：HurwitzZeta.completedCosZeta_zero (s 
: Complex) : completedCosZeta 0 s = completedRiemannZeta s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
## Relating the Mellin transform to the Dirichlet series
-/
theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta s =
      (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, Gammaℝ_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp only [h, Nat.cast_zero, zero_cpow (Complex.ne_zero_of_one_lt_re hs), div_zero]
  · rfl

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
/-
**zeta_eq_tsum_one_div_nat_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zeta_eq_tsum_one_div_nat_cpow {s : Complex} (hs : 1 < re s) : riemannZeta 
s = ∑' n : Nat, 1 / (n : Complex) ^ s
参数：hs : 1 < re s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `HurwitzZeta.cosZeta_zero`：HurwitzZeta.cosZeta_zero : cosZeta 0 = riemann
Zeta
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HurwitzZeta.hasSum_nat_cosZeta`：hasSum_nat_cosZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.cos (2 * π * a * n) / (n : Com
plex) ^ s) (cosZeta …

--- 原说明 ---
The Riemann zeta function agrees with the naive Dirichlet-series definition when
 the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the 
sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`
.)
-/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

/-- Alternate formulation of `zeta_eq_tsum_one_div_nat_cpow` with a `+ 1` (to avoid relying
on mathlib's conventions for `0 ^ s`). -/
/-
**zeta_eq_tsum_one_div_nat_add_one_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zeta_eq_tsum_one_div_nat_add_one_cpow {s : Complex} (hs : 1 < re s) : riem
annZeta s = ∑' n : Nat, 1 / (n + 1 : Complex) ^ s
参数：hs : 1 < re s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zeta_eq_tsum_one_div_nat_cpow`：zeta_eq_tsum_one_div_nat_cpow {s : Comple
x} (hs : 1 < re s) : riemannZeta s = ∑' n : Nat, 1 / (n : Complex) ^ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Summable.tsum_eq_zero_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [ins
t_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, S
ummable f → ∑' …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用引理 `Complex.summable_one_div_nat_cpow`：Complex.summable_one_div_nat_cpow {p 
: Complex} : Summable (fun n : Nat => 1 / (n : Complex) ^ p) ↔ 1 < re p

--- 原说明 ---
Alternate formulation of `zeta_eq_tsum_one_div_nat_cpow` with a `+ 1` (to avoid 
relying
on mathlib's conventions for `0 ^ s`).
-/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [Summable.tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
/-
**zeta_nat_eq_tsum_of_gt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zeta_nat_eq_tsum_of_gt_one {k : Nat} (hk : 1 < k) : riemannZeta k = ∑' n :
 Nat, 1 / (n : Complex) ^ k
参数：hk : 1 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zeta_eq_tsum_one_div_nat_cpow`：zeta_eq_tsum_one_div_nat_cpow {s : Comple
x} (hs : 1 < re s) : riemannZeta s = ∑' n : Nat, 1 / (n : Complex) ^ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so 
the power
function can be expressed using naïve `pow` rather than `cpow`.
-/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]
/-
**two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : Nat} (hk : 2 <= k) (h
k2 : Even k) : 2 * riemannZeta k = ∑' (n : Int), ((n : Complex) ^ k)⁻¹
参数：hk : 2 <= k；hk2 : Even k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 77 条，此处仅展示前 30 条）
-/
lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) :
    2 * riemannZeta k = ∑' (n : ℤ), ((n : ℂ) ^ k)⁻¹ := by
  have hkk : 1 < k := by linarith
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have h0 : (0 ^ k : ℂ)⁻¹ = 0 := by simp; lia
    norm_cast
    simp [h0, zeta_eq_tsum_one_div_nat_add_one_cpow (s := k) (by simp [hkk]),
      tsum_pnat_eq_tsum_succ (f := fun n => ((n : ℂ) ^ k)⁻¹)]
  · intro n
    simp [Even.neg_pow hk2]
  · exact (Summable.of_nat_of_neg (by simp [hkk]) (by simp [hkk])).of_norm

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
/-
**riemannZeta_residue_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_residue_one : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[!=
] 1) (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HurwitzZeta.hurwitzZetaEven_residue_one`：hurwitzZetaEven_residue_one (a 
: UnitAddCircle) : Tendsto (fun s => (s - 1) * hurwitzZetaEven a s) (𝓝[!=] 1) (𝓝
 1)

--- 原说明 ---
The residue of `ζ(s)` at `s = 1` is equal to 1.
-/
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  exact hurwitzZetaEven_residue_one 0

/-- The residue of `ζ(s)` at `s = 1` is equal to 1, expressed using `tsum`. -/
/-
**tendsto_sub_mul_tsum_nat_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_sub_mul_tsum_nat_cpow : Tendsto (fun s : Complex => (s - 1) * ∑' (
n : Nat), 1 / (n : Complex) ^ s) (𝓝[{s | 1 < re s}] 1) (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `zeta_eq_tsum_one_div_nat_cpow`：zeta_eq_tsum_one_div_nat_cpow {s : Comple
x} (hs : 1 < re s) : riemannZeta s = ∑' n : Nat, 1 / (n : Complex) ^ s
· 使用定理 `tendsto_nhdsWithin_mono_left`：tendsto_nhdsWithin_mono_left {f : α -> β} 
{a : α} {s t : Set α} {l : Filter β} (hst : s subseteq t) (h : Tendsto f (𝓝[t] a
) l) : Tendsto f (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `riemannZeta_residue_one`：riemannZeta_residue_one : Tendsto (fun s => (s 
- 1) * riemannZeta s) (𝓝[!=] 1) (𝓝 1)

--- 原说明 ---
The residue of `ζ(s)` at `s = 1` is equal to 1, expressed using `tsum`.
-/
theorem tendsto_sub_mul_tsum_nat_cpow :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℂ) ^ s) (𝓝[{s | 1 < re s}] 1) (𝓝 1) := by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
      congr_arg _ <| zeta_eq_tsum_one_div_nat_cpow hs

/-- The residue of `ζ(s)` at `s = 1` is equal to 1 expressed using `tsum` and for a
real variable. -/
/-
**tendsto_sub_mul_tsum_nat_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_sub_mul_tsum_nat_rpow : Tendsto (fun s : Real => (s - 1) * ∑' (n :
 Nat), 1 / (n : Real) ^ s) (𝓝[>] 1) (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_ofReal_iff`：∀ {α : Type u_2} {l : Filter α} {f : α → ℝ} {
x : ℝ},   Filter.Tendsto (fun x => ↑(f x)) l (nhds ↑x) ↔ Filter.Tendsto f l (nhd
s x)
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_sub_mul_tsum_nat_cpow`：tendsto_sub_mul_tsum_nat_cpow : Tendsto (
fun s : Complex => (s - 1) * ∑' (n : Nat), 1 / (n : Complex) ^ s) (𝓝[{s | 1 < re
 s}] 1) (𝓝 1)

--- 原说明 ---
The residue of `ζ(s)` at `s = 1` is equal to 1 expressed using `tsum` and for a
real variable.
-/
theorem tendsto_sub_mul_tsum_nat_rpow :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℝ) ^ s) (𝓝[>] 1) (𝓝 1) := by
  rw [← tendsto_ofReal_iff, ofReal_one]
  have : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ ↦ by simp_all)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s ↦ ?_
  simp only [one_div, Function.comp_apply, ofReal_mul, ofReal_sub, ofReal_one, ofReal_tsum,
    ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
