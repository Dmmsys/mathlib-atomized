/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial), and
similarly for completed L-functions.

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.
* `rootNumber`: the global root number of the L-series of `χ` (for `χ` primitive; junk otherwise).

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `IsPrimitive.completedLFunction_one_sub`: the **functional equation** for Dirichlet L-functions,
  showing that if `χ` is primitive modulo `N`, then
  `completedLFunction χ s = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
-/

@[expose] public section

open HurwitzZeta Complex Finset ZMod Filter

open scoped Real Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
-/
@[pp_nodot]
/-
**DirichletCharacter.LFunction** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：LFunction (χ : DirichletCharacter Complex N) (s : Complex) : Complex
参数：χ : DirichletCharacter Complex N；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s
` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zet
a functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence ran
ge, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
-/
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s

/--
The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta function.
(Compare `DirichletCharacter.LSeries_modOne_eq`.)
-/
/-
**DirichletCharacter.LFunction_modOne_eq** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCha
racter`。
形式化陈述：∀ {χ : DirichletCharacter ℂ 1}, DirichletCharacter.LFunction χ = riemannZe
ta
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.LFunction.eq_1`：∀ {N : ℕ} [inst : NeZero N] (χ : Diri
chletCharacter ℂ N) (s : ℂ),   DirichletCharacter.LFunction χ s = ZMod.LFunction
 (⇑χ) s
· 使用引理 `ZMod.LFunction_modOne_eq`：LFunction_modOne_eq (Φ : ZMod 1 -> Complex) (s
 : Complex) : LFunction Φ s = Φ 0 * riemannZeta s
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta fun
ction.
(Compare `DirichletCharacter.LSeries_modOne_eq`.)
-/
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

/--
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of the naive Dirichlet
series.
-/
/-
**DirichletCharacter.LFunction_eq_LSeries** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCh
aracter`。
形式化陈述：LFunction_eq_LSeries (χ : DirichletCharacter Complex N) {s : Complex} (hs 
: 1 < re s) : LFunction χ s = LSeries (χ ·) s
参数：χ : DirichletCharacter Complex N；hs : 1 < re s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.LFunction_eq_LSeries`：LFunction_eq_LSeries (Φ : ZMod N -> Complex) 
{s : Complex} (hs : 1 < re s) : LFunction Φ s = LSeries (Φ ·) s

--- 原说明 ---
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of th
e naive Dirichlet
series.
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs
/-
**DirichletCharacter.deriv_LFunction_eq_deriv_LSeries** 是 Mathlib 中的一个引理，位于命名空间 
`DirichletCharacter`。
形式化陈述：deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter Complex N) {s : C
omplex} (hs : 1 < s.re) : deriv (LFunction χ) s = deriv (LSeries (χ ·)) s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `DirichletCharacter.LFunction_eq_LSeries`：LFunction_eq_LSeries (χ : Diric
hletCharacter Complex N) {s : Complex} (hs : 1 < re s) : LFunction χ s = LSeries
 (χ ·) s
-/
lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (LFunction χ) s = deriv (LSeries (χ ·)) s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial.
-/
@[fun_prop]
/-
**DirichletCharacter.differentiableAt_LFunction** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：differentiableAt_LFunction (χ : DirichletCharacter Complex N) (s : Complex
) (hs : s != 1 ∨ χ != 1) : DifferentiableAt Complex (LFunction χ) s
参数：χ : DirichletCharacter Complex N；s : Complex；hs : s != 1 ∨ χ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.differentiableAt_LFunction`：differentiableAt_LFunction (Φ : ZMod N 
-> Complex) (s : Complex) (hs : s != 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt Comple
x (LFunction Φ) s
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
The L-function of a Dirichlet character is differentiable, except at `s = 1` if 
the character is
trivial.
-/
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
@[fun_prop]
/-
**DirichletCharacter.differentiable_LFunction** 是 Mathlib 中的一个引理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：differentiable_LFunction {χ : DirichletCharacter Complex N} (hχ : χ != 1) 
: Differentiable Complex (LFunction χ)
参数：hχ : χ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.differentiableAt_LFunction`：differentiableAt_LFunctio
n (χ : DirichletCharacter Complex N) (s : Complex) (hs : s != 1 ∨ χ != 1) : Diff
erentiableAt Complex (LFunction χ) …

--- 原说明 ---
The L-function of a non-trivial Dirichlet character is differentiable everywhere
.
-/
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
/-
**DirichletCharacter.Even.LFunction_neg_two_mul_nat_add_one** 是 Mathlib 中的一个定理，位
于命名空间 `DirichletCharacter.Even`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {χ : DirichletCharacter ℂ N},   χ.Even → ∀ (n 
: ℕ), DirichletCharacter.LFunction χ (-(2 * (↑n + 1))) = 0
参数：n : ℕ；-(2 * (↑n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.LFunction_neg_two_mul_nat_add_one`：∀ {N : ℕ} [inst : NeZero N] {Φ :
 ZMod N → ℂ}, Function.Even Φ → ∀ (n : ℕ), ZMod.LFunction Φ (-(2 * (↑n + 1))) = 
0
· 使用定理 `DirichletCharacter.Even.to_fun`：∀ {S : Type u_2} [inst : CommRing S] {m 
: ℕ} {χ : DirichletCharacter S m}, χ.Even → Function.Even ⇑χ

--- 原说明 ---
The L-function of an even Dirichlet character vanishes at strictly negative even
 integers.
-/
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-(2 * (n + 1))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
/-
**DirichletCharacter.Even.LFunction_neg_two_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `D
irichletCharacter.Even`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {χ : DirichletCharacter ℂ N},   χ.Even → ∀ (n 
: ℕ) [NeZero n], DirichletCharacter.LFunction χ (-(2 * ↑n)) = 0
参数：n : ℕ；-(2 * ↑n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.LFunction.congr_simp`：∀ {N : ℕ} [inst : NeZero N] (χ 
χ_1 : DirichletCharacter ℂ N),   χ = χ_1 → ∀ (s s_1 : ℂ), s = s_1 → DirichletCha
racter.LFunction χ s = Dirich…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirichletCharacter.Even.LFunction_neg_two_mul_nat_add_one`：∀ {N : ℕ} [in
st : NeZero N] {χ : DirichletCharacter ℂ N},   χ.Even → ∀ (n : ℕ), DirichletChar
acter.LFunction χ (-(2 * (↑n + 1))) = 0

--- 原说明 ---
The L-function of an even Dirichlet character vanishes at strictly negative even
 integers.
-/
lemma Even.LFunction_neg_two_mul_nat {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) [NeZero n] :
    LFunction χ (-(2 * n)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m

/-- The L-function of an odd Dirichlet character vanishes at negative odd integers. -/
/-
**DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one** 是 Mathlib 中的一个定理，位于
命名空间 `DirichletCharacter.Odd`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {χ : DirichletCharacter ℂ N},   χ.Odd → ∀ (n :
 ℕ), DirichletCharacter.LFunction χ (-(2 * ↑n) - 1) = 0
参数：n : ℕ；-(2 * ↑n) - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.LFunction_neg_two_mul_nat_sub_one`：∀ {N : ℕ} [inst : NeZero N] {Φ :
 ZMod N → ℂ}, Function.Odd Φ → ∀ (n : ℕ), ZMod.LFunction Φ (-(2 * ↑n) - 1) = 0
· 使用定理 `DirichletCharacter.Odd.to_fun`：∀ {S : Type u_2} [inst : CommRing S] {m :
 ℕ} {χ : DirichletCharacter S m}, χ.Odd → Function.Odd ⇑χ

--- 原说明 ---
The L-function of an odd Dirichlet character vanishes at negative odd integers.
-/
@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
    {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-(2 * n) - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n

/-!
### Results on changing levels
-/

/-
**DirichletCharacter.LFunction_changeLevel_aux** 是 Mathlib 中的一个引理，位于命名空间 `Dirich
letCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Results on changing levels
-/
private lemma LFunction_changeLevel_aux {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
      |>.isPreconnected
  have hne : 2 ∈ ({1}ᶜ : Set ℂ) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (g := fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .fun_finsetProd fun i h ↦ ?_
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    fun_prop
  · refine eventually_of_mem ?_ (fun t (ht : 1 < t.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)
    · simpa [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L function
of `χ` considered as a Dirichlet character of level `N` from the L function of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`.
(Note that `1 - χ p * p ^ (-s) = 1` when `p` divides `M`). -/
/-
**DirichletCharacter.LFunction_changeLevel** 是 Mathlib 中的一个引理，位于命名空间 `DirichletC
haracter`。
形式化陈述：LFunction_changeLevel {M N : Nat} [NeZero M] [NeZero N] (hMN : M ∣ N) (χ :
 DirichletCharacter Complex M) {s : Complex} (h : χ != 1 ∨ s != 1) : LFunction (
changeLevel hMN χ) s = LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s
))
参数：hMN : M ∣ N；χ : DirichletCharacter Complex M；h : χ != 1 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DirichletCharacter.changeLevel_eq_one_iff`：changeLevel_eq_one_iff {m : N
at} [NeZero m] {χ : DirichletCharacter R n} (hm : n ∣ m) : changeLevel hm χ = 1 
↔ χ = 1
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
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
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用引理 `DirichletCharacter.differentiable_LFunction`：differentiable_LFunction {χ
 : DirichletCharacter Complex N} (hχ : χ != 1) : Differentiable Complex (LFuncti
on χ)
· 使用定理 `continuous_finsetProd`：continuous_finsetProd {f : ι -> X -> M} (s : Fins
et ι) : (forall i in s, Continuous (f i)) -> Continuous fun a => ∏ i in s, f i a
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用引理 `continuous_const_cpow`：continuous_const_cpow (z : Complex) [NeZero z] : 
Continuous fun s : Complex => z ^ s
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Continuous.ext_on`：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense
 s) {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f 
= g
· 使用定理 `Complex.instT2Space`：T2Space ℂ
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain th
e L function
of `χ` considered as a Dirichlet character of level `N` from the L function of `
χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`.
(Note that `1 - χ p * p ^ (-s) = 1` when `p` divides `M`).
-/
lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · have hχ : changeLevel hMN χ ≠ 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
      (differentiable_LFunction h).continuous.mul <| continuous_finsetProd _ fun p hp ↦ by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h ↦ LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

/-!
### The `L`-function of the trivial character mod `N`
-/

/-- The `L`-function of the trivial character mod `N`. -/
/-
**DirichletCharacter.LFunctionTrivChar** 是 Mathlib 中的一个缩写定义，位于命名空间 `DirichletCha
racter`。
形式化陈述：LFunctionTrivChar (N : Nat) [NeZero N]
参数：N : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L`-function of the trivial character mod `N`.
-/
noncomputable abbrev LFunctionTrivChar (N : ℕ) [NeZero N] :=
  (1 : DirichletCharacter ℂ N).LFunction

/-- The L function of the trivial Dirichlet character mod `N` is obtained from the Riemann
zeta function by multiplying with `∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))`. -/
/-
**DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta** 是 Mathlib 中的一个引理，位于命
名空间 `DirichletCharacter`。
形式化陈述：LFunctionTrivChar_eq_mul_riemannZeta {s : Complex} (hs : s != 1) : LFuncti
onTrivChar N s = (∏ p in N.primeFactors, (1 - (p : Complex) ^ (-s))) * riemannZe
ta s
参数：hs : s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirichletCharacter.LFunction_modOne_eq`：∀ {χ : DirichletCharacter ℂ 1}, 
DirichletCharacter.LFunction χ = riemannZeta
· 使用定理 `DirichletCharacter.LFunctionTrivChar.eq_1`：∀ (N : ℕ) [inst : NeZero N], 
DirichletCharacter.LFunctionTrivChar N = DirichletCharacter.LFunction 1
· 使用定理 `Nat.one_dvd`：∀ (n : ℕ), 1 ∣ n
· 使用引理 `DirichletCharacter.changeLevel_one`：changeLevel_one {d : Nat} (h : d ∣ n
) : changeLevel h (1 : DirichletCharacter R d) = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `DirichletCharacter.LFunction_changeLevel`：LFunction_changeLevel {M N : N
at} [NeZero M] [NeZero N] (hMN : M ∣ N) (χ : DirichletCharacter Complex M) {s : 
Complex} (h : χ != 1 ∨ s != 1)…

--- 原说明 ---
The L function of the trivial Dirichlet character mod `N` is obtained from the R
iemann
zeta function by multiplying with `∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))`.
-/
lemma LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunctionTrivChar, ← changeLevel_one N.one_dvd, mul_comm]
  convert! LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- The L function of the trivial Dirichlet character mod `N` has a simple pole with
residue `∏ p ∈ N.primeFactors, (1 - p⁻¹)` at `s = 1`. -/
/-
**DirichletCharacter.LFunctionTrivChar_residue_one** 是 Mathlib 中的一个引理，位于命名空间 `Di
richletCharacter`。
形式化陈述：LFunctionTrivChar_residue_one : Tendsto (fun s => (s - 1) * LFunctionTrivC
har N s) (𝓝[!=] 1) (𝓝 <| ∏ p in N.primeFactors, (1 - (p : Complex)⁻¹))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.eventuallyEq_nhdsWithin`：Set.EqOn.eventuallyEq_nhdsWithin {f g 
: α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用引理 `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`：LFunctionTrivCh
ar_eq_mul_riemannZeta {s : Complex} (hs : s != 1) : LFunctionTrivChar N s = (∏ p
 in N.primeFactors, (1 - (p : Complex) ^ (-s)…
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_neg_one`：cpow_neg_one (x : Complex) : x ^ (-1 : Complex) = 
x⁻¹
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
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_finsetProd`：continuous_finsetProd {f : ι -> X -> M} (s : Fins
et ι) : (forall i in s, Continuous (f i)) -> Continuous fun a => ∏ i in s, f i a
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用引理 `continuous_const_cpow`：continuous_const_cpow (z : Complex) [NeZero z] : 
Continuous fun s : Complex => z ^ s
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The L function of the trivial Dirichlet character mod `N` has a simple pole with
residue `∏ p ∈ N.primeFactors, (1 - p⁻¹)` at `s = 1`.
-/
lemma LFunctionTrivChar_residue_one :
    Tendsto (fun s ↦ (s - 1) * LFunctionTrivChar N s) (𝓝[≠] 1)
      (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  have H : (fun s ↦ (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[≠] 1]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s ↦ ∏ p ∈ N.primeFactors, _) ?_ riemannZeta_residue_one
  refine tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto ?_ 1
  exact continuous_finsetProd _ fun p hp ↦ by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

/-!
### Completed L-functions and the functional equation
-/

section gammaFactor

omit [NeZero N] -- not required for these declarations

open scoped Classical in
/-- The Archimedean Gamma factor: `Gammaℝ s` if `χ` is even, and `Gammaℝ (s + 1)` otherwise. -/
/-
**DirichletCharacter.gammaFactor** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：gammaFactor (χ : DirichletCharacter Complex N) (s : Complex)
参数：χ : DirichletCharacter Complex N；s : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Archimedean Gamma factor: `Gammaℝ s` if `χ` is even, and `Gammaℝ (s + 1)` ot
herwise.
-/
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) :=
  if χ.Even then Gammaℝ s else Gammaℝ (s + 1)
/-
**DirichletCharacter.Even.gammaFactor_def** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCh
aracter.Even`。
形式化陈述：∀ {N : ℕ} {χ : DirichletCharacter ℂ N}, χ.Even → ∀ (s : ℂ), χ.gammaFactor 
s = s.Gammaℝ
参数：s : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
    gammaFactor χ s = Gammaℝ s := by
  simp [gammaFactor, hχ]
/-
**DirichletCharacter.Odd.gammaFactor_def** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCha
racter.Odd`。
形式化陈述：∀ {N : ℕ} {χ : DirichletCharacter ℂ N}, χ.Odd → ∀ (s : ℂ), χ.gammaFactor s
 = (s + 1).Gammaℝ
参数：s : ℂ；s + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `DirichletCharacter.Odd.not_even`：∀ {S : Type u_2} [inst : CommRing S] {m
 : ℕ} (ψ : DirichletCharacter S m) [NeZero 2], ψ.Odd → ¬ψ.Even
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + 1) := by
  simp [gammaFactor, hχ.not_even]

end gammaFactor

/--
The completed L-function of a Dirichlet character, almost everywhere equal to
`LFunction χ s * gammaFactor χ s`.
-/
/-
**DirichletCharacter.completedLFunction** 是 Mathlib 中的一个定义，位于命名空间 `DirichletChar
acter`。
形式化陈述：{N : ℕ} → [NeZero N] → DirichletCharacter ℂ N → ℂ → ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completed L-function of a Dirichlet character, almost everywhere equal to
`LFunction χ s * gammaFactor χ s`.
-/
@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ZMod.completedLFunction χ s

/--
The completed L-function of the (unique) Dirichlet character mod 1 is the completed Riemann zeta
function.
-/
/-
**DirichletCharacter.completedLFunction_modOne_eq** 是 Mathlib 中的一个引理，位于命名空间 `Dir
ichletCharacter`。
形式化陈述：completedLFunction_modOne_eq {χ : DirichletCharacter Complex 1} : complete
dLFunction χ = completedRiemannZeta
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.completedLFunction.eq_1`：∀ {N : ℕ} [inst : NeZero N] 
(χ : DirichletCharacter ℂ N) (s : ℂ),   DirichletCharacter.completedLFunction χ 
s = ZMod.completedLFunction (⇑χ)…
· 使用引理 `ZMod.completedLFunction_modOne_eq`：completedLFunction_modOne_eq (Φ : ZMo
d 1 -> Complex) (s : Complex) : completedLFunction Φ s = Φ 1 * completedRiemannZ
eta s
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The completed L-function of the (unique) Dirichlet character mod 1 is the comple
ted Riemann zeta
function.
-/
lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

/--
The completed L-function of a Dirichlet character is differentiable, with the following
exceptions: at `s = 1` if `χ` is the trivial character (to any modulus); and at `s = 0` if the
modulus is 1. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
/-
**DirichletCharacter.differentiableAt_completedLFunction** 是 Mathlib 中的一个引理，位于命名
空间 `DirichletCharacter`。
形式化陈述：differentiableAt_completedLFunction (χ : DirichletCharacter Complex N) (s 
: Complex) (hs₀ : s != 0 ∨ N != 1) (hs₁ : s != 1 ∨ χ != 1) : DifferentiableAt Co
mplex (completedLFunction χ) s
参数：χ : DirichletCharacter Complex N；s : Complex；hs₀ : s != 0 ∨ N != 1；hs₁ : s !=
 1 ∨ χ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.differentiableAt_completedLFunction`：differentiableAt_completedLFun
ction (Φ : ZMod N -> Complex) (s : Complex) (hs₀ : s != 0 ∨ Φ 0 = 0) (hs₁ : s !=
 1 ∨ ∑ j, Φ j = 0) : Different…
· 使用引理 `DirichletCharacter.map_zero'`：map_zero' (hn : n != 1) : χ 0 = 0
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
The completed L-function of a Dirichlet character is differentiable, with the fo
llowing
exceptions: at `s = 1` if `χ` is the trivial character (to any modulus); and at 
`s = 0` if the
modulus is 1. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer on
e or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ N ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (completedLFunction χ) s :=
  ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)

/-- The completed L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
/-
**DirichletCharacter.differentiable_completedLFunction** 是 Mathlib 中的一个引理，位于命名空间
 `DirichletCharacter`。
形式化陈述：differentiable_completedLFunction {χ : DirichletCharacter Complex N} (hχ :
 χ != 1) : Differentiable Complex (completedLFunction χ)
参数：hχ : χ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.differentiableAt_completedLFunction`：differentiableAt
_completedLFunction (χ : DirichletCharacter Complex N) (s : Complex) (hs₀ : s !=
 0 ∨ N != 1) (hs₁ : s != 1 ∨ χ != 1) : Diffe…
· 使用引理 `DirichletCharacter.level_one'`：level_one' (hn : n = 1) : χ = 1

--- 原说明 ---
The completed L-function of a non-trivial Dirichlet character is differentiable 
everywhere.
-/
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

/--
Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well.
-/
/-
**DirichletCharacter.LFunction_eq_completed_div_gammaFactor** 是 Mathlib 中的一个引理，位
于命名空间 `DirichletCharacter`。
形式化陈述：LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter Complex N) 
(s : Complex) (h : s != 0 ∨ N != 1) : LFunction χ s = completedLFunction χ s / g
ammaFactor χ s
参数：χ : DirichletCharacter Complex N；s : Complex；h : s != 0 ∨ N != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.even_or_odd`：even_or_odd [NoZeroDivisors S] : ψ.Even 
∨ ψ.Odd
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.Even.gammaFactor_def`：∀ {N : ℕ} {χ : DirichletCharact
er ℂ N}, χ.Even → ∀ (s : ℂ), χ.gammaFactor s = s.Gammaℝ
· 使用引理 `ZMod.LFunction_eq_completed_div_gammaFactor_even`：LFunction_eq_completed
_div_gammaFactor_even (hΦ : Φ.Even) (s : Complex) (hs : s != 0 ∨ Φ 0 = 0) : LFun
ction Φ s = completedLFunction Φ s / G…
· 使用定理 `DirichletCharacter.Even.to_fun`：∀ {S : Type u_2} [inst : CommRing S] {m 
: ℕ} {χ : DirichletCharacter S m}, χ.Even → Function.Even ⇑χ
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用引理 `DirichletCharacter.map_zero'`：map_zero' (hn : n != 1) : χ 0 = 0
· 使用定理 `DirichletCharacter.Odd.gammaFactor_def`：∀ {N : ℕ} {χ : DirichletCharacte
r ℂ N}, χ.Odd → ∀ (s : ℂ), χ.gammaFactor s = (s + 1).Gammaℝ
· 使用引理 `ZMod.LFunction_eq_completed_div_gammaFactor_odd`：LFunction_eq_completed_
div_gammaFactor_odd (hΦ : Φ.Odd) (s : Complex) : LFunction Φ s = completedLFunct
ion Φ s / GammaReal (s + 1)
· 使用定理 `DirichletCharacter.Odd.to_fun`：∀ {S : Type u_2} [inst : CommRing S] {m :
 ℕ} {χ : DirichletCharacter S m}, χ.Odd → Function.Odd ⇑χ

--- 原说明 ---
Relation between the completed L-function and the usual one. We state it this wa
y around so
it holds at the poles of the gamma factor as well.
-/
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ N ≠ 1) : LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun

open scoped Classical in
/--
Global root number of `χ` (for `χ` primitive; junk otherwise). Defined as
`gaussSum χ stdAddChar / I ^ a / N ^ (1 / 2)`, where `a = 0` if even, `a = 1` if odd. (The factor
`1 / I ^ a` is the Archimedean root number.) This is a complex number of absolute value 1.
-/
/-
**DirichletCharacter.rootNumber** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：rootNumber (χ : DirichletCharacter Complex N) : Complex
参数：χ : DirichletCharacter Complex N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Global root number of `χ` (for `χ` primitive; junk otherwise). Defined as
`gaussSum χ stdAddChar / I ^ a / N ^ (1 / 2)`, where `a = 0` if even, `a = 1` if
 odd. (The factor
`1 / I ^ a` is the Archimedean root number.) This is a complex number of absolut
e value 1.
-/
noncomputable def rootNumber (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : ℂ)

/-- The root number of the unique Dirichlet character modulo 1 is 1. -/
/-
**DirichletCharacter.rootNumber_modOne** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：rootNumber_modOne (χ : DirichletCharacter Complex 1) : rootNumber χ = 1
参数：χ : DirichletCharacter Complex 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.singleton_eq_univ`：singleton_eq_univ [Subsingleton α] (a : α) : (
{a} : Finset α) = univ
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The root number of the unique Dirichlet character modulo 1 is 1.
-/
lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) : rootNumber χ = 1 := by
  simp [rootNumber, gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _),
    (show χ.Even from map_one _)]

namespace IsPrimitive

/-- **Functional equation** for primitive Dirichlet L-functions. -/
/-
**DirichletCharacter.IsPrimitive.completedLFunction_one_sub** 是 Mathlib 中的一个定理，位
于命名空间 `DirichletCharacter.IsPrimitive`。
形式化陈述：completedLFunction_one_sub {χ : DirichletCharacter Complex N} (hχ : IsPrim
itive χ) (s : Complex) : completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNu
mber χ * completedLFunction χ⁻¹ s
参数：hχ : IsPrimitive χ；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `DirichletCharacter.completedLFunction_modOne_eq`：completedLFunction_modO
ne_eq {χ : DirichletCharacter Complex 1} : completedLFunction χ = completedRiema
nnZeta
· 使用定理 `completedRiemannZeta_one_sub`：completedRiemannZeta_one_sub (s : Complex)
 : completedRiemannZeta (1 - s) = completedRiemannZeta s
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用引理 `DirichletCharacter.rootNumber_modOne`：rootNumber_modOne (χ : DirichletCh
aracter Complex 1) : rootNumber χ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `DirichletCharacter.conductor_one`：conductor_one [NeZero n] : conductor (
1 : DirichletCharacter R n) = 1
· 使用定理 `DirichletCharacter.IsPrimitive.eq_1`：∀ {R : Type u_1} [inst : CommMonoid
WithZero R] {n : ℕ} (χ : DirichletCharacter R n), χ.IsPrimitive = (χ.conductor =
 n)
· 使用定理 `DirichletCharacter.rootNumber.eq_1`：∀ {N : ℕ} [inst : NeZero N] (χ : Dir
ichletCharacter ℂ N),   χ.rootNumber = (gaussSum χ ZMod.stdAddChar / Complex.I ^
 if χ.Even then 0 else 1…
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `Complex.cpow_sub`：cpow_sub {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
**Functional equation** for primitive Dirichlet L-functions.
-/
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  classical
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, rootNumber_modOne]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h ↦ hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber, ← mul_comm_div, ← mul_comm_div, ← cpow_sub _ _ (NeZero.ne _), sub_sub, add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) / ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction, completedLFunction_one_sub_odd h.to_fun,
        pow_one, h, div_I, mul_neg_one, ← neg_mul, neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j ↦ χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul j, map_mul, mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)) := by
    rw [completedLFunction, completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_one.neg), mul_one]

end IsPrimitive

end DirichletCharacter

/-!
### The logarithmic derivative of the L-function of a Dirichlet character

We show that `s ↦ -(L' χ s) / L χ s + 1 / (s - 1)` is continuous outside the zeros of `L χ`
when `χ` is a trivial Dirichlet character and that `-L' χ / L χ` is continuous outside
the zeros of `L χ` when `χ` is nontrivial.
-/

namespace DirichletCharacter

open Complex

section trivial

variable (n : ℕ) [NeZero n]

/-- The function obtained by "multiplying away" the pole of `L χ` for a trivial Dirichlet
character `χ`. Its (negative) logarithmic derivative is used to prove Dirichlet's Theorem
on primes in arithmetic progression. -/
/-
**DirichletCharacter.LFunctionTrivChar** 是 Mathlib 中的一个缩写定义，位于命名空间 `DirichletCha
racter`。
形式化陈述：LFunctionTrivChar (N : Nat) [NeZero N]
参数：N : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function obtained by "multiplying away" the pole of `L χ` for a trivial Diri
chlet
character `χ`. Its (negative) logarithmic derivative is used to prove Dirichlet'
s Theorem
on primes in arithmetic progression.
-/
noncomputable abbrev LFunctionTrivChar₁ : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * LFunctionTrivChar n s) 1
    (∏ p ∈ n.primeFactors, (1 - (p : ℂ)⁻¹))
/-
**DirichletCharacter.LFunctionTrivChar** 是 Mathlib 中的一个缩写定义，位于命名空间 `DirichletCha
racter`。
形式化陈述：LFunctionTrivChar (N : Nat) [NeZero N]
参数：N : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 ≠ 0 := by
  simp only [Function.update_self]
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  simpa [sub_ne_zero] using (Nat.prime_of_mem_primeFactors hp).ne_one

/-- `s ↦ (s - 1) * L χ s` is an entire function when `χ` is a trivial Dirichlet character. -/
/-
**DirichletCharacter.differentiable_LFunctionTrivChar** 是 Mathlib 中的一个引理，位于命名空间 
`DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ↦ (s - 1) * L χ s` is an entire function when `χ` is a trivial Dirichlet char
acter.
-/
lemma differentiable_LFunctionTrivChar₁ : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s ↦ (s - 1) * LFunctionTrivChar n s)
    (fun _ hs ↦ DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all))
    fun _ hs ↦ Function.update_of_ne (Set.mem_sdiff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa using LFunctionTrivChar_residue_one
/-
**DirichletCharacter.deriv_LFunctionTrivChar** 是 Mathlib 中的一个引理，位于命名空间 `Dirichle
tCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma deriv_LFunctionTrivChar₁_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv (LFunctionTrivChar₁ n) s =
      (s - 1) * deriv (LFunctionTrivChar n) s + LFunctionTrivChar n s := by
  have H : deriv (LFunctionTrivChar₁ n) s =
      deriv (fun w ↦ (w - 1) * LFunctionTrivChar n w) s := by
    refine eventuallyEq_iff_exists_mem.mpr ?_ |>.deriv_eq
    exact ⟨_, isOpen_ne.mem_nhds hs, fun _ hw ↦ Function.update_of_ne (Set.mem_ofPred.mp hw) ..⟩
  rw [H, deriv_fun_mul (by fun_prop) (differentiableAt_LFunction _ s (.inl hs)), deriv_sub_const,
    deriv_id'', one_mul, add_comm]

/-- The negative logarithmic derivative of `s ↦ (s - 1) * L χ s` for a trivial
Dirichlet character `χ` is continuous away from the zeros of `L χ` (including at `s = 1`). -/
/-
**DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar** 是 Mathlib 中的一
个引理，位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negative logarithmic derivative of `s ↦ (s - 1) * L χ s` for a trivial
Dirichlet character `χ` is continuous away from the zeros of `L χ` (including at
 `s = 1`).
-/
lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    ContinuousOn (fun s ↦ -deriv (LFunctionTrivChar₁ n) s / LFunctionTrivChar₁ n s)
      {s | s = 1 ∨ LFunctionTrivChar n s ≠ 0} := by
  simp_rw [neg_div]
  have h := differentiable_LFunctionTrivChar₁ n
  refine ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun w hw ↦ ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁, Function.update_of_ne hw', mul_ne_zero_iff]
    exact ⟨sub_ne_zero_of_ne hw', (Set.mem_ofPred.mp hw).resolve_left hw'⟩

end trivial

section nontrivial

variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}

/-- The negative logarithmic derivative of the L-function of a nontrivial Dirichlet character
is continuous away from the zeros of the L-function. -/
/-
**DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv** 是 Mathlib 
中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ != 1) : ContinuousO
n (fun s => -deriv (LFunction χ) s / LFunction χ s) {s | LFunction χ s != 0}
参数：hχ : χ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.differentiable_LFunction`：differentiable_LFunction {χ
 : DirichletCharacter Complex N} (hχ : χ != 1) : Differentiable Complex (LFuncti
on χ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousOn.div`：ContinuousOn.div (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (h₀ : forall x in s, g x != 0) : ContinuousOn (f / g) s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContDiff.continuous_deriv`：ContDiff.continuous_deriv (h : ContDiff 𝕜 n f
) (hn : 1 <= n) : Continuous (deriv f)
· 使用定理 `Differentiable.contDiff`：∀ {E : Type u} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E},   Differentiable ℂ f → ∀
 {n : WithTop…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R

--- 原说明 ---
The negative logarithmic derivative of the L-function of a nontrivial Dirichlet 
character
is continuous away from the zeros of the L-function.
-/
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ ≠ 1) :
    ContinuousOn (fun s ↦ -deriv (LFunction χ) s / LFunction χ s) {s | LFunction χ s ≠ 0} := by
  have h := differentiable_LFunction hχ
  simpa [neg_div] using! ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw ↦ hw).fun_neg

end nontrivial

end DirichletCharacter

