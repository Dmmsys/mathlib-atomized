/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.MoveAdd

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Functions and measures of temperate growth -/

@[expose] public section

noncomputable section

open scoped Nat NNReal ContDiff

open Asymptotics

variable {ι 𝕜 R D E F G H : Type*}

namespace Function

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function is called of temperate growth if it is smooth and all iterated derivatives are
polynomially bounded. -/
@[fun_prop]
/-
**Function.HasTemperateGrowth** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：HasTemperateGrowth (f : E -> F) : Prop
参数：f : E -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is called of temperate growth if it is smooth and all iterated deriva
tives are
polynomially bounded.
-/
def HasTemperateGrowth (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ k

/-- A function has temperate growth if and only if it is smooth and its `n`-th iterated
derivative is `O((1 + ‖x‖) ^ k)` for some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.

TODO: when `E` is finite dimensional, this is equivalent to the derivatives being `O(‖x‖ ^ k)`
as `‖x‖ → ∞`.
-/
/-
**Function.hasTemperateGrowth_iff_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：hasTemperateGrowth_iff_isBigO {f : E -> F} : f.HasTemperateGrowth ↔ ContDi
ff Real ∞ f ∧ forall n, exists k, iteratedFDeriv Real n f =O[⊤] (fun x => (1 + ‖
x‖) ^ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
A function has temperate growth if and only if it is smooth and its `n`-th itera
ted
derivative is `O((1 + ‖x‖) ^ k)` for some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound
 holds everywhere.

TODO: when `E` is finite dimensional, this is equivalent to the derivatives bein
g `O(‖x‖ ^ k)`
as `‖x‖ → ∞`.
-/
theorem hasTemperateGrowth_iff_isBigO {f : E → F} :
    f.HasTemperateGrowth ↔ ContDiff ℝ ∞ f ∧
      ∀ n, ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
  simp_rw [Asymptotics.isBigO_top]
  congrm ContDiff ℝ ∞ f ∧ (∀ n, ∃ k C, ∀ x, _ ≤ C * ?_)
  rw [norm_pow, Real.norm_of_nonneg (by positivity)]

/-- If `f` has temperate growth, then its `n`-th iterated derivative is `O((1 + ‖x‖) ^ k)` for
some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.
-/
/-
**Function.HasTemperateGrowth.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTemp
erateGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f :
 E → F},   Function.HasTemperateGrowth f → ∀ (n : ℕ), ∃ k, iteratedFDeriv ℝ n f 
=O[⊤] fun x => (1 + ‖x‖) ^ k
参数：n : ℕ；1 + ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.hasTemperateGrowth_iff_isBigO`：hasTemperateGrowth_iff_isBigO {f
 : E -> F} : f.HasTemperateGrowth ↔ ContDiff Real ∞ f ∧ forall n, exists k, iter
atedFDeriv Real n f =O[⊤] (f…

--- 原说明 ---
If `f` has temperate growth, then its `n`-th iterated derivative is `O((1 + ‖x‖)
 ^ k)` for
some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound
 holds everywhere.
-/
theorem HasTemperateGrowth.isBigO {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (n : ℕ) :
    ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) :=
  Function.hasTemperateGrowth_iff_isBigO.mp hf_temperate |>.2 n

/-- If `f` has temperate growth, then for any `N : ℕ` one can find `k` such that *all* iterated
derivatives of `f` of order `≤ N` are `O((1 + ‖x‖) ^ k)`.

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.
-/
/-
**Function.HasTemperateGrowth.isBigO_uniform** 是 Mathlib 中的一个定理，位于命名空间 `Function
.HasTemperateGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f :
 E → F},   Function.HasTemperateGrowth f → ∀ (N : ℕ), ∃ k, ∀ n ≤ N, iteratedFDer
iv ℝ n f =O[⊤] fun x => (1 + ‖x‖) ^ k
参数：N : ℕ；1 + ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Function.HasTemperateGrowth.isBigO`：∀ {E : Type u_5} {F : Type u_6} [ins
t : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGrou
p F]   [inst_3 : NormedS…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `f` has temperate growth, then for any `N : ℕ` one can find `k` such that *al
l* iterated
derivatives of `f` of order `≤ N` are `O((1 + ‖x‖) ^ k)`.

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound
 holds everywhere.
-/
theorem HasTemperateGrowth.isBigO_uniform {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (N : ℕ) :
    ∃ k, ∀ n ≤ N, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
  choose k hk using hf_temperate.isBigO
  use (Finset.range (N + 1)).sup k
  intro n hn
  refine (hk n).trans (isBigO_of_le _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  · simp
  · exact Finset.le_sup (by simpa using hn)
/-
**Function.HasTemperateGrowth.norm_iteratedFDeriv_le_uniform** 是 Mathlib 中的一个定理，
位于命名空间 `Function.HasTemperateGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f :
 E → F},   Function.HasTemperateGrowth f →     ∀ (n : ℕ), ∃ k C, 0 ≤ C ∧ ∀ N ≤ n
, ∀ (x : E), ‖iteratedFDeriv ℝ N f x‖ ≤ C * (1 + ‖x‖) ^ k
参数：n : ℕ；x : E；1 + ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.isBigO_uniform`：∀ {E : Type u_5} {F : Type u
_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAdd
CommGroup F]   [inst_3 : NormedS…
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem HasTemperateGrowth.norm_iteratedFDeriv_le_uniform {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ N ≤ n, ∀ x : E, ‖iteratedFDeriv ℝ N f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  rcases hf_temperate.isBigO_uniform n with ⟨k, hk⟩
  set F := fun x (N : Fin (n + 1)) ↦ iteratedFDeriv ℝ N f x
  have : F =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
    simp_rw [F, isBigO_pi, Fin.forall_iff, Nat.lt_succ_iff]
    exact hk
  rcases this.exists_nonneg with ⟨C, C_nonneg, hC⟩
  simp (discharger := positivity) only [isBigOWith_top, Real.norm_of_nonneg,
    pi_norm_le_iff_of_nonneg, Fin.forall_iff, Nat.lt_succ_iff] at hC
  exact ⟨k, C, C_nonneg, fun N hN x ↦ hC x N hN⟩
/-
**Function.HasTemperateGrowth.of_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasT
emperateGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f :
 E → F},   Function.HasTemperateGrowth (fderiv ℝ f) →     Differentiable ℝ f → ∀
 {k : ℕ} {C : ℝ}, (∀ (x : E), ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) → Function.HasTemperate
Growth f
参数：fderiv ℝ f；∀ (x : E), ‖f x‖ ≤ C * (1 + ‖x‖) ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_succ_iff_fderiv`：contDiff_succ_iff_fderiv : ContDiff 𝕜 (n + 1) 
f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOnNhd 𝕜 f univ) ∧ ContDiff 𝕜 n (fderi
v 𝕜 f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iteratedFDeriv_succ_eq_comp_right`：iteratedFDeriv_succ_eq_comp_right {n 
: Nat} : iteratedFDeriv 𝕜 (n + 1) f x = ((continuousMultilinearCurryRightEquiv' 
𝕜 n E F).symm ∘ iterate…
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
-/
lemma HasTemperateGrowth.of_fderiv {f : E → F}
    (h'f : Function.HasTemperateGrowth (fderiv ℝ f)) (hf : Differentiable ℝ f) {k : ℕ} {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Function.HasTemperateGrowth f := by
  refine ⟨contDiff_succ_iff_fderiv.2 ⟨hf, by simp, h'f.1⟩, fun n ↦ ?_⟩
  rcases n with rfl | m
  · exact ⟨k, C, fun x ↦ by simpa using h x⟩
  · rcases h'f.2 m with ⟨k', C', h'⟩
    refine ⟨k', C', ?_⟩
    simpa [iteratedFDeriv_succ_eq_comp_right] using h'

@[fun_prop]
/-
**Function.HasTemperateGrowth.zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTemper
ateGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F], Fun
ction.HasTemperateGrowth fun x => 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDeriv_fun_zero`：iteratedFDeriv_fun_zero {n : Nat} : iteratedFDe
riv 𝕜 n (fun (_ : E) => (0 : F)) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma HasTemperateGrowth.zero :
    Function.HasTemperateGrowth (fun _ : E ↦ (0 : F)) := by
  refine ⟨contDiff_const, fun n ↦ ⟨0, 0, fun x ↦ ?_⟩⟩
  simp

@[fun_prop, simp]
/-
**Function.HasTemperateGrowth.const** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempe
rateGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] (c :
 F), Function.HasTemperateGrowth fun x => c
参数：c : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.of_fderiv`：∀ {E : Type u_5} {F : Type u_6} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_fun_const`：fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) =
 0
· 使用定理 `Function.HasTemperateGrowth.zero`：∀ {E : Type u_5} {F : Type u_6} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma HasTemperateGrowth.const (c : F) :
    Function.HasTemperateGrowth (fun _ : E ↦ c) :=
  .of_fderiv (by simpa using .zero) (differentiable_const c) (k := 0) (C := ‖c‖) (fun x ↦ by simp)

@[fun_prop]
/-
**Function._root_.HasCompactSupport.hasTemperateGrowth** 是 Mathlib 中的一个引理，位于命名空间
 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HasCompactSupport.hasTemperateGrowth {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff ℝ ∞ f) : f.HasTemperateGrowth := by
  refine ⟨h₂, fun n ↦ ?_⟩
  set g := fun x ↦ ‖iteratedFDeriv ℝ n f x‖
  have hg : Continuous g := (h₂.continuous_iteratedFDeriv <| mod_cast le_top).norm
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge_of_hasCompactSupport ((h₁.iteratedFDeriv _).norm)
  refine ⟨0, g x₀, fun x ↦ ?_⟩
  simpa using hx₀ x

/-- Composition of two temperate growth functions is of temperate growth.

Version where the outer function `g` is only of temperate growth on the image of inner function
`f`. -/
/-
**Function.HasTemperateGrowth.comp'** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempe
rateGrowth`。
形式化陈述：∀ {D : Type u_4} {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] [inst_4 : NormedAddCommGroup D] [inst_5 : NormedSpace ℝ D]   {g : E →
 F} {f : D → E} {t : Set E},   Set.range f ⊆ t →     UniqueDiffOn ℝ t →       Co
ntDiffOn ℝ (↑⊤) g t →         (∀ (N : ℕ), ∃ k C, ∃ (_ : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ t
, ‖iteratedFDerivWithin ℝ n g t x‖ ≤ C * (1 + ‖x‖) ^ k) →           Function.Has
TemperateGrowth f → Function.HasTemperateGrowth (g ∘ f)
参数：↑⊤；∀ (N : ℕ), ∃ k C, ∃ (_ : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ t, ‖iteratedFDerivWithin ℝ
 n g t x‖ ≤ C * (1 + ‖x‖) ^ k；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.comp_contDiff`：ContDiffOn.comp_contDiff {s : Set F} {g : F ->
 G} {f : E -> F} (hg : ContDiffOn 𝕜 n g s) (hf : ContDiff 𝕜 n f) (hs : forall x,
 f x in s) : C…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.HasTemperateGrowth.norm_iteratedFDeriv_le_uniform`：∀ {E : Type 
u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [in
st_2 : NormedAddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
Composition of two temperate growth functions is of temperate growth.

Version where the outer function `g` is only of temperate growth on the image of
 inner function
`f`.
-/
theorem HasTemperateGrowth.comp' [NormedAddCommGroup D] [NormedSpace ℝ D] {g : E → F} {f : D → E}
    {t : Set E} (ht : Set.range f ⊆ t) (ht' : UniqueDiffOn ℝ t) (hg₁ : ContDiffOn ℝ ∞ g t)
    (hg₂ : ∀ N, ∃ k C, ∃ (_hC : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ t,
    ‖iteratedFDerivWithin ℝ n g t x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hf : f.HasTemperateGrowth) : (g ∘ f).HasTemperateGrowth := by
  refine ⟨hg₁.comp_contDiff hf.1 (ht ⟨·, rfl⟩), fun n ↦ ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg₂ n
  have h₁' : ∀ x, ‖f x‖ ≤ C₁ * (1 + ‖x‖) ^ k₁ := by simpa using h₁ 0
  set C₃ := ∑ k ∈ Finset.range (k₂ + 1), C₂ * (k₂.choose k : ℝ) * (C₁ ^ k)
  use k₁ * k₂ + k₁ * n, n ! * C₃ * (1 + C₁) ^ n
  intro x
  have hg' : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C₃ * (1 + ‖x‖) ^ (k₁ * k₂) := by
    intro i hi
    calc _ ≤ C₂ * (1 + ‖f x‖) ^ k₂ := h₂ i hi (f x) (ht ⟨x, rfl⟩)
      _ = ∑ i ∈ Finset.range (k₂ + 1), C₂ * (‖f x‖ ^ i * (k₂.choose i)) := by
        rw [add_comm, add_pow, Finset.mul_sum]
        simp
      _ ≤ ∑ i ∈ Finset.range (k₂ + 1), C₂ * (k₂.choose i) * C₁ ^ i * (1 + ‖x‖) ^ (k₁ * k₂) := by
        apply Finset.sum_le_sum
        intro i hi
        grw [h₁']
        simp_rw [mul_pow, ← pow_mul]
        move_mul [← (k₂.choose _ : ℝ), C₂]
        gcongr
        · simp
        · grind
      _ = _ := by simp [C₃, Finset.sum_mul]
  have hf' : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ i := by
    intro i hi hi'
    calc _ ≤ C₁ * (1 + ‖x‖) ^ k₁ := h₁ i hi' x
      _ ≤ (1 + C₁) * (1 + ‖x‖) ^ k₁ := by gcongr; simp
      _ ≤ _ := by
        apply le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC₁]) (by simp [one_le_pow₀]))
        grind
  calc _ ≤ n ! * (C₃ * (1 + ‖x‖) ^ (k₁ * k₂)) * ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ n :=
      norm_iteratedFDeriv_comp_le' ht ht' hg₁ hf.1 (mod_cast le_top) x hg' hf'
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- Composition of two temperate growth functions is of temperate growth. -/
@[fun_prop]
/-
**Function.HasTemperateGrowth.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTemper
ateGrowth`。
形式化陈述：∀ {D : Type u_4} {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] [inst_4 : NormedAddCommGroup D] [inst_5 : NormedSpace ℝ D]   {g : E →
 F} {f : D → E},   Function.HasTemperateGrowth g → Function.HasTemperateGrowth f
 → Function.HasTemperateGrowth (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.comp'`：∀ {D : Type u_4} {E : Type u_5} {F : 
Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.HasTemperateGrowth.norm_iteratedFDeriv_le_uniform`：∀ {E : Type 
u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [in
st_2 : NormedAddCommGroup F]   [inst_3 : NormedS…

--- 原说明 ---
Composition of two temperate growth functions is of temperate growth.
-/
theorem HasTemperateGrowth.comp [NormedAddCommGroup D] [NormedSpace ℝ D] {g : E → F} {f : D → E}
    (hg : g.HasTemperateGrowth) (hf : f.HasTemperateGrowth) : (g ∘ f).HasTemperateGrowth := by
  apply hf.comp' (t := Set.univ)
  · simp
  · simp
  · rw [contDiffOn_univ]
    exact hg.1
  · simpa [iteratedFDerivWithin_univ] using hg.norm_iteratedFDeriv_le_uniform

section Addition

variable {f g : E → F}

@[to_fun (attr := fun_prop)]
/-
**Function.HasTemperateGrowth.neg** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f :
 E → F}, Function.HasTemperateGrowth f → Function.HasTemperateGrowth (-f)
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.neg`：ContDiff.neg {f : E -> F} (hf : ContDiff 𝕜 n f) : ContDiff
 𝕜 n fun x => -f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDeriv_neg_apply`：iteratedFDeriv_neg_apply {i : Nat} {f : E -> F
} : iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
theorem HasTemperateGrowth.neg (hf : f.HasTemperateGrowth) : (-f).HasTemperateGrowth := by
  refine ⟨hf.1.neg, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 n
  exact ⟨k, C, fun x ↦ by simpa [iteratedFDeriv_neg_apply] using h x⟩

@[to_fun (attr := fun_prop)]
/-
**Function.HasTemperateGrowth.add** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f g
 : E → F},   Function.HasTemperateGrowth f → Function.HasTemperateGrowth g → Fun
ction.HasTemperateGrowth (f + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.hasTemperateGrowth_iff_isBigO`：hasTemperateGrowth_iff_isBigO {f
 : E -> F} : f.HasTemperateGrowth ↔ ContDiff Real ∞ f ∧ forall n, exists k, iter
atedFDeriv Real n f =O[⊤] (f…
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iteratedFDeriv_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : 
Type uF}…
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_add_iff_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a ≤ a + b ↔ 0 
≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.pow_of_le_right`：∀ {α : Type u_1} {l : Filter α} {f :
 α → ℝ}, 1 ≤ᶠ[l] f → ∀ {m n : ℕ}, n ≤ m → (f ^ n) =O[l] (f ^ m)
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `Nat.le_max_right`：∀ (a b : ℕ), b ≤ max a b
-/
theorem HasTemperateGrowth.add (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (f + g).HasTemperateGrowth := by
  rw [hasTemperateGrowth_iff_isBigO] at *
  refine ⟨hf.1.add hg.1, fun n ↦ ?_⟩
  obtain ⟨k₁, h₁⟩ := hf.2 n
  obtain ⟨k₂, h₂⟩ := hg.2 n
  use max k₁ k₂
  rw [iteratedFDeriv_add (hf.1.of_le <| mod_cast le_top) (hg.1.of_le <| mod_cast le_top)]
  have : 1 ≤ᶠ[⊤] fun (x : E) ↦ 1 + ‖x‖ := by
    filter_upwards with _ using (le_add_iff_nonneg_right _).mpr (by positivity)
  exact (h₁.trans (IsBigO.pow_of_le_right this (k₁.le_max_left k₂))).add
    (h₂.trans (IsBigO.pow_of_le_right this (k₁.le_max_right k₂)))

@[to_fun (attr := fun_prop)]
/-
**Function.HasTemperateGrowth.sub** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {f g
 : E → F},   Function.HasTemperateGrowth f → Function.HasTemperateGrowth g → Fun
ction.HasTemperateGrowth (f - g)
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.HasTemperateGrowth.add`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `Function.HasTemperateGrowth.neg`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
-/
theorem HasTemperateGrowth.sub (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (f - g).HasTemperateGrowth := by
  convert hf.add hg.neg
  grind

@[fun_prop]
/-
**Function.HasTemperateGrowth.sum** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] {f : ι → E → F} {s : Finset ι},   (∀ i ∈ s, Function.HasTemperateGrow
th (f i)) → Function.HasTemperateGrowth fun x => ∑ i ∈ s, f i x
参数：∀ i ∈ s, Function.HasTemperateGrowth (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.HasTemperateGrowth.add`：∀ {E : Type u_5} {F : Type u_6} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
-/
theorem HasTemperateGrowth.sum {f : ι → E → F} {s : Finset ι}
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) : (∑ i ∈ s, f i ·).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨hf, h⟩ := by simpa using! hf
    simpa [has] using! hf.add (ih h)

end Addition

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The product of two functions of temperate growth is again of temperate growth.

Version for bilinear maps. -/
@[fun_prop]
/-
**Function._root_.ContinuousLinearMap.bilinear_hasTemperateGrowth** 是 Mathlib 中的
一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two functions of temperate growth is again of temperate growth.

Version for bilinear maps.
-/
theorem _root_.ContinuousLinearMap.bilinear_hasTemperateGrowth [NormedSpace 𝕜 E]
    (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (fun x ↦ B (f x) (g x)).HasTemperateGrowth := by
  rw [Function.hasTemperateGrowth_iff_isBigO]
  constructor
  · apply (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1)
  intro n
  rcases hf.isBigO_uniform n with ⟨k1, h1⟩
  rcases hg.isBigO_uniform n with ⟨k2, h2⟩
  use k1 + k2
  have estimate (x : D) : ‖iteratedFDeriv ℝ n (fun x ↦ B (f x) (g x)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
    (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear hf.1 hg.1 x (mod_cast le_top)
  refine (IsBigO.of_norm_le estimate).trans (.const_mul_left (.fun_sum fun i hi ↦ ?_) _)
  simp_rw [mul_assoc, pow_add]
  refine .const_mul_left (.mul (h1 i ?_).norm_left (h2 (n - i) ?_).norm_left) _ <;>
  grind
/-
**Function.HasTemperateGrowth.id** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTemperat
eGrowth`。
形式化陈述：∀ {E : Type u_5} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E],
 Function.HasTemperateGrowth id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.of_fderiv`：∀ {E : Type u_5} {F : Type u_6} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `fderiv_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : 
Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Top
olo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Function.HasTemperateGrowth.const`：∀ {E : Type u_5} {F : Type u_6} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma HasTemperateGrowth.id : Function.HasTemperateGrowth (id : E → E) := by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1)
  · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id ℝ E)
    exact fderiv_fun_id
  · apply differentiable_id
  · simp

@[fun_prop]
/-
**Function.HasTemperateGrowth.id'** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {E : Type u_5} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E],
 Function.HasTemperateGrowth fun x => x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.id`：∀ {E : Type u_5} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E], Function.HasTemperateGrowth id
-/
lemma HasTemperateGrowth.id' : Function.HasTemperateGrowth (fun (x : E) ↦ x) :=
  Function.HasTemperateGrowth.id

/-- The product of two functions of temperate growth is again of temperate growth.

Version for scalar multiplication. -/
@[to_fun (attr := fun_prop)]
/-
**Function.HasTemperateGrowth.smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTemper
ateGrowth`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] [inst_4 : NontriviallyNormedField 𝕜]   [inst_5 : NormedAlgebra ℝ 𝕜] [
inst_6 : NormedSpace 𝕜 F] {f : E → 𝕜} {g : E → F},   Function.HasTemperateGrowth
 f → Function.HasTemperateGrowth g → Function.HasTemperateGrowth (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.bilinear_hasTemperateGrowth`：∀ {𝕜 : Type u_2} {D : T
ype u_4} {E : Type u_5} {F : Type u_6} {G : Type u_7} [inst : NormedAddCommGroup
 E]   [inst_1 : NormedSpace ℝ E] [ins…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
The product of two functions of temperate growth is again of temperate growth.

Version for scalar multiplication.
-/
theorem HasTemperateGrowth.smul {f : E → 𝕜} {g : E → F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f • g).HasTemperateGrowth :=
  (ContinuousLinearMap.lsmul ℝ 𝕜).bilinear_hasTemperateGrowth hf hg

variable [NormedRing R] [NormedAlgebra ℝ R]

/-- The product of two functions of temperate growth is again of temperate growth. -/
@[to_fun (attr := fun_prop)]
/-
**Function.HasTemperateGrowth.mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {R : Type u_3} {E : Type u_5} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedRing R]   [inst_3 : NormedAlgebra ℝ R] {f g : E →
 R},   Function.HasTemperateGrowth f → Function.HasTemperateGrowth g → Function.
HasTemperateGrowth (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.bilinear_hasTemperateGrowth`：∀ {𝕜 : Type u_2} {D : T
ype u_4} {E : Type u_5} {F : Type u_6} {G : Type u_7} [inst : NormedAddCommGroup
 E]   [inst_1 : NormedSpace ℝ E] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The product of two functions of temperate growth is again of temperate growth.
-/
theorem HasTemperateGrowth.mul {f g : E → R} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f * g).HasTemperateGrowth :=
  (ContinuousLinearMap.mul ℝ R).bilinear_hasTemperateGrowth hf hg

@[to_fun (attr := fun_prop)]
/-
**Function.HasTemperateGrowth.pow** 是 Mathlib 中的一个定理，位于命名空间 `Function.HasTempera
teGrowth`。
形式化陈述：∀ {R : Type u_3} {E : Type u_5} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedRing R]   [inst_3 : NormedAlgebra ℝ R] {f : E → R
},   Function.HasTemperateGrowth f → ∀ (k : ℕ), Function.HasTemperateGrowth (f ^
 k)
参数：k : ℕ；f ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Function.HasTemperateGrowth.const`：∀ {E : Type u_5} {F : Type u_6} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Function.HasTemperateGrowth.mul`：∀ {R : Type u_3} {E : Type u_5} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedRing R]   [ins
t_3 : NormedAlgebra ℝ…
-/
theorem HasTemperateGrowth.pow {f : E → R} (hf : f.HasTemperateGrowth) (k : ℕ) :
    (f ^ k).HasTemperateGrowth := by
  induction k with
  | zero => simpa only [pow_zero] using! HasTemperateGrowth.const 1
  | succ k IH => rw [pow_succ]; fun_prop

end Multiplication

@[fun_prop]
/-
**Function._root_.ContinuousLinearMap.hasTemperateGrowth** 是 Mathlib 中的一个引理，位于命名
空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.hasTemperateGrowth (f : E →L[ℝ] F) :
    Function.HasTemperateGrowth f := by
  apply Function.HasTemperateGrowth.of_fderiv ?_ f.differentiable (k := 1) (C := ‖f‖) (fun x ↦ ?_)
  · have : fderiv ℝ f = fun _ ↦ f := by ext1 v; simp only [ContinuousLinearMap.fderiv]
    simp [this]
  · exact (f.le_opNorm x).trans (by simp [mul_add])

@[fun_prop]
/-
**Function._root_.ContinuousLinearEquiv.hasTemperateGrowth** 是 Mathlib 中的一个引理，位于
命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearEquiv.hasTemperateGrowth (f : E ≃L[ℝ] F) :
    Function.HasTemperateGrowth f :=
  f.toContinuousLinearMap.hasTemperateGrowth

@[fun_prop]
/-
**Function.Complex.hasTemperateGrowth_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Function
.Complex`。
形式化陈述：Function.HasTemperateGrowth Complex.ofReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
-/
theorem Complex.hasTemperateGrowth_ofReal : Complex.ofReal.HasTemperateGrowth :=
  (Complex.ofRealCLM).hasTemperateGrowth

variable (𝕜) in
@[fun_prop]
/-
**Function.RCLike.hasTemperateGrowth_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Function.
RCLike`。
形式化陈述：∀ (𝕜 : Type u_2) [inst : RCLike 𝕜], Function.HasTemperateGrowth RCLike.ofR
eal
参数：𝕜 : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
-/
theorem RCLike.hasTemperateGrowth_ofReal [RCLike 𝕜] : (RCLike.ofReal (K := 𝕜)).HasTemperateGrowth :=
  (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

@[fun_prop]
/-
**Function.hasTemperateGrowth_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：hasTemperateGrowth_inner_left (c : H) : (inner Real · c).HasTemperateGrowt
h
参数：c : H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `instCStarRingReal`：CStarRing ℝ
-/
theorem hasTemperateGrowth_inner_left (c : H) : (inner ℝ · c).HasTemperateGrowth :=
  ((innerSL ℝ).flip c).hasTemperateGrowth

@[fun_prop]
/-
**Function.hasTemperateGrowth_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：hasTemperateGrowth_inner_right (c : H) : (inner Real c ·).HasTemperateGrow
th
参数：c : H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem hasTemperateGrowth_inner_right (c : H) : (inner ℝ c ·).HasTemperateGrowth :=
  (innerSL ℝ c).hasTemperateGrowth

variable (H) in
@[fun_prop]
/-
**Function.hasTemperateGrowth_norm_sq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：hasTemperateGrowth_norm_sq : (fun (x : H) => ‖x‖ ^ 2).HasTemperateGrowth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.of_fderiv`：∀ {E : Type u_5} {F : Type u_6} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_norm_sq`：fderiv_norm_sq : fderiv Real (fun (x : F) => ‖x‖ ^ 2) = 
2 • (innerSL Real (E
· 使用定理 `LipschitzAdd.continuousAdd`：∀ {β : Type u_2} [inst : PseudoMetricSpace β
] [inst_1 : AddMonoid β] [LipschitzAdd β], ContinuousAdd β
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `Differentiable.norm_sq`：Differentiable.norm_sq (hf : Differentiable Real
 f) : Differentiable Real fun y => ‖f y‖ ^ 2
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_pow_two`：∀ {α : Type u} [inst : CommSemiring α] (a b : α), (a + b) ^
 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 44 条，此处仅展示前 30 条）
-/
theorem hasTemperateGrowth_norm_sq : (fun (x : H) ↦ ‖x‖ ^ 2).HasTemperateGrowth := by
  apply _root_.Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · rw [fderiv_norm_sq]
    convert! (2 • innerSL ℝ).hasTemperateGrowth
  · exact .norm_sq ℝ differentiable_id
  · intro x
    rw [norm_pow, norm_norm, one_mul, add_pow_two]
    exact le_add_of_nonneg_left (by positivity)

variable (H) in
/-- The Bessel potential `x ↦ (1 + ‖x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
/-
**Function.hasTemperateGrowth_one_add_norm_sq_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction`。
形式化陈述：hasTemperateGrowth_one_add_norm_sq_rpow (r : Real) : (fun (x : H) => (1 + 
‖x‖ ^ 2) ^ r).HasTemperateGrowth
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_add_of_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorde
r α] [AddLeftMono α] {a b c d : α}, a < b + c → c ≤ d → a < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `ContDiffOn.rpow_const_of_ne`：ContDiffOn.rpow_const_of_ne (hf : ContDiffO
n Real n f s) (h : forall x in s, f x != 0) : ContDiffOn Real n (fun x => f x ^ 
p) s
· 使用定理 `contDiffOn_fun_id`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyN
ormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {n : 
WithTop…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
（共 127 条，此处仅展示前 30 条）

--- 原说明 ---
The Bessel potential `x ↦ (1 + ‖x‖ ^ 2) ^ r` has temperate growth.
-/
theorem hasTemperateGrowth_one_add_norm_sq_rpow (r : ℝ) :
    (fun (x : H) ↦ (1 + ‖x‖ ^ 2) ^ r).HasTemperateGrowth := by
  /- We prove this using that the composition of temperate functions is temperate.
  Since `x ^ r` is not smooth at the origin, we have to use `HasTemperateGrowth.comp'`, with any
  open set `t` that is contains the complement of the unit ball and does not contain the origin. -/
  set t := {y : ℝ | 1 / 2 < y}
  have ht : Set.range (fun (x : H) ↦ (1 + ‖x‖ ^ 2)) ⊆ t := by
    rintro - ⟨y, rfl⟩
    simp only [Set.mem_ofPred_eq, t]
    exact lt_add_of_lt_add_left (c := 0) (by norm_num) (by positivity)
  have hdiff : ContDiffOn ℝ ∞ (fun x ↦ x ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx ↦ (lt_trans (by norm_num) hx).ne'
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  apply HasTemperateGrowth.comp' ht hunique hdiff _ (by fun_prop)
  -- The remaining part of the proof is proving that `x ↦ x ^ r` has temperate growth on `t`.
  -- This could be generalized to `t := {y : ℝ | ε < y}` for any `0 < ε < 1` if necessary.
  intro N
  /- Since `x ^ r` for negative `r` blows up near the origin (and we can't take
  `t := {y : ℝ | 1 / 2 < y}`), we have to choose `k` later than `N - r` times some factor depending
  on `t`. -/
  obtain ⟨k, hk⟩ := exists_nat_ge (max r <| (N - r) * Real.log 2 / (Real.log (3 / 2)))
  have hk₁ : r ≤ k := le_sup_left.trans hk
  have hk₂ : Real.log 2 * (N - r) ≤ (Real.log (3 / 2)) * k := by
    have := le_sup_right.trans hk
    field_simp at this
    grind
  use k, ∑ k ∈ Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer ℝ k)‖, by positivity
  intro n hn x hx
  have : ContDiffAt ℝ n (fun x ↦ x ^ r) x :=
    Real.contDiffAt_rpow_const <| Or.inl (lt_trans (by norm_num) hx).ne'
  -- We calculate the derivative of `x ^ r`.
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique this hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  gcongr 1
  · have : n ∈ Finset.range (N + 1) := by grind
    apply Finset.single_le_sum (fun _ _ ↦ by positivity) this
  -- It remains to show that `‖x ^ (r - n)‖ ≤ (1 + ‖x‖) ^ k`:
  have hx' : 1 / 2 < x := by simpa [t] using hx
  have hx'' : 0 < x := lt_of_lt_of_le (by norm_num) hx'.le
  simp only [Real.norm_eq_abs]
  apply (Real.abs_rpow_le_abs_rpow _ _).trans
  -- We consider the two cases `n ≤ r` and `r < n`.
  by_cases! h : 0 ≤ r - n
  · have : r - n ≤ k := by simpa using hk₁.trans (by simp)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
      (Real.rpow_le_rpow_of_exponent_le (by simp) this)
  have h : 0 < n - r := by grind
  calc
    /- In the case `0 < n - r`, we need the factor `Real.log 2 / (Real.log (3 / 2))` to control
    the growth near `‖x‖ = 1/2`. -/
    _ = x ^ (-(n - r)) := by
      rw [neg_sub]
      congr
      simpa using hx''.le
    _ ≤ (2 : ℝ) ^ (n - r) := by
      simp only [one_div, Set.mem_ofPred_eq, t] at hx
      rw [Real.rpow_neg_eq_inv_rpow]
      gcongr
      exact ((inv_lt_comm₀ hx'' (by norm_num)).mpr hx).le
    _ = Real.exp (Real.log 2 * (n - r)) := by
      rw [Real.rpow_def_of_pos]
      norm_num
    _ ≤ Real.exp (Real.log (3 / 2) * k) := by
      gcongr 1
      apply le_trans _ hk₂
      gcongr
    _ ≤ (3 / 2) ^ k := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos]
      norm_num
    _ ≤ _ := by
      gcongr
      grind

end Function

namespace MeasureTheory.Measure

variable [NormedAddCommGroup E] [MeasurableSpace E]

open Module
open scoped ENNReal

/-- A measure `μ` has temperate growth if there is an `n : ℕ` such that `(1 + ‖x‖) ^ (- n)` is
`μ`-integrable. -/
/-
**MeasureTheory.Measure.HasTemperateGrowth** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：{E : Type u_5} → [NormedAddCommGroup E] → [inst : MeasurableSpace E] → Mea
sureTheory.Measure E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` has temperate growth if there is an `n : ℕ` such that `(1 + ‖x‖) ^
 (- n)` is
`μ`-integrable.
-/
class HasTemperateGrowth (μ : Measure E) : Prop where
  exists_integrable : ∃ (n : ℕ), Integrable (fun x ↦ (1 + ‖x‖) ^ (- (n : ℝ))) μ

open scoped Classical in
/-- An integer exponent `l` such that `(1 + ‖x‖) ^ (-l)` is integrable if `μ` has
temperate growth. -/
/-
**MeasureTheory.Measure.integrablePower** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：integrablePower (μ : Measure E) : Nat
参数：μ : Measure E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HasTemperateGrowth.exists_integrable`：∀ {E : Type 
u_5} {inst : NormedAddCommGroup E} {inst_1 : MeasurableSpace E} {μ : MeasureTheo
ry.Measure E}   [self : μ.HasTemperateGrowth], ∃…

--- 原说明 ---
An integer exponent `l` such that `(1 + ‖x‖) ^ (-l)` is integrable if `μ` has
temperate growth.
-/
def integrablePower (μ : Measure E) : ℕ :=
  if h : μ.HasTemperateGrowth then h.exists_integrable.choose else 0
/-
**MeasureTheory.Measure.integrable_pow_neg_integrablePower** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：integrable_pow_neg_integrablePower (μ : Measure E) [h : μ.HasTemperateGrow
th] : Integrable (fun x => (1 + ‖x‖) ^ (- (μ.integrablePower : Real))) μ
参数：μ : Measure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HasTemperateGrowth.exists_integrable`：∀ {E : Type 
u_5} {inst : NormedAddCommGroup E} {inst_1 : MeasurableSpace E} {μ : MeasureTheo
ry.Measure E}   [self : μ.HasTemperateGrowth], ∃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.rpow_neg_natCast`：rpow_neg_natCast (x : Real) (n : Nat) : x ^ (-n :
 Real) = x ^ (-n : Int)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma integrable_pow_neg_integrablePower
    (μ : Measure E) [h : μ.HasTemperateGrowth] :
    Integrable (fun x ↦ (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ))) μ := by
  simpa [Measure.integrablePower, h] using h.exists_integrable.choose_spec
/-
**MeasureTheory.Measure._root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGro
wth** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth {μ : Measure E}
    [h : IsFiniteMeasure μ] : μ.HasTemperateGrowth := ⟨⟨0, by simp⟩⟩

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-
**MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.IsAddHaarMeasure`。
形式化陈述：∀ {E : Type u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E
] [inst_2 : NormedSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measu
reTheory.Measure E} [h : μ.IsAddHaarMeasure], μ.HasTemperateGrowth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integrable_one_add_norm`：integrable_one_add_norm {r : Real} (hnr : (finr
ank Real E : Real) < r) : Integrable (fun x => (1 + ‖x‖) ^ (-r)) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
instance IsAddHaarMeasure.instHasTemperateGrowth {μ : Measure E}
    [h : μ.IsAddHaarMeasure] : μ.HasTemperateGrowth :=
  ⟨⟨finrank ℝ E + 1, by apply integrable_one_add_norm; norm_num⟩⟩

/-- Pointwise inequality to control `x ^ k * f` in terms of `1 / (1 + x) ^ l` if one controls both
`f` (with a bound `C₁`) and `x ^ (k + l) * f` (with a bound `C₂`). This will be used to check
integrability of `x ^ k * f x` when `f` is a Schwartz function, and to control explicitly its
integral in terms of suitable seminorms of `f`. -/
/-
**MeasureTheory.Measure._root_.pow_mul_le_of_le_of_pow_mul_le** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise inequality to control `x ^ k * f` in terms of `1 / (1 + x) ^ l` if one
 controls both
`f` (with a bound `C₁`) and `x ^ (k + l) * f` (with a bound `C₂`). This will be 
used to check
integrability of `x ^ k * f x` when `f` is a Schwartz function, and to control e
xplicitly its
integral in terms of suitable seminorms of `f`.
-/
lemma _root_.pow_mul_le_of_le_of_pow_mul_le {C₁ C₂ : ℝ} {k l : ℕ} {x f : ℝ} (hx : 0 ≤ x)
    (hf : 0 ≤ f) (h₁ : f ≤ C₁) (h₂ : x ^ (k + l) * f ≤ C₂) :
    x ^ k * f ≤ 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : ℝ)) := by
  have : 0 ≤ C₂ := le_trans (by positivity) h₂
  have : 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : ℝ)) = ((1 + x) / 2) ^ (-(l : ℝ)) * (C₁ + C₂) := by
    rw [Real.div_rpow (by positivity) zero_le_two]
    simp [div_eq_inv_mul, ← Real.rpow_neg_one, ← Real.rpow_mul]
    ring
  rw [this]
  rcases le_total x 1 with h'x | h'x
  · gcongr
    · apply (pow_le_one₀ hx h'x).trans
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      · positivity
      · linarith
      · simp
    · linarith
  · calc
    x ^ k * f = x ^ (-(l : ℝ)) * (x ^ (k + l) * f) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← mul_assoc, ← Real.rpow_add (by positivity)]
      simp
    _ ≤ ((1 + x) / 2) ^ (-(l : ℝ)) * (C₁ + C₂) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
      · exact h₂.trans (by linarith)

variable [NormedAddCommGroup F]

variable [BorelSpace E] [SecondCountableTopology E] in
/-- Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable `l`, then
`x ^ k * f` is integrable. The bounds are not relevant for the integrability conclusion, but they
are relevant for bounding the integral in `integral_pow_mul_le_of_le_of_pow_mul_le`. We formulate
the two lemmas with the same set of assumptions for ease of applications. -/
/-
**MeasureTheory.Measure._root_.integrable_of_le_of_pow_mul_le** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable 
`l`, then
`x ^ k * f` is integrable. The bounds are not relevant for the integrability con
clusion, but they
are relevant for bounding the integral in `integral_pow_mul_le_of_le_of_pow_mul_
le`. We formulate
the two lemmas with the same set of assumptions for ease of applications.
-/
lemma _root_.integrable_of_le_of_pow_mul_le {μ : Measure E} [μ.HasTemperateGrowth] {f : E → F}
    {C₁ C₂ : ℝ} {k : ℕ} (hf : ∀ x, ‖f x‖ ≤ C₁)
    (h'f : ∀ x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ ≤ C₂) (h''f : AEStronglyMeasurable f μ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖) μ := by
  apply ((integrable_pow_neg_integrablePower μ).const_mul (2 ^ μ.integrablePower * (C₁ + C₂))).mono'
  · exact AEStronglyMeasurable.mul (aestronglyMeasurable_id.norm.pow _) h''f.norm
  · filter_upwards with v
    simp only [norm_mul, norm_pow, norm_norm]
    apply pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)

/-- Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable `l`, then
one can bound explicitly the integral of `x ^ k * f`. -/
/-
**MeasureTheory.Measure._root_.integral_pow_mul_le_of_le_of_pow_mul_le** 是 Mathl
ib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable 
`l`, then
one can bound explicitly the integral of `x ^ k * f`.
-/
lemma _root_.integral_pow_mul_le_of_le_of_pow_mul_le
    {μ : Measure E} [μ.HasTemperateGrowth] {f : E → F} {C₁ C₂ : ℝ} {k : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ C₁) (h'f : ∀ x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ ≤ C₂) :
    ∫ x, ‖x‖ ^ k * ‖f x‖ ∂μ ≤ 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ)) ∂μ) * (C₁ + C₂) := by
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_mono_of_nonneg
  · filter_upwards with v using by positivity
  · exact ((integrable_pow_neg_integrablePower μ).const_mul _).mul_const _
  filter_upwards with v
  exact (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)).trans
    (le_of_eq (by ring))

/-- For any `HasTemperateGrowth` measure and `p`, there exists an integer power `k` such that
`(1 + ‖x‖) ^ (-k)` is in `L^p`. -/
/-
**MeasureTheory.Measure.HasTemperateGrowth.exists_eLpNorm_lt_top** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure.HasTemperateGrowth`。
形式化陈述：∀ {E : Type u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E
] (p : ENNReal) {μ : MeasureTheory.Measure E},   μ.HasTemperateGrowth → ∃ k, Mea
sureTheory.eLpNorm (fun x => (1 + ‖x‖) ^ (-↑k)) p μ < ⊤
参数：p : ENNReal；fun x => (1 + ‖x‖) ^ (-↑k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound`：eLpNormEssSup_lt_top_of_
ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNormEssSu
p f μ < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `lt_add_of_pos_of_le`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddRightStrictMono α] {a b c : α},   0 < a → b ≤ c → b < a + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MeasureTheory.Measure.HasTemperateGrowth.exists_integrable`：∀ {E : Type 
u_5} {inst : NormedAddCommGroup E} {inst_1 : MeasurableSpace E} {μ : MeasureTheo
ry.Measure E}   [self : μ.HasTemperateGrowth], ∃…
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
For any `HasTemperateGrowth` measure and `p`, there exists an integer power `k` 
such that
`(1 + ‖x‖) ^ (-k)` is in `L^p`.
-/
theorem HasTemperateGrowth.exists_eLpNorm_lt_top (p : ℝ≥0∞)
    {μ : Measure E} (hμ : μ.HasTemperateGrowth) :
    ∃ k : ℕ, eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ < ⊤ := by
  cases p with
  | top => exact ⟨0, eLpNormEssSup_lt_top_of_ae_bound (C := 1) (by simp)⟩
  | coe p =>
    cases eq_or_ne (p : ℝ≥0∞) 0 with
    | inl hp => exact ⟨0, by simp [hp]⟩
    | inr hp =>
      have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
      have hp_pos : 0 < (p : ℝ) := by simpa [zero_lt_iff] using hp
      rcases hμ.exists_integrable with ⟨l, hl⟩
      let k := ⌈(l / p : ℝ)⌉₊
      have hlk : l ≤ k * (p : ℝ) := by simpa [div_le_iff₀ hp_pos] using Nat.le_ceil (l / p : ℝ)
      use k
      suffices HasFiniteIntegral (fun x ↦ ((1 + ‖x‖) ^ (-(k * p) : ℝ))) μ by
        rw [hasFiniteIntegral_iff_enorm] at this
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp ENNReal.coe_ne_top]
        simp only [ENNReal.coe_toReal]
        refine Eq.subst (motive := (∫⁻ x, · x ∂μ < ⊤)) (funext fun x ↦ ?_) this
        rw [← neg_mul, Real.rpow_mul (h_one_add x).le]
        exact Real.enorm_rpow_of_nonneg (by positivity) NNReal.zero_le_coe
      refine hl.hasFiniteIntegral.mono' (ae_of_all μ fun x ↦ ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (h_one_add x).le _)]
      gcongr
      simp

end MeasureTheory.Measure

