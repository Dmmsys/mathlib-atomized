/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

universe u v w

open Topology Filter Asymptotics Set
open scoped Nat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {m : ℤ}

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

/-
**hasStrictDerivAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) : HasStrictD
erivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
参数：m : Int；x : 𝕜；h : x != 0 ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `hasStrictDerivAt_pow`：hasStrictDerivAt_pow (n : Nat) (x : 𝕜) : HasStrict
DerivAt (fun x : 𝕜 => x ^ n) (n * x ^ (n - 1)) x
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.scomp`：HasStrictDerivAt.scomp (hg : HasStrictDerivAt g₁
 g₁' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (g₁ ∘ h) (h' • g₁'
) x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `hasStrictDerivAt_inv`：hasStrictDerivAt_inv (hx : x != 0) : HasStrictDeri
vAt Inv.inv (-(x ^ 2)⁻¹) x
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
### Derivative of `x ↦ x^m` for `m : ℤ`
-/
theorem hasStrictDerivAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x := by
  have : ∀ m : ℤ, 0 < m → HasStrictDerivAt (· ^ m) ((m : 𝕜) * x ^ (m - 1)) x := fun m hm ↦ by
    lift m to ℕ using hm.le
    simp only [zpow_natCast, Int.cast_natCast]
    convert hasStrictDerivAt_pow m x
    rw [← Int.ofNat_one, ← Int.ofNat_sub, zpow_natCast]
    norm_cast at hm
  rcases lt_trichotomy m 0 with (hm | hm | hm)
  · have hx : x ≠ 0 := h.resolve_right hm.not_ge
    have := (hasStrictDerivAt_inv ?_).scomp _ (this (-m) (neg_pos.2 hm)) <;>
      [skip; exact zpow_ne_zero _ hx]
    simp only [Function.comp_def, zpow_neg, inv_inv, smul_eq_mul] at this
    convert! this using 1
    rw [sq, mul_inv, inv_inv, Int.cast_neg, neg_mul, neg_mul_neg, ← zpow_add₀ hx, mul_assoc, ←
      zpow_add₀ hx]
    congr
    abel
  · simp only [hm, zpow_zero, Int.cast_zero, zero_mul, hasStrictDerivAt_const]
  · exact this m hm
/-
**hasDerivAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) : HasDerivAt (fun 
x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
参数：m : Int；x : 𝕜；h : x != 0 ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `hasStrictDerivAt_zpow`：hasStrictDerivAt_zpow (m : Int) (x : 𝕜) (h : x !=
 0 ∨ 0 <= m) : HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
-/
theorem hasDerivAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  (hasStrictDerivAt_zpow m x h).hasDerivAt
/-
**hasDerivWithinAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) (s : Set 𝕜) 
: HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x
参数：m : Int；x : 𝕜；h : x != 0 ∨ 0 <= m；s : Set 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `hasDerivAt_zpow`：hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
 : HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
-/
theorem hasDerivWithinAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x :=
  (hasDerivAt_zpow m x h).hasDerivWithinAt
/-
**differentiableAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x != 0 ∨ 0
 <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedField.continuousAt_zpow`：∀ {𝕜 : Type u_4} [inst : NontriviallyNorm
edField 𝕜] {n : ℤ} {x : 𝕜}, ContinuousAt (fun x => x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_zpow`：hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
 : HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
-/
theorem differentiableAt_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  ⟨fun H => NormedField.continuousAt_zpow.1 H.continuousAt, fun H =>
    (hasDerivAt_zpow m x H).differentiableAt⟩
/-
**differentiableWithinAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) : Diff
erentiableWithinAt 𝕜 (fun x => x ^ m) s x
参数：m : Int；x : 𝕜；h : x != 0 ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_zpow`：differentiableAt_zpow : DifferentiableAt 𝕜 (fun x
 => x ^ m) x ↔ x != 0 ∨ 0 <= m
-/
theorem differentiableWithinAt_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x :=
  (differentiableAt_zpow.mpr h).differentiableWithinAt
/-
**differentiableOn_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_zpow (m : Int) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 <= m) : D
ifferentiableOn 𝕜 (fun x => x ^ m) s
参数：m : Int；s : Set 𝕜；h : (0 : 𝕜) ∉ s ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_zpow`：differentiableWithinAt_zpow (m : Int) (x : 
𝕜) (h : x != 0 ∨ 0 <= m) : DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem differentiableOn_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
  differentiableWithinAt_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs
/-
**deriv_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_zpow (m : Int) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1)
参数：m : Int；x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_zpow`：hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
 : HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableAt_zpow`：differentiableAt_zpow : DifferentiableAt 𝕜 (fun x
 => x ^ m) x ↔ x != 0 ∨ 0 <= m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases H : x ≠ 0 ∨ 0 ≤ m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push Not at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne, mul_zero]

@[simp]
/-
**deriv_zpow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_zpow' (m : Int) : (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x 
^ (m - 1)
参数：m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_zpow`：deriv_zpow (m : Int) (x : 𝕜) : deriv (fun x => x ^ m) x = m 
* x ^ (m - 1)
-/
theorem deriv_zpow' (m : ℤ) : (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1) :=
  funext <| deriv_zpow m
/-
**derivWithin_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x != 0 ∨ 0 <= m) : 
derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : x != 0 ∨ 0 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `hasDerivWithinAt_zpow`：hasDerivWithinAt_zpow (m : Int) (x : 𝕜) (h : x !=
 0 ∨ 0 <= m) (s : Set 𝕜) : HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m -
 1)) s x
-/
theorem derivWithin_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x ≠ 0 ∨ 0 ≤ m) :
    derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1) :=
  (hasDerivWithinAt_zpow m x h s).derivWithin hxs

@[simp]
/-
**iter_deriv_zpow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_zpow' (m : Int) (k : Nat) : (deriv^[k] fun x : 𝕜 => x ^ m) = fu
n x => (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k)
参数：m : Int；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_range_zero`：prod_range_zero (f : Nat -> M) : ∏ k in range 0,
 f k = 1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `deriv_const_mul_field'`：deriv_const_mul_field' (u : 𝕜') : (deriv fun x =
> u * v x) = fun x => u * deriv v x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_zpow'`：deriv_zpow' (m : Int) : (deriv fun x : 𝕜 => x ^ m) = fun x 
=> (m : 𝕜) * x ^ (m - 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem iter_deriv_zpow' (m : ℤ) (k : ℕ) :
    (deriv^[k] fun x : 𝕜 => x ^ m) =
      fun x => (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) := by
  induction k with
  | zero =>
    simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero, Function.iterate_zero]
  | succ k ihk =>
    simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.natCast_succ, ← sub_sub, Int.cast_sub, Int.cast_natCast,
      mul_assoc]
/-
**iter_deriv_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_zpow (m : Int) (x : 𝕜) (k : Nat) : deriv^[k] (fun y => y ^ m) x
 = (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k)
参数：m : Int；x : 𝕜；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `iter_deriv_zpow'`：iter_deriv_zpow' (m : Int) (k : Nat) : (deriv^[k] fun 
x : 𝕜 => x ^ m) = fun x => (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k)
-/
theorem iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
    deriv^[k] (fun y => y ^ m) x = (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x
/-
**iter_deriv_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_pow (n : Nat) (x : 𝕜) (k : Nat) : deriv^[k] (fun x : 𝕜 => x ^ n
) x = (∏ i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k)
参数：n : Nat；x : 𝕜；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iter_deriv_zpow`：iter_deriv_zpow (m : Int) (x : 𝕜) (k : Nat) : deriv^[k]
 (fun y => y ^ m) x = (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    deriv^[k] (fun x : 𝕜 => x ^ n) x = (∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) := by
  simp only [← zpow_natCast, iter_deriv_zpow, Int.cast_natCast]
  rcases le_or_gt k n with hkn | hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i ∈ Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]

@[simp]
/-
**iter_deriv_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_pow' (n k : Nat) : (deriv^[k] fun x : 𝕜 => x ^ n) = fun x => (∏
 i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iter_deriv_pow`：iter_deriv_pow (n : Nat) (x : 𝕜) (k : Nat) : deriv^[k] (
fun x : 𝕜 => x ^ n) x = (∏ i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k)
-/
theorem iter_deriv_pow' (n k : ℕ) :
    (deriv^[k] fun x : 𝕜 => x ^ n) =
      fun x => (∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k
/-
**iter_deriv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_inv (k : Nat) (x : 𝕜) : deriv^[k] Inv.inv x = (-1) ^ k * k ! * 
x ^ (-1 - k : Int)
参数：k : Nat；x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `iter_deriv_zpow`：iter_deriv_zpow (m : Int) (x : 𝕜) (k : Nat) : deriv^[k]
 (fun y => y ^ m) x = (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k)
· 使用引理 `Finset.prod_neg`：prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι -> M) 
: ∏ x in s, -f x = (-1) ^ #s * ∏ x in s, f x
· 使用定理 `Finset.prod_Ico_eq_prod_range`：prod_Ico_eq_prod_range (f : Nat -> M) (m 
n : Nat) : ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k)
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
theorem iter_deriv_inv (k : ℕ) (x : 𝕜) :
    deriv^[k] Inv.inv x = (-1) ^ k * k ! * x ^ (-1 - k : ℤ) := calc
  deriv^[k] Inv.inv x = deriv^[k] (· ^ (-1 : ℤ)) x := by simp
  _ = (∏ i ∈ Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) := mod_cast iter_deriv_zpow (-1) x k
  _ = (-1) ^ k * k ! * x ^ (-1 - k : ℤ) := by
    simp only [← neg_add', Finset.prod_neg, ← Finset.prod_Ico_id_eq_factorial,
      Finset.prod_Ico_eq_prod_range]
    simp

@[simp]
/-
**iter_deriv_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_inv' (k : Nat) : deriv^[k] Inv.inv = fun x : 𝕜 => (-1) ^ k * k 
! * x ^ (-1 - k : Int)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iter_deriv_inv`：iter_deriv_inv (k : Nat) (x : 𝕜) : deriv^[k] Inv.inv x =
 (-1) ^ k * k ! * x ^ (-1 - k : Int)
-/
theorem iter_deriv_inv' (k : ℕ) :
    deriv^[k] Inv.inv = fun x : 𝕜 => (-1) ^ k * k ! * x ^ (-1 - k : ℤ) :=
  funext (iter_deriv_inv k)

open Nat Function in
/-
**iter_deriv_inv_linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_inv_linear (k : Nat) (c d : 𝕜) : deriv^[k] (fun x => (c * x + d
)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (c * x + d) ^ (-1 - k : Int))
参数：k : Nat；c d : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const_mul_field'`：deriv_const_mul_field' (u : 𝕜') : (deriv fun x =
> u * v x) = fun x => u * deriv v x
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 119 条，此处仅展示前 30 条）
-/
theorem iter_deriv_inv_linear (k : ℕ) (c d : 𝕜) :
    deriv^[k] (fun x ↦ (c * x + d)⁻¹) =
    (fun x : 𝕜 ↦ (-1) ^ k * k ! * c ^ k * (c * x + d) ^ (-1 - k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [factorial_succ, add_comm k 1, iterate_add_apply, ihk]
    ext z
    simp only [Int.reduceNeg, iterate_one, deriv_const_mul_field', cast_add, cast_one]
    by_cases hd : c = 0
    · simp [hd]
    · have := deriv_comp_add_const (fun x ↦ (c * x) ^ (-1 - k : ℤ)) (d / c) z
      have h0 : (fun x ↦ (c * (x + d / c)) ^ (-1 - (k : ℤ))) =
        (fun x ↦ (c * x + d) ^ (-1 - (k : ℤ))) := by
        ext y
        field_simp
      rw [h0, deriv_comp_mul_left c (fun x ↦ (x) ^ (-1 - k : ℤ)) (z + d / c)] at this
      simp [this]
      field_simp
      ring_nf
/-
**iter_deriv_inv_linear_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iter_deriv_inv_linear_sub (k : Nat) (c d : 𝕜) : deriv^[k] (fun x => (c * x
 - d)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (c * x - d) ^ (-1 - k : Int))
参数：k : Nat；c d : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iter_deriv_inv_linear`：iter_deriv_inv_linear (k : Nat) (c d : 𝕜) : deriv
^[k] (fun x => (c * x + d)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (c * x + 
d) ^ (-1 - …
-/
theorem iter_deriv_inv_linear_sub (k : ℕ) (c d : 𝕜) :
    deriv^[k] (fun x ↦ (c * x - d)⁻¹) =
    (fun x : 𝕜 ↦ (-1) ^ k * k ! * c ^ k * (c * x - d) ^ (-1 - k : ℤ)) := by
  simpa [sub_eq_add_neg] using iter_deriv_inv_linear k c (-d)

variable {f : E → 𝕜} {t : Set E} {a : E}

@[fun_prop]
/-
**DifferentiableWithinAt.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a
 != 0 ∨ 0 <= m) : DifferentiableWithinAt 𝕜 (fun x => f x ^ m) t a
参数：hf : DifferentiableWithinAt 𝕜 f t a；h : f a != 0 ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_zpow`：differentiableAt_zpow : DifferentiableAt 𝕜 (fun x
 => x ^ m) x ↔ x != 0 ∨ 0 <= m
-/
theorem DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ m) t a :=
  (differentiableAt_zpow.2 h).comp_differentiableWithinAt a hf

@[fun_prop]
/-
**DifferentiableAt.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : f a != 0 ∨ 0 <= m
) : DifferentiableAt 𝕜 (fun x => f x ^ m) a
参数：hf : DifferentiableAt 𝕜 f a；h : f a != 0 ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_zpow`：differentiableAt_zpow : DifferentiableAt 𝕜 (fun x
 => x ^ m) x ↔ x != 0 ∨ 0 <= m
-/
theorem DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : f a ≠ 0 ∨ 0 ≤ m) :
    DifferentiableAt 𝕜 (fun x => f x ^ m) a :=
  (differentiableAt_zpow.2 h).comp a hf

@[fun_prop]
/-
**DifferentiableOn.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) (h : (forall x in t, f
 x != 0) ∨ 0 <= m) : DifferentiableOn 𝕜 (fun x => f x ^ m) t
参数：hf : DifferentiableOn 𝕜 f t；h : (forall x in t, f x != 0) ∨ 0 <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.zpow`：DifferentiableWithinAt.zpow (hf : Different
iableWithinAt 𝕜 f t a) (h : f a != 0 ∨ 0 <= m) : DifferentiableWithinAt 𝕜 (fun x
 => f x ^ m) t a
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
-/
theorem DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) (h : (∀ x ∈ t, f x ≠ 0) ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => f x ^ m) t := fun x hx =>
  (hf x hx).zpow <| h.imp_left fun h => h x hx

@[fun_prop]
/-
**Differentiable.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.zpow (hf : Differentiable 𝕜 f) (h : (forall x, f x != 0) ∨ 
0 <= m) : Differentiable 𝕜 fun x => f x ^ m
参数：hf : Differentiable 𝕜 f；h : (forall x, f x != 0) ∨ 0 <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.zpow`：DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f 
a) (h : f a != 0 ∨ 0 <= m) : DifferentiableAt 𝕜 (fun x => f x ^ m) a
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
-/
theorem Differentiable.zpow (hf : Differentiable 𝕜 f) (h : (∀ x, f x ≠ 0) ∨ 0 ≤ m) :
    Differentiable 𝕜 fun x => f x ^ m := fun x => (hf x).zpow <| h.imp_left fun h => h x
