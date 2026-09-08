/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Eventual sign of polynomials

This file proves that a polynomial has a fixed sign beyond its largest or smallest root.

## Main statements

* `zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`:
  If `x` is larger than all roots of `P` and the leading coefficient of `P` is nonnegative
  then `P (x)` is positive.
* `zero_le_eval_of_roots_le_of_leadingCoeff_nonneg`:
  If we only assume that `x` is at least as large as all roots, then `P (x)` is nonnegative.
* `eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos`,
  `eval_le_zero_of_roots_le_of_leadingCoeff_nonpos`:
  Versions of the above when the leading coefficient of `P` is nonpositive.
* `zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg`,
  `zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg`,
  `negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos`,
  `negOnePow_mul_eval_le_zero_of_le_roots_of_leadingCoeff_nonpos`:
  Analogous results for `x` which is smaller than (or at least as small as) all roots.

## TODO

Generalize to real-closed fields.
-/

public section

open Real Polynomial

namespace Polynomial

section PolynomialSign

variable {P : ℝ[X]} {x : ℝ}

/-
**Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (hroots : forall y, P.IsRo
ot y -> y < x) (hlc : 0 <= P.leadingCoeff) : 0 < P.eval x
参数：hroots : forall y, P.IsRoot y -> y < x；hlc : 0 <= P.leadingCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Filter.Eventually.exists_forall_of_atTop`：∀ {α : Type u_3} [inst : Preor
der α] [IsDirectedOrder α] {p : α → Prop} [Nonempty α],   (∀ᶠ (x : α) in Filter.
atTop, p x) → ∃ a, ∀ (b : α), …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`：tendsto_atTop_of_leadin
gCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 <= P.leadingCoeff) : Tendsto (fun 
x => eval x P) atTop atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
（共 44 条，此处仅展示前 30 条）
-/
theorem zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → y < x) (hlc : 0 ≤ P.leadingCoeff) : 0 < P.eval x := by
  replace hlc : 0 < P.leadingCoeff := by
    contrapose! hroots
    exact ⟨x, by simp [leadingCoeff_eq_zero.mp <| eq_of_le_of_ge hroots hlc], le_refl x⟩
  by_cases! hdeg : P.degree ≤ 0
  · rwa [eq_C_of_degree_le_zero hdeg, ← natDegree_eq_zero_iff_degree_le_zero.mpr hdeg, eval_C]
  contrapose! hroots
  obtain ⟨z, hz⟩ := Filter.Eventually.exists_forall_of_atTop <|
    (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le).eventually_gt_atTop 0
  let w := max x z
  have hw : x ≤ w ∧ 0 < P.eval w := ⟨le_max_left .., hz w (le_max_right ..)⟩
  obtain ⟨y, hy⟩ := (Set.mem_image ..).mp
    (intermediate_value_Icc hw.1 P.continuous.continuousOn (show 0 ∈ _ by grind))
  exact ⟨y, ⟨hy.2, by grind⟩⟩
/-
**Polynomial.zero_le_eval_of_roots_le_of_leadingCoeff_nonneg** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：zero_le_eval_of_roots_le_of_leadingCoeff_nonneg (hroots : forall y, P.IsRo
ot y -> y <= x) (hlc : 0 <= P.leadingCoeff) : 0 <= P.eval x
参数：hroots : forall y, P.IsRoot y -> y <= x；hlc : 0 <= P.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`：zero_lt_eval
_of_roots_lt_of_leadingCoeff_nonneg (hroots : forall y, P.IsRoot y -> y < x) (hl
c : 0 <= P.leadingCoeff) : 0 < P.eval x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem zero_le_eval_of_roots_le_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → y ≤ x) (hlc : 0 ≤ P.leadingCoeff) : 0 ≤ P.eval x := by
  by_cases! hroots' : ∃ y, P.IsRoot y ∧ x ≤ y
  · obtain ⟨y, hroot, hle⟩ := hroots'
    rw [eq_of_le_of_ge hle (hroots y hroot), hroot]
  · exact (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots' hlc).le
/-
**Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos (hroots : forall y, P.IsRo
ot y -> y < x) (hlc : P.leadingCoeff <= 0) : P.eval x < 0
参数：hroots : forall y, P.IsRoot y -> y < x；hlc : P.leadingCoeff <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`：zero_lt_eval
_of_roots_lt_of_leadingCoeff_nonneg (hroots : forall y, P.IsRoot y -> y < x) (hl
c : 0 <= P.leadingCoeff) : 0 < P.eval x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, a ≤ -b ↔ b ≤ -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → y < x) (hlc : P.leadingCoeff ≤ 0) : P.eval x < 0 := by
  suffices 0 < (-P).eval x by apply neg_pos.mp; rwa [← eval_neg]
  refine zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, le_neg, neg_zero]
/-
**Polynomial.eval_le_zero_of_roots_le_of_leadingCoeff_nonpos** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：eval_le_zero_of_roots_le_of_leadingCoeff_nonpos (hroots : forall y, P.IsRo
ot y -> y <= x) (hlc : P.leadingCoeff <= 0) : P.eval x <= 0
参数：hroots : forall y, P.IsRoot y -> y <= x；hlc : P.leadingCoeff <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.zero_le_eval_of_roots_le_of_leadingCoeff_nonneg`：zero_le_eval
_of_roots_le_of_leadingCoeff_nonneg (hroots : forall y, P.IsRoot y -> y <= x) (h
lc : 0 <= P.leadingCoeff) : 0 <= P.eval x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem eval_le_zero_of_roots_le_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → y ≤ x) (hlc : P.leadingCoeff ≤ 0) : P.eval x ≤ 0 := by
  suffices 0 ≤ (-P).eval x by apply neg_nonneg.mp; rwa [← eval_neg]
  refine zero_le_eval_of_roots_le_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, neg_nonneg]
/-
**Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg** 是 M
athlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (hroots : fo
rall y, P.IsRoot y -> x < y) (hlc : 0 <= P.leadingCoeff) : 0 < Int.negOnePow P.n
atDegree * P.eval x
参数：hroots : forall y, P.IsRoot y -> x < y；hlc : 0 <= P.leadingCoeff。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.comp_neg_X_leadingCoeff_eq`：∀ {R : Type u} [inst : Ring R] (p
 : Polynomial R),   (p.comp (-Polynomial.X)).leadingCoeff = (-1) ^ p.natDegree *
 p.leadingCoeff
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_prod_atom`：∀ {R : Type u_1} [inst : CommS
emiring R] (a : R) (b : ℕ) {e : R}, (a + 0) ^ b * Nat.rawCast 1 = e → a ^ b = e
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 70 条，此处仅展示前 30 条）
-/
theorem zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → x < y) (hlc : 0 ≤ P.leadingCoeff) :
      0 < Int.negOnePow P.natDegree * P.eval x := by
  have hroots' y (hy : (P.comp (-X)).IsRoot y) : y < -x := by
    grind [show P.IsRoot (-y) by rwa [IsRoot.def, eval_comp, eval_neg, eval_X, ← IsRoot.def] at hy]
  have hlc' : 0 ≤ Int.negOnePow (P.comp (-X)).natDegree * (P.comp (-X)).leadingCoeff := by
    rw [show (P.comp (-X)).leadingCoeff = P.leadingCoeff * Int.negOnePow P.natDegree by simp; ring,
      show (P.comp (-X)).natDegree = P.natDegree by simp [natDegree_comp], mul_comm, mul_assoc]
    simpa [Int.cast_negOnePow_natCast, pow_right_comm]
  cases P.natDegree.even_or_odd
  case inl h =>
    rw [Int.negOnePow_even] at hlc' ⊢
    · push_cast at hlc' ⊢; rw [one_mul] at hlc' ⊢
      have := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots' hlc'
      simpa using this
    · simpa
    · simpa [natDegree_comp]
  case inr h =>
    rw [Int.negOnePow_odd] at hlc' ⊢
    · push_cast at hlc' ⊢; rw [neg_one_mul] at hlc' ⊢
      have := eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hroots' (nonpos_of_neg_nonneg hlc')
      exact neg_pos.mpr (by simpa using this)
    · simpa
    · simpa [natDegree_comp]
/-
**Polynomial.zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg** 是 M
athlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg (hroots : fo
rall y, P.IsRoot y -> x <= y) (hlc : 0 <= P.leadingCoeff) : 0 <= Int.negOnePow P
.natDegree * P.eval x
参数：hroots : forall y, P.IsRoot y -> x <= y；hlc : 0 <= P.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_ge_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤ 
a → a ≤ b → a = b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
`：zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (hroots : forall
 y, P.IsRoot y -> x < y) (hlc : 0 <= P.leadingCoeff) : 0 < Int…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → x ≤ y) (hlc : 0 ≤ P.leadingCoeff) :
      0 ≤ Int.negOnePow P.natDegree * P.eval x := by
  by_cases! hroots' : ∃ y, P.IsRoot y ∧ y ≤ x
  · obtain ⟨y, hroot, hle⟩ := hroots'
    rw [eq_of_ge_of_le hle (hroots y hroot), hroot, mul_zero]
  · exact (zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg hroots' hlc).le
/-
**Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos** 是 M
athlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos (hroots : fo
rall y, P.IsRoot y -> x < y) (hlc : P.leadingCoeff <= 0) : Int.negOnePow P.natDe
gree * P.eval x < 0
参数：hroots : forall y, P.IsRoot y -> x < y；hlc : P.leadingCoeff <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
`：zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (hroots : forall
 y, P.IsRoot y -> x < y) (hlc : 0 <= P.leadingCoeff) : 0 < Int…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, a ≤ -b ↔ b ≤ -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → x < y) (hlc : P.leadingCoeff ≤ 0) :
      Int.negOnePow P.natDegree * P.eval x < 0 := by
  suffices 0 < Int.negOnePow (-P).natDegree * (-P).eval x by apply neg_pos.mp; simpa
  refine zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, le_neg, neg_zero]
/-
**Polynomial.negOnePow_mul_eval_le_zero_of_le_roots_of_leadingCoeff_nonpos** 是 M
athlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：negOnePow_mul_eval_le_zero_of_le_roots_of_leadingCoeff_nonpos (hroots : fo
rall y, P.IsRoot y -> x <= y) (hlc : P.leadingCoeff <= 0) : Int.negOnePow P.natD
egree * P.eval x <= 0
参数：hroots : forall y, P.IsRoot y -> x <= y；hlc : P.leadingCoeff <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg
`：zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg (hroots : forall
 y, P.IsRoot y -> x <= y) (hlc : 0 <= P.leadingCoeff) : 0 <= I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem negOnePow_mul_eval_le_zero_of_le_roots_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → x ≤ y) (hlc : P.leadingCoeff ≤ 0) :
      Int.negOnePow P.natDegree * P.eval x ≤ 0 := by
  suffices 0 ≤ Int.negOnePow (-P).natDegree * (-P).eval x by apply neg_nonneg.mp; simpa
  refine zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, neg_nonneg]

end PolynomialSign

end Polynomial

