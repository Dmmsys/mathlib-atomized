/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Phragmen-Lindelöf principle

In this file we prove several versions of the Phragmen-Lindelöf principle, a version of the maximum
modulus principle for an unbounded domain.

## Main statements

* `PhragmenLindelof.horizontal_strip`: the Phragmen-Lindelöf principle in a horizontal strip
  `{z : ℂ | a < complex.im z < b}`;

* `PhragmenLindelof.eq_zero_on_horizontal_strip`, `PhragmenLindelof.eqOn_horizontal_strip`:
  extensionality lemmas based on the Phragmen-Lindelöf principle in a horizontal strip;

* `PhragmenLindelof.vertical_strip`: the Phragmen-Lindelöf principle in a vertical strip
  `{z : ℂ | a < complex.re z < b}`;

* `PhragmenLindelof.eq_zero_on_vertical_strip`, `PhragmenLindelof.eqOn_vertical_strip`:
  extensionality lemmas based on the Phragmen-Lindelöf principle in a vertical strip;

* `PhragmenLindelof.quadrant_I`, `PhragmenLindelof.quadrant_II`, `PhragmenLindelof.quadrant_III`,
  `PhragmenLindelof.quadrant_IV`: the Phragmen-Lindelöf principle in the coordinate quadrants;

* `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`,
  `PhragmenLindelof.right_half_plane_of_bounded_on_real`: two versions of the Phragmen-Lindelöf
  principle in the right half-plane;

* `PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`,
  `PhragmenLindelof.eqOn_right_half_plane_of_superexponential_decay`: extensionality lemmas based
  on the Phragmen-Lindelöf principle in the right half-plane.

In the case of the right half-plane, we prove a version of the Phragmen-Lindelöf principle that is
useful for Ilyashenko's proof of the individual finiteness theorem (a polynomial vector field on the
real plane has only finitely many limit cycles).
-/

public section

open Set Function Filter Asymptotics Metric Complex Bornology
open scoped Topology Filter Real

local notation "expR" => Real.exp

namespace PhragmenLindelof

/-!
### Auxiliary lemmas
-/


variable {E : Type*} [NormedAddCommGroup E]

/-- An auxiliary lemma that combines two double exponential estimates into a similar estimate
on the difference of the functions. -/
/-
**PhragmenLindelof.isBigO_sub_exp_exp** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelo
f`。
形式化陈述：isBigO_sub_exp_exp {a : Real} {f g : Complex -> E} {l : Filter Complex} {u
 : Complex -> Real} (hBf : exists c < a, exists B, f =O[l] fun z => expR (B * ex
pR (c * |u z|))) (hBg : exists c < a, exists B, g =O[l] fun z => expR (B * expR 
(c * |u z|))) : exists c < a, exists B, (f - g) =O[l] fun z => expR (B * expR (c
 * |u z|))
参数：hBf : exists c < a, exists B, f =O[l] fun z => expR (B * expR (c * |u z|))；hB
g : exists c < a, exists B, g =O[l] fun z => expR (B * expR (c * |u z|))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.trans_le`：∀ {α : Type u_1} {E : Type u_3} {G : Type u
_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddC
ommGroup F'] {f :…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
An auxiliary lemma that combines two double exponential estimates into a similar
 estimate
on the difference of the functions.
-/
theorem isBigO_sub_exp_exp {a : ℝ} {f g : ℂ → E} {l : Filter ℂ} {u : ℂ → ℝ}
    (hBf : ∃ c < a, ∃ B, f =O[l] fun z => expR (B * expR (c * |u z|)))
    (hBg : ∃ c < a, ∃ B, g =O[l] fun z => expR (B * expR (c * |u z|))) :
    ∃ c < a, ∃ B, (f - g) =O[l] fun z => expR (B * expR (c * |u z|)) := by
  have : ∀ {c₁ c₂ B₁ B₂}, c₁ ≤ c₂ → 0 ≤ B₂ → B₁ ≤ B₂ → ∀ z,
      ‖expR (B₁ * expR (c₁ * |u z|))‖ ≤ ‖expR (B₂ * expR (c₂ * |u z|))‖ := fun hc hB₀ hB z ↦ by
    simp only [Real.norm_eq_abs, Real.abs_exp]; gcongr
  rcases hBf with ⟨cf, hcf, Bf, hOf⟩; rcases hBg with ⟨cg, hcg, Bg, hOg⟩
  refine ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), ?_⟩
  refine (hOf.trans_le <| this ?_ ?_ ?_).sub (hOg.trans_le <| this ?_ ?_ ?_)
  exacts [le_max_left _ _, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    le_max_right _ _, le_max_left _ _, (le_max_right _ _).trans (le_max_right _ _)]

/-- An auxiliary lemma that combines two “exponential of a power” estimates into a similar estimate
on the difference of the functions. -/
/-
**PhragmenLindelof.isBigO_sub_exp_rpow** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindel
of`。
形式化陈述：isBigO_sub_exp_rpow {a : Real} {f g : Complex -> E} {l : Filter Complex} (
hBf : exists c < a, exists B, f =O[cobounded Complex ⊓ l] fun z => expR (B * ‖z‖
 ^ c)) (hBg : exists c < a, exists B, g =O[cobounded Complex ⊓ l] fun z => expR 
(B * ‖z‖ ^ c)) : exists c < a, exists B, (f - g) =O[cobounded Complex ⊓ l] fun z
 => expR (B * ‖z‖ ^ c)
参数：hBf : exists c < a, exists B, f =O[cobounded Complex ⊓ l] fun z => expR (B * 
‖z‖ ^ c)；hBg : exists c < a, exists B, g =O[cobounded Complex ⊓ l] fun z => expR
 (B * ‖z‖ ^ c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_norm_eventuallyLE`：∀ {α : Type u_1} {E : Type u_3}
 [inst : Norm E] {f : α → E} {l : Filter α} {g : α → ℝ},   (fun x => ‖f x‖) ≤ᶠ[l
] g → f =O[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `eventually_cobounded_le_norm`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] (a : ℝ), ∀ᶠ (x : E) in Bornology.cobounded E, a ≤ ‖x‖
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
An auxiliary lemma that combines two “exponential of a power” estimates into a s
imilar estimate
on the difference of the functions.
-/
theorem isBigO_sub_exp_rpow {a : ℝ} {f g : ℂ → E} {l : Filter ℂ}
    (hBf : ∃ c < a, ∃ B, f =O[cobounded ℂ ⊓ l] fun z => expR (B * ‖z‖ ^ c))
    (hBg : ∃ c < a, ∃ B, g =O[cobounded ℂ ⊓ l] fun z => expR (B * ‖z‖ ^ c)) :
    ∃ c < a, ∃ B, (f - g) =O[cobounded ℂ ⊓ l] fun z => expR (B * ‖z‖ ^ c) := by
  have : ∀ {c₁ c₂ B₁ B₂ : ℝ}, c₁ ≤ c₂ → 0 ≤ B₂ → B₁ ≤ B₂ →
      (fun z : ℂ => expR (B₁ * ‖z‖ ^ c₁)) =O[cobounded ℂ ⊓ l]
        fun z => expR (B₂ * ‖z‖ ^ c₂) := fun hc hB₀ hB ↦ .of_norm_eventuallyLE <| by
    filter_upwards [(eventually_cobounded_le_norm 1).filter_mono inf_le_left] with z hz
    simp only [Real.norm_eq_abs, Real.abs_exp]
    gcongr
  rcases hBf with ⟨cf, hcf, Bf, hOf⟩; rcases hBg with ⟨cg, hcg, Bg, hOg⟩
  refine ⟨max cf cg, max_lt hcf hcg, max 0 (max Bf Bg), ?_⟩
  refine (hOf.trans <| this ?_ ?_ ?_).sub (hOg.trans <| this ?_ ?_ ?_)
  exacts [le_max_left _ _, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    le_max_right _ _, le_max_left _ _, (le_max_right _ _).trans (le_max_right _ _)]

variable [NormedSpace ℂ E] {a b C : ℝ} {f g : ℂ → E} {z : ℂ}

/-!
### Phragmen-Lindelöf principle in a horizontal strip
-/

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of `U`.

Then `‖f z‖` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ im z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|re z|`.
-/
/-
**PhragmenLindelof.horizontal_strip** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`
。
形式化陈述：horizontal_strip (hfd : DiffContOnCl Complex f (im ⁻¹' Ioo a b)) (hB : exi
sts c < π / (b - a), exists B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Io
o a b)] fun z => expR (B * expR (c * |z.re|))) (hle_a : forall z : Complex, im z
 = a -> ‖f z‖ <= C) (hle_b : forall z, im z = b -> ‖f z‖ <= C) (hza : a <= im z)
 (hzb : im z <= b) : ‖f z‖ <= C
参数：hfd : DiffContOnCl Complex f (im ⁻¹' Ioo a b)；hB : exists c < π / (b - a), ex
ists B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z => expR (
B * expR (c * |z.re|))；hle_a : forall z : Complex, im z = a -> ‖f z‖ <= C；hle_b 
: forall z, im z = b -> ‖f z‖ <= C；hza : a <= im z；hzb : im z <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 224 条，此处仅展示前 30 条）

--- 原说明 ---
**Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for som
e `c < π / (b - a)`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of `U`.

Then `‖f z‖` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ im z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|re z|`.
-/
theorem horizontal_strip (hfd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (hle_a : ∀ z : ℂ, im z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, im z = b → ‖f z‖ ≤ C) (hza : a ≤ im z)
    (hzb : im z ≤ b) : ‖f z‖ ≤ C := by
  -- If `im z = a` or `im z = b`, then we apply `hle_a` or `hle_b`, otherwise `im z ∈ Ioo a b`.
  rw [le_iff_eq_or_lt] at hza hzb
  rcases hza with hza | hza; · exact hle_a _ hza.symm
  rcases hzb with hzb | hzb; · exact hle_b _ hzb
  wlog hC₀ : 0 < C generalizing C
  · refine le_of_forall_gt_imp_ge_of_dense fun C' hC' => this (fun w hw => ?_) (fun w hw => ?_) ?_
    · exact (hle_a _ hw).trans hC'.le
    · exact (hle_b _ hw).trans hC'.le
    · refine ((norm_nonneg (f (a * I))).trans (hle_a _ ?_)).trans_lt hC'
      rw [mul_I_im, ofReal_re]
  -- After a change of variables, we deal with the strip `a - b < im z < a + b` instead
  -- of `a < im z < b`
  obtain ⟨a, b, rfl, rfl⟩ : ∃ a' b', a = a' - b' ∧ b = a' + b' :=
    ⟨(a + b) / 2, (b - a) / 2, by ring, by ring⟩
  have hab : a - b < a + b := hza.trans hzb
  have hb : 0 < b := by simpa only [sub_eq_add_neg, add_lt_add_iff_left, neg_lt_self_iff] using hab
  rw [add_sub_sub_cancel, ← two_mul, div_mul_eq_div_div] at hB
  have hπb : 0 < π / 2 / b := div_pos Real.pi_div_two_pos hb
  -- Choose some `c B : ℝ` satisfying `hB`, then choose `max c 0 < d < π / 2 / b`.
  rcases hB with ⟨c, hc, B, hO⟩
  obtain ⟨d, ⟨hcd, hd₀⟩, hd⟩ : ∃ d, (c < d ∧ 0 < d) ∧ d < π / 2 / b := by
    simpa only [max_lt_iff] using exists_between (max_lt hc hπb)
  have hb' : d * b < π / 2 := (lt_div_iff₀ hb).1 hd
  set aff := (fun w => d * (w - a * I) : ℂ → ℂ)
  set g := fun (ε : ℝ) (w : ℂ) => exp (ε * (exp (aff w) + exp (-aff w)))
  /- Since `g ε z → 1` as `ε → 0⁻`, it suffices to prove that `‖g ε z • f z‖ ≤ C`
    for all negative `ε`. -/
  suffices ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), ‖g ε z • f z‖ ≤ C by
    refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) this
    apply ((continuous_ofReal.mul continuous_const).cexp.smul continuous_const).norm.tendsto'
    simp
  filter_upwards [self_mem_nhdsWithin] with ε ε₀; change ε < 0 at ε₀
  -- An upper estimate on `‖g ε w‖` that will be used in two branches of the proof.
  obtain ⟨δ, δ₀, hδ⟩ :
    ∃ δ : ℝ,
      δ < 0 ∧ ∀ ⦃w⦄, im w ∈ Icc (a - b) (a + b) → ‖g ε w‖ ≤ expR (δ * expR (d * |re w|)) := by
    refine
      ⟨ε * Real.cos (d * b),
        mul_neg_of_neg_of_pos ε₀
          (Real.cos_pos_of_mem_Ioo <| abs_lt.1 <| (abs_of_pos (mul_pos hd₀ hb)).symm ▸ hb'),
        fun w hw => ?_⟩
    replace hw : |im (aff w)| ≤ d * b := by
      rw [← Real.closedBall_eq_Icc, mem_closedBall, Real.dist_eq] at hw
      rw [im_ofReal_mul, sub_im, mul_I_im, ofReal_re, _root_.abs_mul, abs_of_pos hd₀]
      gcongr
    simpa only [aff, re_ofReal_mul, _root_.abs_mul, abs_of_pos hd₀, sub_re, mul_I_re, ofReal_im,
      zero_mul, neg_zero, sub_zero] using
      norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le ε₀.le hw hb'.le
  -- `abs (g ε w) ≤ 1` on the lines `w.im = a ± b` (actually, it holds everywhere in the strip)
  have hg₁ : ∀ w, im w = a - b ∨ im w = a + b → ‖g ε w‖ ≤ 1 := by
    refine fun w hw => (hδ <| hw.by_cases ?_ ?_).trans (Real.exp_le_one_iff.2 ?_)
    exacts [fun h => h.symm ▸ left_mem_Icc.2 hab.le, fun h => h.symm ▸ right_mem_Icc.2 hab.le,
      mul_nonpos_of_nonpos_of_nonneg δ₀.le (Real.exp_pos _).le]
  /- Our a priori estimate on `f` implies that `g ε w • f w → 0` as `|w.re| → ∞` along the strip. In
    particular, its norm is less than or equal to `C` for sufficiently large `|w.re|`. -/
  obtain ⟨R, hzR, hR⟩ :
    ∃ R : ℝ, |z.re| < R ∧ ∀ w, |re w| = R → im w ∈ Ioo (a - b) (a + b) → ‖g ε w • f w‖ ≤ C := by
    refine ((eventually_gt_atTop _).and ?_).exists
    rcases hO.exists_pos with ⟨A, hA₀, hA⟩
    simp only [isBigOWith_iff, eventually_inf_principal, eventually_comap, mem_Ioo,
      mem_preimage, (· ∘ ·), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hA
    suffices
        Tendsto (fun R => expR (δ * expR (d * R) + B * expR (c * R) + Real.log A)) atTop (𝓝 0) by
      filter_upwards [this.eventually (ge_mem_nhds hC₀), hA] with R hR Hle w hre him
      calc
        ‖g ε w • f w‖ ≤ expR (δ * expR (d * R) + B * expR (c * R) + Real.log A) := ?_
        _ ≤ C := hR
      rw [norm_smul, Real.exp_add, ← hre, Real.exp_add, Real.exp_log hA₀, mul_assoc, mul_comm _ A]
      gcongr
      exacts [hδ <| Ioo_subset_Icc_self him, Hle _ hre him]
    refine Real.tendsto_exp_atBot.comp ?_
    suffices H : Tendsto (fun R => δ + B * (expR ((d - c) * R))⁻¹) atTop (𝓝 (δ + B * 0)) by
      rw [mul_zero, add_zero] at H
      refine Tendsto.atBot_add ?_ tendsto_const_nhds
      simpa only [id, (· ∘ ·), add_mul, mul_assoc, ← div_eq_inv_mul, ← Real.exp_sub, ← sub_mul,
        sub_sub_cancel]
        using H.neg_mul_atTop δ₀ <| Real.tendsto_exp_atTop.comp <| tendsto_id.const_mul_atTop hd₀
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    exact tendsto_inv_atTop_zero.comp <| Real.tendsto_exp_atTop.comp <|
      tendsto_id.const_mul_atTop (sub_pos.2 hcd)
  have hR₀ : 0 < R := (_root_.abs_nonneg _).trans_lt hzR
  /- Finally, we apply the bounded version of the maximum modulus principle to the rectangle
    `(-R, R) × (a - b, a + b)`. The function is bounded by `C` on the horizontal sides by assumption
    (and because `‖g ε w‖ ≤ 1`) and on the vertical sides by the choice of `R`. -/
  have hgd : Differentiable ℂ (g ε) :=
    ((((differentiable_id.sub_const _).const_mul _).cexp.add
            ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul _).cexp
  replace hd : DiffContOnCl ℂ (fun w => g ε w • f w) (Ioo (-R) R ×ℂ Ioo (a - b) (a + b)) :=
    (hgd.diffContOnCl.smul hfd).mono inter_subset_right
  convert!
    norm_le_of_forall_mem_frontier_norm_le ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hd
      (fun w hw => _) _
  · rw [frontier_reProdIm, closure_Ioo (neg_lt_self hR₀).ne, frontier_Ioo hab, closure_Ioo hab.ne,
      frontier_Ioo (neg_lt_self hR₀)] at hw
    by_cases him : w.im = a - b ∨ w.im = a + b
    · rw [norm_smul, ← one_mul C]
      gcongr
      exacts [hg₁ _ him, him.by_cases (hle_a _) (hle_b _)]
    · replace hw : w ∈ {-R, R} ×ℂ Icc (a - b) (a + b) := hw.resolve_left fun h ↦ him h.2
      have hw' := eq_endpoints_or_mem_Ioo_of_mem_Icc hw.2; rw [← or_assoc] at hw'
      exact hR _ ((abs_eq hR₀.le).2 hw.1.symm) (hw'.resolve_left him)
  · rw [closure_reProdIm, closure_Ioo hab.ne, closure_Ioo (neg_lt_self hR₀).ne]
    exact ⟨abs_le.1 hzR.le, ⟨hza.le, hzb.le⟩⟩

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
/-
**PhragmenLindelof.eq_zero_on_horizontal_strip** 是 Mathlib 中的一个定理，位于命名空间 `Phragm
enLindelof`。
形式化陈述：eq_zero_on_horizontal_strip (hd : DiffContOnCl Complex f (im ⁻¹' Ioo a b))
 (hB : exists c < π / (b - a), exists B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 
(im ⁻¹' Ioo a b)] fun z => expR (B * expR (c * |z.re|))) (ha : forall z : Comple
x, z.im = a -> f z = 0) (hb : forall z : Complex, z.im = b -> f z = 0) : EqOn f 
0 (im ⁻¹' Icc a b)
参数：hd : DiffContOnCl Complex f (im ⁻¹' Ioo a b)；hB : exists c < π / (b - a), exi
sts B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z => expR (B
 * expR (c * |z.re|))；ha : forall z : Complex, z.im = a -> f z = 0；hb : forall z
 : Complex, z.im = b -> f z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `PhragmenLindelof.horizontal_strip`：horizontal_strip (hfd : DiffContOnCl 
Complex f (im ⁻¹' Ioo a b)) (hB : exists c < π / (b - a), exists B, f =O[comap (
_root_.abs ∘ re) atTop …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for som
e `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
theorem eq_zero_on_horizontal_strip (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (ha : ∀ z : ℂ, z.im = a → f z = 0) (hb : ∀ z : ℂ, z.im = b → f z = 0) :
    EqOn f 0 (im ⁻¹' Icc a b) := fun _z hz =>
  norm_le_zero_iff.1 <| horizontal_strip hd hB (fun z hz => (ha z hz).symm ▸ norm_zero.le)
    (fun z hz => (hb z hz).symm ▸ norm_zero.le) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
/-
**PhragmenLindelof.eqOn_horizontal_strip** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLind
elof`。
形式化陈述：eqOn_horizontal_strip {g : Complex -> E} (hdf : DiffContOnCl Complex f (im
 ⁻¹' Ioo a b)) (hBf : exists c < π / (b - a), exists B, f =O[comap (_root_.abs ∘
 re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z => expR (B * expR (c * |z.re|))) (hdg : D
iffContOnCl Complex g (im ⁻¹' Ioo a b)) (hBg : exists c < π / (b - a), exists B,
 g =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z => expR (B * exp
R (c * |z.re|))) (ha : forall z : Complex, z.im = a -> f z = g z) (hb : forall z
 : Complex, z.im = b -> f 
参数：hdf : DiffContOnCl Complex f (im ⁻¹' Ioo a b)；hBf : exists c < π / (b - a), e
xists B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)] fun z => expR 
(B * expR (c * |z.re|))；hdg : DiffContOnCl Complex g (im ⁻¹' Ioo a b)；hBg : exis
ts c < π / (b - a), exists B, g =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo
 a b)] fun z => expR (B * expR (c * |z.re|))；ha : forall z : Complex, z.im = a -
> f z = g z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PhragmenLindelof.eq_zero_on_horizontal_strip`：eq_zero_on_horizontal_stri
p (hd : DiffContOnCl Complex f (im ⁻¹' Ioo a b)) (hB : exists c < π / (b - a), e
xists B, f =O[comap (_root_.abs ∘ …
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_exp`：isBigO_sub_exp_exp {a : Real} {f g 
: Complex -> E} {l : Filter Complex} {u : Complex -> Real} (hBf : exists c < a, 
exists B, f =O[l] fun z =…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
**Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |re z|))` o
n `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
theorem eqOn_horizontal_strip {g : ℂ → E} (hdf : DiffContOnCl ℂ f (im ⁻¹' Ioo a b))
    (hBf : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (hdg : DiffContOnCl ℂ g (im ⁻¹' Ioo a b))
    (hBg : ∃ c < π / (b - a), ∃ B, g =O[comap (_root_.abs ∘ re) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.re|)))
    (ha : ∀ z : ℂ, z.im = a → f z = g z) (hb : ∀ z : ℂ, z.im = b → f z = g z) :
    EqOn f g (im ⁻¹' Icc a b) := fun _z hz =>
  sub_eq_zero.1 (eq_zero_on_horizontal_strip (hdf.sub hdg) (isBigO_sub_exp_exp hBf hBg)
    (fun w hw => sub_eq_zero.2 (ha w hw)) (fun w hw => sub_eq_zero.2 (hb w hw)) hz)

/-!
### Phragmen-Lindelöf principle in a vertical strip
-/

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some `c < π / (b - a)`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of `U`.

Then `‖f z‖` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ re z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|im z|`.
-/
/-
**PhragmenLindelof.vertical_strip** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：vertical_strip (hfd : DiffContOnCl Complex f (re ⁻¹' Ioo a b)) (hB : exist
s c < π / (b - a), exists B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo 
a b)] fun z => expR (B * expR (c * |z.im|))) (hle_a : forall z : Complex, re z =
 a -> ‖f z‖ <= C) (hle_b : forall z, re z = b -> ‖f z‖ <= C) (hza : a <= re z) (
hzb : re z <= b) : ‖f z‖ <= C
参数：hfd : DiffContOnCl Complex f (re ⁻¹' Ioo a b)；hB : exists c < π / (b - a), ex
ists B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z => expR (
B * expR (c * |z.im|))；hle_a : forall z : Complex, re z = a -> ‖f z‖ <= C；hle_b 
: forall z, re z = b -> ‖f z‖ <= C；hza : a <= re z；hzb : re z <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `PhragmenLindelof.horizontal_strip`：horizontal_strip (hfd : DiffContOnCl 
Complex f (im ⁻¹' Ioo a b)) (hB : exists c < π / (b - a), exists B, f =O[comap (
_root_.abs ∘ re) atTop …
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Differentiable.mul_const`：Differentiable.mul_const (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => a y * b
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1

--- 原说明 ---
**Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for som
e `c < π / (b - a)`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of `U`.

Then `‖f z‖` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ re z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|im z|`.
-/
theorem vertical_strip (hfd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (hle_a : ∀ z : ℂ, re z = a → ‖f z‖ ≤ C) (hle_b : ∀ z, re z = b → ‖f z‖ ≤ C) (hza : a ≤ re z)
    (hzb : re z ≤ b) : ‖f z‖ ≤ C := by
  suffices ‖f (z * I * -I)‖ ≤ C by simpa [mul_assoc] using this
  have H : MapsTo (· * -I) (im ⁻¹' Ioo a b) (re ⁻¹' Ioo a b) := fun z hz ↦ by simpa using hz
  refine horizontal_strip (f := fun z ↦ f (z * -I))
    (hfd.comp (differentiable_id.mul_const _).diffContOnCl H) ?_ (fun z hz => hle_a _ ?_)
    (fun z hz => hle_b _ ?_) ?_ ?_
  · rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    have : Tendsto (· * -I) (comap (|re ·|) atTop ⊓ 𝓟 (im ⁻¹' Ioo a b))
        (comap (|im ·|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)) := by
      refine (tendsto_comap_iff.2 ?_).inf H.tendsto
      simpa [Function.comp_def] using tendsto_comap
    simpa [Function.comp_def] using hO.comp_tendsto this
  all_goals simpa

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
/-
**PhragmenLindelof.eq_zero_on_vertical_strip** 是 Mathlib 中的一个定理，位于命名空间 `Phragmen
Lindelof`。
形式化陈述：eq_zero_on_vertical_strip (hd : DiffContOnCl Complex f (re ⁻¹' Ioo a b)) (
hB : exists c < π / (b - a), exists B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (r
e ⁻¹' Ioo a b)] fun z => expR (B * expR (c * |z.im|))) (ha : forall z : Complex,
 re z = a -> f z = 0) (hb : forall z : Complex, re z = b -> f z = 0) : EqOn f 0 
(re ⁻¹' Icc a b)
参数：hd : DiffContOnCl Complex f (re ⁻¹' Ioo a b)；hB : exists c < π / (b - a), exi
sts B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z => expR (B
 * expR (c * |z.im|))；ha : forall z : Complex, re z = a -> f z = 0；hb : forall z
 : Complex, re z = b -> f z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `PhragmenLindelof.vertical_strip`：vertical_strip (hfd : DiffContOnCl Comp
lex f (re ⁻¹' Ioo a b)) (hB : exists c < π / (b - a), exists B, f =O[comap (_roo
t_.abs ∘ im) atTop ⊓ …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for som
e `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
theorem eq_zero_on_vertical_strip (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hB : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (ha : ∀ z : ℂ, re z = a → f z = 0) (hb : ∀ z : ℂ, re z = b → f z = 0) :
    EqOn f 0 (re ⁻¹' Icc a b) := fun _z hz =>
  norm_le_zero_iff.1 <| vertical_strip hd hB (fun z hz => (ha z hz).symm ▸ norm_zero.le)
    (fun z hz => (hb z hz).symm ▸ norm_zero.le) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |im z|))` on `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
/-
**PhragmenLindelof.eqOn_vertical_strip** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindel
of`。
形式化陈述：eqOn_vertical_strip {g : Complex -> E} (hdf : DiffContOnCl Complex f (re ⁻
¹' Ioo a b)) (hBf : exists c < π / (b - a), exists B, f =O[comap (_root_.abs ∘ i
m) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z => expR (B * expR (c * |z.im|))) (hdg : Dif
fContOnCl Complex g (re ⁻¹' Ioo a b)) (hBg : exists c < π / (b - a), exists B, g
 =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z => expR (B * expR 
(c * |z.im|))) (ha : forall z : Complex, re z = a -> f z = g z) (hb : forall z :
 Complex, re z = b -> f z 
参数：hdf : DiffContOnCl Complex f (re ⁻¹' Ioo a b)；hBf : exists c < π / (b - a), e
xists B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)] fun z => expR 
(B * expR (c * |z.im|))；hdg : DiffContOnCl Complex g (re ⁻¹' Ioo a b)；hBg : exis
ts c < π / (b - a), exists B, g =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo
 a b)] fun z => expR (B * expR (c * |z.im|))；ha : forall z : Complex, re z = a -
> f z = g z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PhragmenLindelof.eq_zero_on_vertical_strip`：eq_zero_on_vertical_strip (h
d : DiffContOnCl Complex f (re ⁻¹' Ioo a b)) (hB : exists c < π / (b - a), exist
s B, f =O[comap (_root_.abs ∘ im…
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_exp`：isBigO_sub_exp_exp {a : Real} {f g 
: Complex -> E} {l : Filter Complex} {u : Complex -> Real} (hBf : exists c < a, 
exists B, f =O[l] fun z =…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
**Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`.
Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable on `U` and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * exp(c * |im z|))` o
n `U` for some
  `c < π / (b - a)`;
* `f z = g z` on the boundary of `U`.

Then `f` is equal to `g` on the closed strip `{z : ℂ | a ≤ re z ≤ b}`.
-/
theorem eqOn_vertical_strip {g : ℂ → E} (hdf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hBf : ∃ c < π / (b - a), ∃ B, f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (hdg : DiffContOnCl ℂ g (re ⁻¹' Ioo a b))
    (hBg : ∃ c < π / (b - a), ∃ B, g =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z ↦ expR (B * expR (c * |z.im|)))
    (ha : ∀ z : ℂ, re z = a → f z = g z) (hb : ∀ z : ℂ, re z = b → f z = g z) :
    EqOn f g (re ⁻¹' Icc a b) := fun _z hz =>
  sub_eq_zero.1 (eq_zero_on_vertical_strip (hdf.sub hdg) (isBigO_sub_exp_exp hBf hBg)
    (fun w hw => sub_eq_zero.2 (ha w hw)) (fun w hw => sub_eq_zero.2 (hb w hw)) hz)

/-!
### Phragmen-Lindelöf principle in coordinate quadrants
-/

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the first quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed first quadrant. -/
nonrec theorem quadrant_I (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ‖f (x * I)‖ ≤ C) (hz_re : 0 ≤ z.re)
    (hz_im : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  -- The case `z = 0` is trivial.
  rcases eq_or_ne z 0 with (rfl | hzne)
  · exact hre 0 le_rfl
  -- Otherwise, `z = e ^ ζ` for some `ζ : ℂ`, `0 < Im ζ < π / 2`.
  obtain ⟨ζ, hζ, rfl⟩ : ∃ ζ : ℂ, ζ.im ∈ Icc 0 (π / 2) ∧ exp ζ = z := by
    refine ⟨log z, ?_, exp_log hzne⟩
    rw [log_im]
    exact ⟨arg_nonneg_iff.2 hz_im, arg_le_pi_div_two_iff.2 (Or.inl hz_re)⟩
  -- We are going to apply `PhragmenLindelof.horizontal_strip` to `f ∘ Complex.exp` and `ζ`.
  change ‖(f ∘ exp) ζ‖ ≤ C
  have H : MapsTo exp (im ⁻¹' Ioo 0 (π / 2)) (Ioi 0 ×ℂ Ioi 0) := fun z hz ↦ by
    rw [mem_reProdIm, exp_re, exp_im, mem_Ioi, mem_Ioi]
    have : 0 < Real.cos z.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1, hz.2], hz.2⟩
    have : 0 < Real.sin z.im :=
      Real.sin_pos_of_mem_Ioo ⟨hz.1, hz.2.trans (half_lt_self Real.pi_pos)⟩
    constructor <;> positivity
  refine horizontal_strip (hd.comp differentiable_exp.diffContOnCl H) ?_ ?_ ?_ hζ.1 hζ.2
  · -- The estimate `hB` on `f` implies the required estimate on
    -- `f ∘ exp` with the same `c` and `B' = max B 0`.
    rw [sub_zero, div_div_cancel₀ Real.pi_pos.ne']
    rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, max B 0, ?_⟩
    rw [← comap_comap, comap_abs_atTop, comap_sup, inf_sup_right]
    -- We prove separately the estimates as `ζ.re → ∞` and as `ζ.re → -∞`
    refine IsBigO.sup ?_ <| (hO.comp_tendsto <| tendsto_exp_comap_re_atTop.inf H.tendsto).trans <|
      .of_norm_eventuallyLE ?_
    · -- For the estimate as `ζ.re → -∞`, note that `f` is continuous within the first quadrant at
      -- zero, hence `f (exp ζ)` has a limit as `ζ.re → -∞`, `0 < ζ.im < π / 2`.
      have hc : ContinuousWithinAt f (Ioi 0 ×ℂ Ioi 0) 0 := by
        refine (hd.continuousOn _ ?_).mono subset_closure
        simp [closure_reProdIm, mem_reProdIm]
      refine ((hc.tendsto.comp <| tendsto_exp_comap_re_atBot.inf H.tendsto).isBigO_one ℝ).trans
        (isBigO_of_le _ fun w => ?_)
      rw [norm_one, Real.norm_of_nonneg (Real.exp_pos _).le, Real.one_le_exp_iff]
      positivity
    · -- For the estimate as `ζ.re → ∞`, we reuse the upper estimate on `f`
      simp only [EventuallyLE, eventually_inf_principal, eventually_comap, comp_apply,
        Real.norm_of_nonneg (Real.exp_pos _).le, norm_exp, ← Real.exp_mul, Real.exp_le_exp]
      filter_upwards [eventually_ge_atTop 0] with x hx z hz _
      rw [hz, abs_of_nonneg hx, mul_comm _ c]
      gcongr; apply le_max_left
  · -- If `ζ.im = 0`, then `Complex.exp ζ` is a positive real number
    intro ζ hζ; lift ζ to ℝ using hζ
    rw [comp_apply, ← ofReal_exp]
    exact hre _ (Real.exp_pos _).le
  · -- If `ζ.im = π / 2`, then `Complex.exp ζ` is a purely imaginary number with positive `im`
    intro ζ hζ
    rw [← re_add_im ζ, hζ, comp_apply, exp_add_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two, ofReal_zero, ofReal_one, one_mul, zero_add, ←
      ofReal_exp]
    exact him _ (Real.exp_pos _).le

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the first quadrant.

Then `f` is equal to zero on the closed first quadrant. -/
/-
**PhragmenLindelof.eq_zero_on_quadrant_I** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLind
elof`。
形式化陈述：eq_zero_on_quadrant_I (hd : DiffContOnCl Complex f (Ioi 0 ×Complex Ioi 0))
 (hB : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Compl
ex Ioi 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, 0 <= x -> f x = 
0) (him : forall x : Real, 0 <= x -> f (x * I) = 0) : EqOn f 0 {z | 0 <= z.re ∧ 
0 <= z.im}
参数：hd : DiffContOnCl Complex f (Ioi 0 ×Complex Ioi 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Ioi 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, 0 <= x -> f x = 0；him : forall x : Real, 0 <= 
x -> f (x * I) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `PhragmenLindelof.quadrant_I`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℂ E] {C : ℝ} {f : ℂ → E} {z : ℂ},   DiffContOnCl ℂ f (
Set.Ioi 0 ×ℂ Set.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a func
tion such that

* `f` is differentiable in the open first quadrant and is continuous on its clos
ure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first quad
rant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the first quadrant.

Then `f` is equal to zero on the closed first quadrant.
-/
theorem eq_zero_on_quadrant_I (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = 0) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = 0) :
    EqOn f 0 {z | 0 ≤ z.re ∧ 0 ≤ z.im} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_I hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open first quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open first
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the first quadrant.

Then `f` is equal to `g` on the closed first quadrant. -/
/-
**PhragmenLindelof.eqOn_quadrant_I** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：eqOn_quadrant_I (hdf : DiffContOnCl Complex f (Ioi 0 ×Complex Ioi 0)) (hBf
 : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex I
oi 0)] fun z => expR (B * ‖z‖ ^ c)) (hdg : DiffContOnCl Complex g (Ioi 0 ×Comple
x Ioi 0)) (hBg : exists c < (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (Io
i 0 ×Complex Ioi 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, 0 <= x
 -> f x = g x) (him : forall x : Real, 0 <= x -> f (x * I) = g (x * I)) : EqOn f
 g {z | 0 <= z.re ∧ 0 <= z
参数：hdf : DiffContOnCl Complex f (Ioi 0 ×Complex Ioi 0)；hBf : exists c < (2 : Rea
l), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Ioi 0)] fun z => expR (
B * ‖z‖ ^ c)；hdg : DiffContOnCl Complex g (Ioi 0 ×Complex Ioi 0)；hBg : exists c 
< (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Ioi 0)] fun z
 => expR (B * ‖z‖ ^ c)；hre : forall x : Real, 0 <= x -> f x = g x；him : forall x
 : Real, 0 <= x -> f (x * I) = g (x * I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PhragmenLindelof.eq_zero_on_quadrant_I`：eq_zero_on_quadrant_I (hd : Diff
ContOnCl Complex f (Ioi 0 ×Complex Ioi 0)) (hB : exists c < (2 : Real), exists B
, f =O[cobounded Complex ⊓ 𝓟…
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_rpow`：isBigO_sub_exp_rpow {a : Real} {f 
g : Complex -> E} {l : Filter Complex} (hBf : exists c < a, exists B, f =O[cobou
nded Complex ⊓ l] fun z =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
**Phragmen-Lindelöf principle** in the first quadrant. Let `f g : ℂ → E` be func
tions such that

* `f` and `g` are differentiable in the open first quadrant and are continuous o
n its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the op
en first
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the first quadrant.

Then `f` is equal to `g` on the closed first quadrant.
-/
theorem eqOn_quadrant_I (hdf : DiffContOnCl ℂ f (Ioi 0 ×ℂ Ioi 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Ioi 0 ×ℂ Ioi 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = g x) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = g (x * I)) :
    EqOn f g {z | 0 ≤ z.re ∧ 0 ≤ z.im} := fun _z hz =>
  sub_eq_zero.1 <|
    eq_zero_on_quadrant_I (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
      (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the second quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed second quadrant. -/
/-
**PhragmenLindelof.quadrant_II** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：quadrant_II (hd : DiffContOnCl Complex f (Iio 0 ×Complex Ioi 0)) (hB : exi
sts c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Ioi 0)]
 fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, x <= 0 -> ‖f x‖ <= C) (him
 : forall x : Real, 0 <= x -> ‖f (x * I)‖ <= C) (hz_re : z.re <= 0) (hz_im : 0 <
= z.im) : ‖f z‖ <= C
参数：hd : DiffContOnCl Complex f (Iio 0 ×Complex Ioi 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Ioi 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, x <= 0 -> ‖f x‖ <= C；him : forall x : Real, 0 
<= x -> ‖f (x * I)‖ <= C；hz_re : z.re <= 0；hz_im : 0 <= z.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_I_re`：mul_I_re (z : Complex) : (z * I).re = -z.im
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Complex.mul_I_im`：mul_I_im (z : Complex) : (z * I).im = z.re
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `PhragmenLindelof.quadrant_I`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℂ E] {C : ℝ} {f : ℂ → E} {z : ℂ},   DiffContOnCl ℂ f (
Set.Ioi 0 ×ℂ Set.…
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Differentiable.mul_const`：Differentiable.mul_const (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => a y * b
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Filter.tendsto_mul_right_cobounded`：tendsto_mul_right_cobounded {a : α} 
(ha : a != 0) : Tendsto (· * a) (cobounded α) (cobounded α)
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
**Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a fun
ction such that

* `f` is differentiable in the open second quadrant and is continuous on its clo
sure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second qua
drant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the second 
quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed second qua
drant.
-/
theorem quadrant_II (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ‖f (x * I)‖ ≤ C) (hz_re : z.re ≤ 0)
    (hz_im : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', z' * I = z := ⟨z / I, div_mul_cancel₀ _ I_ne_zero⟩
  simp only [mul_I_re, mul_I_im, neg_nonpos] at hz_re hz_im
  change ‖(f ∘ (· * I)) z‖ ≤ C
  have H : MapsTo (· * I) (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Ioi 0) := fun w hw ↦ by
    simpa only [mem_reProdIm, mul_I_re, mul_I_im, neg_lt_zero, mem_Iio] using! hw.symm
  rcases hB with ⟨c, hc, B, hO⟩
  refine quadrant_I (hd.comp (differentiable_id.mul_const _).diffContOnCl H) ⟨c, hc, B, ?_⟩ him
    (fun x hx => ?_) hz_im hz_re
  · simpa only [Function.comp_def, norm_mul, norm_I, mul_one]
      using hO.comp_tendsto ((tendsto_mul_right_cobounded I_ne_zero).inf H.tendsto)
  · rw [comp_apply, mul_assoc, I_mul_I, mul_neg_one, ← ofReal_neg]
    exact hre _ (neg_nonpos.2 hx)

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the second quadrant.

Then `f` is equal to zero on the closed second quadrant. -/
/-
**PhragmenLindelof.eq_zero_on_quadrant_II** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLin
delof`。
形式化陈述：eq_zero_on_quadrant_II (hd : DiffContOnCl Complex f (Iio 0 ×Complex Ioi 0)
) (hB : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Comp
lex Ioi 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, x <= 0 -> f x =
 0) (him : forall x : Real, 0 <= x -> f (x * I) = 0) : EqOn f 0 {z | z.re <= 0 ∧
 0 <= z.im}
参数：hd : DiffContOnCl Complex f (Iio 0 ×Complex Ioi 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Ioi 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, x <= 0 -> f x = 0；him : forall x : Real, 0 <= 
x -> f (x * I) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `PhragmenLindelof.quadrant_II`：quadrant_II (hd : DiffContOnCl Complex f (
Iio 0 ×Complex Ioi 0)) (hB : exists c < (2 : Real), exists B, f =O[cobounded Com
plex ⊓ 𝓟 (Iio 0 ×C…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a fun
ction such that

* `f` is differentiable in the open second quadrant and is continuous on its clo
sure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second qua
drant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the second quadrant.

Then `f` is equal to zero on the closed second quadrant.
-/
theorem eq_zero_on_quadrant_II (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = 0) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = 0) :
    EqOn f 0 {z | z.re ≤ 0 ∧ 0 ≤ z.im} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_II hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open second quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open second
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the second quadrant.

Then `f` is equal to `g` on the closed second quadrant. -/
/-
**PhragmenLindelof.eqOn_quadrant_II** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`
。
形式化陈述：eqOn_quadrant_II (hdf : DiffContOnCl Complex f (Iio 0 ×Complex Ioi 0)) (hB
f : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex 
Ioi 0)] fun z => expR (B * ‖z‖ ^ c)) (hdg : DiffContOnCl Complex g (Iio 0 ×Compl
ex Ioi 0)) (hBg : exists c < (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (I
io 0 ×Complex Ioi 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, x <= 
0 -> f x = g x) (him : forall x : Real, 0 <= x -> f (x * I) = g (x * I)) : EqOn 
f g {z | z.re <= 0 ∧ 0 <= 
参数：hdf : DiffContOnCl Complex f (Iio 0 ×Complex Ioi 0)；hBf : exists c < (2 : Rea
l), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Ioi 0)] fun z => expR (
B * ‖z‖ ^ c)；hdg : DiffContOnCl Complex g (Iio 0 ×Complex Ioi 0)；hBg : exists c 
< (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Ioi 0)] fun z
 => expR (B * ‖z‖ ^ c)；hre : forall x : Real, x <= 0 -> f x = g x；him : forall x
 : Real, 0 <= x -> f (x * I) = g (x * I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PhragmenLindelof.eq_zero_on_quadrant_II`：eq_zero_on_quadrant_II (hd : Di
ffContOnCl Complex f (Iio 0 ×Complex Ioi 0)) (hB : exists c < (2 : Real), exists
 B, f =O[cobounded Complex ⊓ …
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_rpow`：isBigO_sub_exp_rpow {a : Real} {f 
g : Complex -> E} {l : Filter Complex} (hBf : exists c < a, exists B, f =O[cobou
nded Complex ⊓ l] fun z =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
**Phragmen-Lindelöf principle** in the second quadrant. Let `f g : ℂ → E` be fun
ctions such that

* `f` and `g` are differentiable in the open second quadrant and are continuous 
on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the op
en second
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the second quadrant.

Then `f` is equal to `g` on the closed second quadrant.
-/
theorem eqOn_quadrant_II (hdf : DiffContOnCl ℂ f (Iio 0 ×ℂ Ioi 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Iio 0 ×ℂ Ioi 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = g x) (him : ∀ x : ℝ, 0 ≤ x → f (x * I) = g (x * I)) :
    EqOn f g {z | z.re ≤ 0 ∧ 0 ≤ z.im} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_II (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp (B * ‖z‖ ^ c)` on the open third quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the third quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed third quadrant. -/
/-
**PhragmenLindelof.quadrant_III** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：quadrant_III (hd : DiffContOnCl Complex f (Iio 0 ×Complex Iio 0)) (hB : ex
ists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Iio 0)
] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, x <= 0 -> ‖f x‖ <= C) (hi
m : forall x : Real, x <= 0 -> ‖f (x * I)‖ <= C) (hz_re : z.re <= 0) (hz_im : z.
im <= 0) : ‖f z‖ <= C
参数：hd : DiffContOnCl Complex f (Iio 0 ×Complex Iio 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Iio 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, x <= 0 -> ‖f x‖ <= C；him : forall x : Real, x 
<= 0 -> ‖f (x * I)‖ <= C；hz_re : z.re <= 0；hz_im : z.im <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PhragmenLindelof.quadrant_I`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℂ E] {C : ℝ} {f : ℂ → E} {z : ℂ},   DiffContOnCl ℂ f (
Set.Ioi 0 ×ℂ Set.…
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `differentiable_neg`：differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 -
> 𝕜)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Filter.tendsto_neg_cobounded`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto Neg.neg (Bornology.cobounded E) (Bornology.cobounded E)
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)

--- 原说明 ---
**Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a func
tion such that

* `f` is differentiable in the open third quadrant and is continuous on its clos
ure;
* `‖f z‖` is bounded from above by `A * exp (B * ‖z‖ ^ c)` on the open third qua
drant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the third q
uadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed third quad
rant.
-/
theorem quadrant_III (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ‖f (x * I)‖ ≤ C) (hz_re : z.re ≤ 0)
    (hz_im : z.im ≤ 0) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z := ⟨-z, neg_neg z⟩
  simp only [neg_re, neg_im, neg_nonpos] at hz_re hz_im
  change ‖(f ∘ Neg.neg) z‖ ≤ C
  have H : MapsTo Neg.neg (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Iio 0) := by
    intro w hw
    simpa only [mem_reProdIm, neg_re, neg_im, neg_lt_zero, mem_Iio] using! hw
  refine
    quadrant_I (hd.comp differentiable_neg.diffContOnCl H) ?_ (fun x hx => ?_) (fun x hx => ?_)
      hz_re hz_im
  · rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    simpa only [Function.comp_def, norm_neg]
      using hO.comp_tendsto (Filter.tendsto_neg_cobounded.inf H.tendsto)
  · rw [comp_apply, ← ofReal_neg]
    exact hre (-x) (neg_nonpos.2 hx)
  · rw [comp_apply, ← neg_mul, ← ofReal_neg]
    exact him (-x) (neg_nonpos.2 hx)

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open third quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the third quadrant.

Then `f` is equal to zero on the closed third quadrant. -/
/-
**PhragmenLindelof.eq_zero_on_quadrant_III** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLi
ndelof`。
形式化陈述：eq_zero_on_quadrant_III (hd : DiffContOnCl Complex f (Iio 0 ×Complex Iio 0
)) (hB : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Com
plex Iio 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, x <= 0 -> f x 
= 0) (him : forall x : Real, x <= 0 -> f (x * I) = 0) : EqOn f 0 {z | z.re <= 0 
∧ z.im <= 0}
参数：hd : DiffContOnCl Complex f (Iio 0 ×Complex Iio 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Iio 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, x <= 0 -> f x = 0；him : forall x : Real, x <= 
0 -> f (x * I) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `PhragmenLindelof.quadrant_III`：quadrant_III (hd : DiffContOnCl Complex f
 (Iio 0 ×Complex Iio 0)) (hB : exists c < (2 : Real), exists B, f =O[cobounded C
omplex ⊓ 𝓟 (Iio 0 ×…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a func
tion such that

* `f` is differentiable in the open third quadrant and is continuous on its clos
ure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open third quad
rant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the third quadrant.

Then `f` is equal to zero on the closed third quadrant.
-/
theorem eq_zero_on_quadrant_III (hd : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = 0) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = 0) :
    EqOn f 0 {z | z.re ≤ 0 ∧ z.im ≤ 0} := fun _z hz =>
  norm_le_zero_iff.1 <| quadrant_III hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
    (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open third quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open third
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the third quadrant.

Then `f` is equal to `g` on the closed third quadrant. -/
/-
**PhragmenLindelof.eqOn_quadrant_III** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof
`。
形式化陈述：eqOn_quadrant_III (hdf : DiffContOnCl Complex f (Iio 0 ×Complex Iio 0)) (h
Bf : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex
 Iio 0)] fun z => expR (B * ‖z‖ ^ c)) (hdg : DiffContOnCl Complex g (Iio 0 ×Comp
lex Iio 0)) (hBg : exists c < (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (
Iio 0 ×Complex Iio 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, x <=
 0 -> f x = g x) (him : forall x : Real, x <= 0 -> f (x * I) = g (x * I)) : EqOn
 f g {z | z.re <= 0 ∧ z.im
参数：hdf : DiffContOnCl Complex f (Iio 0 ×Complex Iio 0)；hBf : exists c < (2 : Rea
l), exists B, f =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Iio 0)] fun z => expR (
B * ‖z‖ ^ c)；hdg : DiffContOnCl Complex g (Iio 0 ×Complex Iio 0)；hBg : exists c 
< (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (Iio 0 ×Complex Iio 0)] fun z
 => expR (B * ‖z‖ ^ c)；hre : forall x : Real, x <= 0 -> f x = g x；him : forall x
 : Real, x <= 0 -> f (x * I) = g (x * I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PhragmenLindelof.eq_zero_on_quadrant_III`：eq_zero_on_quadrant_III (hd : 
DiffContOnCl Complex f (Iio 0 ×Complex Iio 0)) (hB : exists c < (2 : Real), exis
ts B, f =O[cobounded Complex ⊓…
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_rpow`：isBigO_sub_exp_rpow {a : Real} {f 
g : Complex -> E} {l : Filter Complex} (hBf : exists c < a, exists B, f =O[cobou
nded Complex ⊓ l] fun z =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
**Phragmen-Lindelöf principle** in the third quadrant. Let `f g : ℂ → E` be func
tions such that

* `f` and `g` are differentiable in the open third quadrant and are continuous o
n its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the op
en third
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the third quadrant.

Then `f` is equal to `g` on the closed third quadrant.
-/
theorem eqOn_quadrant_III (hdf : DiffContOnCl ℂ f (Iio 0 ×ℂ Iio 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Iio 0 ×ℂ Iio 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, x ≤ 0 → f x = g x) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = g (x * I)) :
    EqOn f g {z | z.re ≤ 0 ∧ z.im ≤ 0} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_III (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth quadrant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the fourth quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed fourth quadrant. -/
/-
**PhragmenLindelof.quadrant_IV** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：quadrant_IV (hd : DiffContOnCl Complex f (Ioi 0 ×Complex Iio 0)) (hB : exi
sts c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Iio 0)]
 fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, 0 <= x -> ‖f x‖ <= C) (him
 : forall x : Real, x <= 0 -> ‖f (x * I)‖ <= C) (hz_re : 0 <= z.re) (hz_im : z.i
m <= 0) : ‖f z‖ <= C
参数：hd : DiffContOnCl Complex f (Ioi 0 ×Complex Iio 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Iio 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, 0 <= x -> ‖f x‖ <= C；him : forall x : Real, x 
<= 0 -> ‖f (x * I)‖ <= C；hz_re : 0 <= z.re；hz_im : z.im <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PhragmenLindelof.quadrant_II`：quadrant_II (hd : DiffContOnCl Complex f (
Iio 0 ×Complex Ioi 0)) (hB : exists c < (2 : Real), exists B, f =O[cobounded Com
plex ⊓ 𝓟 (Iio 0 ×C…
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `differentiable_neg`：differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 -
> 𝕜)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Filter.tendsto_neg_cobounded`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto Neg.neg (Bornology.cobounded E) (Bornology.cobounded E)
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a

--- 原说明 ---
**Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a fun
ction such that

* `f` is differentiable in the open fourth quadrant and is continuous on its clo
sure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth qua
drant
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the boundary of the fourth 
quadrant.

Then `‖f z‖` is bounded from above by the same constant on the closed fourth qua
drant.
-/
theorem quadrant_IV (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ‖f (x * I)‖ ≤ C) (hz_re : 0 ≤ z.re)
    (hz_im : z.im ≤ 0) : ‖f z‖ ≤ C := by
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z := ⟨-z, neg_neg z⟩
  simp only [neg_re, neg_im, neg_nonpos, neg_nonneg] at hz_re hz_im
  change ‖(f ∘ Neg.neg) z‖ ≤ C
  have H : MapsTo Neg.neg (Iio 0 ×ℂ Ioi 0) (Ioi 0 ×ℂ Iio 0) := fun w hw ↦ by
    simpa only [mem_reProdIm, neg_re, neg_im, neg_lt_zero, neg_pos, mem_Ioi, mem_Iio] using hw
  refine quadrant_II
    (hd.comp differentiable_neg.diffContOnCl H) ?_ (fun x hx => ?_) (fun x hx => ?_) hz_re hz_im
  · rcases hB with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, ?_⟩
    simpa only [Function.comp_def, norm_neg]
      using hO.comp_tendsto (Filter.tendsto_neg_cobounded.inf H.tendsto)
  · rw [comp_apply, ← ofReal_neg]
    exact hre (-x) (neg_nonneg.2 hx)
  · rw [comp_apply, ← neg_mul, ← ofReal_neg]
    exact him (-x) (neg_nonpos.2 hx)

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth quadrant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the fourth quadrant.

Then `f` is equal to zero on the closed fourth quadrant. -/
/-
**PhragmenLindelof.eq_zero_on_quadrant_IV** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLin
delof`。
形式化陈述：eq_zero_on_quadrant_IV (hd : DiffContOnCl Complex f (Ioi 0 ×Complex Iio 0)
) (hB : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Comp
lex Iio 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, 0 <= x -> f x =
 0) (him : forall x : Real, x <= 0 -> f (x * I) = 0) : EqOn f 0 {z | 0 <= z.re ∧
 z.im <= 0}
参数：hd : DiffContOnCl Complex f (Ioi 0 ×Complex Iio 0)；hB : exists c < (2 : Real)
, exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Iio 0)] fun z => expR (B 
* ‖z‖ ^ c)；hre : forall x : Real, 0 <= x -> f x = 0；him : forall x : Real, x <= 
0 -> f (x * I) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `PhragmenLindelof.quadrant_IV`：quadrant_IV (hd : DiffContOnCl Complex f (
Ioi 0 ×Complex Iio 0)) (hB : exists c < (2 : Real), exists B, f =O[cobounded Com
plex ⊓ 𝓟 (Ioi 0 ×C…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a fun
ction such that

* `f` is differentiable in the open fourth quadrant and is continuous on its clo
sure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth qua
drant
  for some `A`, `B`, and `c < 2`;
* `f` is equal to zero on the boundary of the fourth quadrant.

Then `f` is equal to zero on the closed fourth quadrant.
-/
theorem eq_zero_on_quadrant_IV (hd : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hB : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = 0) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = 0) :
    EqOn f 0 {z | 0 ≤ z.re ∧ z.im ≤ 0} := fun _z hz =>
  norm_le_zero_iff.1 <|
    quadrant_IV hd hB (fun x hx => norm_le_zero_iff.2 <| hre x hx)
      (fun x hx => norm_le_zero_iff.2 <| him x hx) hz.1 hz.2

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f g : ℂ → E` be functions such that

* `f` and `g` are differentiable in the open fourth quadrant and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open fourth
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the fourth quadrant.

Then `f` is equal to `g` on the closed fourth quadrant. -/
/-
**PhragmenLindelof.eqOn_quadrant_IV** 是 Mathlib 中的一个定理，位于命名空间 `PhragmenLindelof`
。
形式化陈述：eqOn_quadrant_IV (hdf : DiffContOnCl Complex f (Ioi 0 ×Complex Iio 0)) (hB
f : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex 
Iio 0)] fun z => expR (B * ‖z‖ ^ c)) (hdg : DiffContOnCl Complex g (Ioi 0 ×Compl
ex Iio 0)) (hBg : exists c < (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (I
oi 0 ×Complex Iio 0)] fun z => expR (B * ‖z‖ ^ c)) (hre : forall x : Real, 0 <= 
x -> f x = g x) (him : forall x : Real, x <= 0 -> f (x * I) = g (x * I)) : EqOn 
f g {z | 0 <= z.re ∧ z.im 
参数：hdf : DiffContOnCl Complex f (Ioi 0 ×Complex Iio 0)；hBf : exists c < (2 : Rea
l), exists B, f =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Iio 0)] fun z => expR (
B * ‖z‖ ^ c)；hdg : DiffContOnCl Complex g (Ioi 0 ×Complex Iio 0)；hBg : exists c 
< (2 : Real), exists B, g =O[cobounded Complex ⊓ 𝓟 (Ioi 0 ×Complex Iio 0)] fun z
 => expR (B * ‖z‖ ^ c)；hre : forall x : Real, 0 <= x -> f x = g x；him : forall x
 : Real, x <= 0 -> f (x * I) = g (x * I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `PhragmenLindelof.eq_zero_on_quadrant_IV`：eq_zero_on_quadrant_IV (hd : Di
ffContOnCl Complex f (Ioi 0 ×Complex Iio 0)) (hB : exists c < (2 : Real), exists
 B, f =O[cobounded Complex ⊓ …
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_rpow`：isBigO_sub_exp_rpow {a : Real} {f 
g : Complex -> E} {l : Filter Complex} (hBf : exists c < a, exists B, f =O[cobou
nded Complex ⊓ l] fun z =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
**Phragmen-Lindelöf principle** in the fourth quadrant. Let `f g : ℂ → E` be fun
ctions such that

* `f` and `g` are differentiable in the open fourth quadrant and are continuous 
on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the op
en fourth
  quadrant for some `A`, `B`, and `c < 2`;
* `f` is equal to `g` on the boundary of the fourth quadrant.

Then `f` is equal to `g` on the closed fourth quadrant.
-/
theorem eqOn_quadrant_IV (hdf : DiffContOnCl ℂ f (Ioi 0 ×ℂ Iio 0))
    (hBf : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hdg : DiffContOnCl ℂ g (Ioi 0 ×ℂ Iio 0))
    (hBg : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)] fun z => expR (B * ‖z‖ ^ c))
    (hre : ∀ x : ℝ, 0 ≤ x → f x = g x) (him : ∀ x : ℝ, x ≤ 0 → f (x * I) = g (x * I)) :
    EqOn f g {z | 0 ≤ z.re ∧ z.im ≤ 0} := fun _z hz =>
  sub_eq_zero.1 <| eq_zero_on_quadrant_IV (hdf.sub hdg) (isBigO_sub_exp_rpow hBf hBg)
    (fun x hx => sub_eq_zero.2 <| hre x hx) (fun x hx => sub_eq_zero.2 <| him x hx) hz

/-!
### Phragmen-Lindelöf principle in the right half-plane
-/


/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `f x → 0` as `x : ℝ` tends to infinity.

Then `‖f z‖` is bounded from above by the same constant on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_bounded_on_real` for a stronger version. -/
/-
**PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real** 是 Mathlib 中的一个定理，位
于命名空间 `PhragmenLindelof`。
形式化陈述：right_half_plane_of_tendsto_zero_on_real (hd : DiffContOnCl Complex f {z |
 0 < z.re}) (hexp : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 
{z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)) (hre : Tendsto (fun x : Real => f x
) atTop (𝓝 0)) (him : forall x : Real, ‖f (x * I)‖ <= C) (hz : 0 <= z.re) : ‖f z
‖ <= C
参数：hd : DiffContOnCl Complex f {z | 0 < z.re}；hexp : exists c < (2 : Real), exis
ts B, f =O[cobounded Complex ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)；hre
 : Tendsto (fun x : Real => f x) atTop (𝓝 0)；him : forall x : Real, ‖f (x * I)‖ 
<= C；hz : 0 <= z.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.closure_setOfPred_lt_re`：closure_setOfPred_lt_re (a : Real) : cl
osure { z : Complex | a < z.re } = { z | a <= z.re }
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `cocompact_eq_atBot_atTop`：cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMin
Order α] [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atT
op
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Filter.disjoint_atBot_principal_Ici`：∀ {α : Type u_3} [inst : Preorder α
] [NoBotOrder α] (x : α), Disjoint Filter.atBot (Filter.principal (Set.Ici x))
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
**Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a fu
nction such that

* `f` is differentiable in the open right half-plane and is continuous on its cl
osure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half
-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `f x → 0` as `x : ℝ` tends to infinity.

Then `‖f z‖` is bounded from above by the same constant on the closed right half
-plane.
See also `PhragmenLindelof.right_half_plane_of_bounded_on_real` for a stronger v
ersion.
-/
theorem right_half_plane_of_tendsto_zero_on_real (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : Tendsto (fun x : ℝ => f x) atTop (𝓝 0)) (him : ∀ x : ℝ, ‖f (x * I)‖ ≤ C)
    (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  /- We are going to apply the Phragmen-Lindelöf principle in the first and fourth quadrants.
    The lemmas immediately imply that for any upper estimate `C'` on `‖f x‖`, `x : ℝ`, `0 ≤ x`,
    the number `max C C'` is an upper estimate on `f` in the whole right half-plane. -/
  revert z
  have hle : ∀ C', (∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C') →
      ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ max C C' := fun C' hC' z hz ↦ by
    rcases hexp with ⟨c, hc, B, hO⟩
    rcases le_total z.im 0 with h | h
    · refine quadrant_IV (hd.mono fun _ => And.left) ⟨c, hc, B, ?_⟩
          (fun x hx => (hC' x hx).trans <| le_max_right _ _)
          (fun x _ => (him x).trans (le_max_left _ _)) hz h
      exact hO.mono (inf_le_inf_left _ <| principal_mono.2 fun _ => And.left)
    · refine quadrant_I (hd.mono fun _ => And.left) ⟨c, hc, B, ?_⟩
          (fun x hx => (hC' x hx).trans <| le_max_right _ _)
          (fun x _ => (him x).trans (le_max_left _ _)) hz h
      exact hO.mono (inf_le_inf_left _ <| principal_mono.2 fun _ => And.left)
  -- Since `f` is continuous on `Ici 0` and `‖f x‖` tends to zero as `x → ∞`,
  -- the norm `‖f x‖` takes its maximum value at some `x₀ : ℝ`.
  obtain ⟨x₀, hx₀, hmax⟩ : ∃ x : ℝ, 0 ≤ x ∧ ∀ y : ℝ, 0 ≤ y → ‖f y‖ ≤ ‖f x‖ := by
    have hfc : ContinuousOn (fun x : ℝ => f x) (Ici 0) := by
      refine hd.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rwa [closure_setOfPred_lt_re]
    by_cases! h₀ : ∀ x : ℝ, 0 ≤ x → f x = 0
    · refine ⟨0, le_rfl, fun y hy => ?_⟩; rw [h₀ y hy, h₀ 0 le_rfl]
    rcases h₀ with ⟨x₀, hx₀, hne⟩
    have hlt : ‖(0 : E)‖ < ‖f x₀‖ := by rwa [norm_zero, norm_pos_iff]
    suffices ∀ᶠ x : ℝ in cocompact ℝ ⊓ 𝓟 (Ici 0), ‖f x‖ ≤ ‖f x₀‖ by
      simpa only [exists_prop] using! hfc.norm.exists_isMaxOn' isClosed_Ici hx₀ this
    rw [cocompact_eq_atBot_atTop, inf_sup_right, (disjoint_atBot_principal_Ici (0 : ℝ)).eq_bot,
      bot_sup_eq]
    exact (hre.norm.eventually <| ge_mem_nhds hlt).filter_mono inf_le_left
  rcases le_or_gt ‖f x₀‖ C with h | h
  · -- If `‖f x₀‖ ≤ C`, then `hle` implies the required estimate
    simpa only [max_eq_left h] using hle _ hmax
  · -- Otherwise, `‖f z‖ ≤ ‖f x₀‖` for all `z` in the right half-plane due to `hle`.
    replace hmax : IsMaxOn (norm ∘ f) {z | 0 < z.re} x₀ := by
      rintro z (hz : 0 < z.re)
      simpa [max_eq_right h.le] using hle _ hmax _ hz.le
    -- Due to the maximum modulus principle applied to the closed ball of radius `x₀.re`,
    -- `‖f 0‖ = ‖f x₀‖`.
    have : ‖f 0‖ = ‖f x₀‖ := by
      apply norm_eq_norm_of_isMaxOn_of_ball_subset hd hmax
      -- move to a lemma?
      intro z hz
      rw [mem_ball, dist_zero_left, dist_eq, Complex.norm_of_nonneg hx₀] at hz
      rw [mem_ofPred_eq]
      contrapose! hz
      calc
        x₀ ≤ x₀ - z.re := (le_sub_self_iff _).2 hz
        _ ≤ |x₀ - z.re| := le_abs_self _
        _ = |(z - x₀).re| := by rw [sub_re, ofReal_re, _root_.abs_sub_comm]
        _ ≤ ‖z - x₀‖ := abs_re_le_norm _
    -- Thus we have `C < ‖f x₀‖ = ‖f 0‖ ≤ C`. Contradiction completes the proof.
    refine (h.not_ge <| this ▸ ?_).elim
    simpa using him 0

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `‖f x‖` is bounded from above by a constant for large real values of `x`.

Then `‖f z‖` is bounded from above by `C` on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real` for a weaker version. -/
/-
**PhragmenLindelof.right_half_plane_of_bounded_on_real** 是 Mathlib 中的一个定理，位于命名空间
 `PhragmenLindelof`。
形式化陈述：right_half_plane_of_bounded_on_real (hd : DiffContOnCl Complex f {z | 0 < 
z.re}) (hexp : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 {z | 
0 < z.re}] fun z => expR (B * ‖z‖ ^ c)) (hre : IsBoundedUnder (· <= ·) atTop fun
 x : Real => ‖f x‖) (him : forall x : Real, ‖f (x * I)‖ <= C) (hz : 0 <= z.re) :
 ‖f z‖ <= C
参数：hd : DiffContOnCl Complex f {z | 0 < z.re}；hexp : exists c < (2 : Real), exis
ts B, f =O[cobounded Complex ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)；hre
 : IsBoundedUnder (· <= ·) atTop fun x : Real => ‖f x‖；him : forall x : Real, ‖f
 (x * I)‖ <= C；hz : 0 <= z.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DiffContOnCl.smul`：smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [Norme
dAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {f : E ->
 F} {s …
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Differentiable.cexp`：Differentiable.cexp (hc : Differentiable 𝕜 f) : Dif
ferentiable 𝕜 fun x => Complex.exp (f x)
· 使用定理 `Differentiable.const_mul`：Differentiable.const_mul (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => b * a y
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`：right_half_pl
ane_of_tendsto_zero_on_real (hd : DiffContOnCl Complex f {z | 0 < z.re}) (hexp :
 exists c < (2 : Real), exists B, f =O[cobounde…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.of_bound'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 (∀ᶠ (x : α) in l,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.exp_le_one_iff`：exp_le_one_iff {x : Real} : exp x <= 1 ↔ x <= 0
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
**Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a fu
nction such that

* `f` is differentiable in the open right half-plane and is continuous on its cl
osure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half
-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant `C` on the imaginary axis;
* `‖f x‖` is bounded from above by a constant for large real values of `x`.

Then `‖f z‖` is bounded from above by `C` on the closed right half-plane.
See also `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real` for a weake
r version.
-/
theorem right_half_plane_of_bounded_on_real (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖) (him : ∀ x : ℝ, ‖f (x * I)‖ ≤ C)
    (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  -- For each `ε < 0`, the function `fun z ↦ exp (ε * z) • f z` satisfies assumptions of
  -- `right_half_plane_of_tendsto_zero_on_real`, hence `‖exp (ε * z) • f z‖ ≤ C` for all `ε < 0`.
  -- Taking the limit as `ε → 0`, we obtain the required inequality.
  suffices ∀ᶠ ε : ℝ in 𝓝[<] 0, ‖exp (ε * z) • f z‖ ≤ C by
    refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) this
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [self_mem_nhdsWithin] with ε ε₀; change ε < 0 at ε₀
  set g : ℂ → E := fun z => exp (ε * z) • f z; change ‖g z‖ ≤ C
  replace hd : DiffContOnCl ℂ g {z : ℂ | 0 < z.re} :=
    (differentiable_id.const_mul _).cexp.diffContOnCl.smul hd
  have hgn : ∀ z, ‖g z‖ = expR (ε * z.re) * ‖f z‖ := fun z ↦ by
    rw [norm_smul, norm_exp, re_ofReal_mul]
  refine right_half_plane_of_tendsto_zero_on_real hd ?_ ?_ (fun y => ?_) hz
  · rcases hexp with ⟨c, hc, B, hO⟩
    refine ⟨c, hc, B, .trans (.of_bound' ?_) hO⟩
    refine eventually_inf_principal.2 <| Eventually.of_forall fun z hz => ?_
    rw [hgn]
    refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    exact mul_nonpos_of_nonpos_of_nonneg ε₀.le (le_of_lt hz)
  · simp_rw [g, ← ofReal_mul, ← ofReal_exp, coe_smul]
    have h₀ : Tendsto (fun x : ℝ => expR (ε * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop ε₀ tendsto_id)
    exact h₀.zero_smul_isBoundedUnder_le hre
  · rw [hgn, re_ofReal_mul, I_re, mul_zero, mul_zero, Real.exp_zero,
      one_mul]
    exact him y

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant on the imaginary axis;
* `f x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x‖` tends to zero as `x → ∞`.

Then `f` is equal to zero on the closed right half-plane. -/
/-
**PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay** 是 Mat
hlib 中的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：eq_zero_on_right_half_plane_of_superexponential_decay (hd : DiffContOnCl C
omplex f {z | 0 < z.re}) (hexp : exists c < (2 : Real), exists B, f =O[cobounded
 Complex ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)) (hre : Superpolynomial
Decay atTop expR fun x => ‖f x‖) (him : exists C, forall x : Real, ‖f (x * I)‖ <
= C) : EqOn f 0 {z : Complex | 0 <= z.re}
参数：hd : DiffContOnCl Complex f {z | 0 < z.re}；hexp : exists c < (2 : Real), exis
ts B, f =O[cobounded Complex ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)；hre
 : SuperpolynomialDecay atTop expR fun x => ‖f x‖；him : exists C, forall x : Rea
l, ‖f (x * I)‖ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real`：right_half_pl
ane_of_tendsto_zero_on_real (hd : DiffContOnCl Complex f {z | 0 < z.re}) (hexp :
 exists c < (2 : Real), exists B, f =O[cobounde…
· 使用定理 `DiffContOnCl.smul`：smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [Norme
dAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E -> 𝕜'} {f : E ->
 F} {s …
· 使用定理 `Differentiable.diffContOnCl`：Differentiable.diffContOnCl (h : Differenti
able 𝕜 f) : DiffContOnCl 𝕜 f s
· 使用定理 `Differentiable.pow`：Differentiable.pow (hf : Differentiable 𝕜 f) (n : Na
t) : Differentiable 𝕜 (f ^ n)
· 使用定理 `Complex.differentiable_exp`：differentiable_exp : Differentiable 𝕜 exp
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
**Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a fu
nction such that

* `f` is differentiable in the open right half-plane and is continuous on its cl
osure;
* `‖f z‖` is bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right half
-plane
  for some `c < 2`;
* `‖f z‖` is bounded from above by a constant on the imaginary axis;
* `f x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x‖` tends to zero as `x → ∞`.

Then `f` is equal to zero on the closed right half-plane.
-/
theorem eq_zero_on_right_half_plane_of_superexponential_decay (hd : DiffContOnCl ℂ f {z | 0 < z.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : SuperpolynomialDecay atTop expR fun x => ‖f x‖) (him : ∃ C, ∀ x : ℝ, ‖f (x * I)‖ ≤ C) :
    EqOn f 0 {z : ℂ | 0 ≤ z.re} := by
  rcases him with ⟨C, hC⟩
  -- Due to continuity, it suffices to prove the equality on the open right half-plane.
  suffices ∀ z : ℂ, 0 < z.re → f z = 0 by
    simpa only [closure_setOfPred_lt_re] using!
      EqOn.of_subset_closure this hd.continuousOn continuousOn_const subset_closure Subset.rfl
  -- Consider $g_n(z)=e^{nz}f(z)$.
  set g : ℕ → ℂ → E := fun (n : ℕ) (z : ℂ) => exp z ^ n • f z
  have hg : ∀ n z, ‖g n z‖ = expR z.re ^ n * ‖f z‖ := fun n z ↦ by
    simp only [g, norm_smul, norm_pow, norm_exp]
  intro z hz
  -- Since `e^{nz} → ∞` as `n → ∞`, it suffices to show that each `g_n` is bounded from above by `C`
  suffices H : ∀ n : ℕ, ‖g n z‖ ≤ C by
    contrapose! H
    simp only [hg]
    exact (((tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_exp_iff.2 hz)).atTop_mul_const
      (norm_pos_iff.2 H)).eventually (eventually_gt_atTop C)).exists
  intro n
  -- This estimate follows from the Phragmen-Lindelöf principle in the right half-plane.
  refine right_half_plane_of_tendsto_zero_on_real ((differentiable_exp.pow n).diffContOnCl.smul hd)
    ?_ ?_ (fun y => ?_) hz.le
  · rcases hexp with ⟨c, hc, B, hO⟩
    refine ⟨max c 1, max_lt hc one_lt_two, n + max B 0, .of_norm_left ?_⟩
    simp only [hg]
    refine ((isBigO_refl (fun z : ℂ => expR z.re ^ n) _).mul hO.norm_left).trans (.of_bound' ?_)
    filter_upwards [(eventually_cobounded_le_norm 1).filter_mono inf_le_left] with z hz
    simp only [← Real.exp_nat_mul, ← Real.exp_add, Real.norm_eq_abs, Real.abs_exp, add_mul]
    gcongr
    · calc
        z.re ≤ ‖z‖ := re_le_norm _
        _ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖z‖ ^ max c 1 := Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _)
    exacts [le_max_left _ _, le_max_left _ _]
  · rw [tendsto_zero_iff_norm_tendsto_zero]; simp only [hg]
    exact hre n
  · rw [hg, re_ofReal_mul, I_re, mul_zero, Real.exp_zero, one_pow, one_mul]
    exact hC y

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f g : ℂ → E` be functions such
that

* `f` and `g` are differentiable in the open right half-plane and are continuous on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the open right
  half-plane for some `c < 2`;
* `‖f z‖` and `‖g z‖` are bounded from above by constants on the imaginary axis;
* `f x - g x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x - g x‖` tends to zero as `x → ∞`.

Then `f` is equal to `g` on the closed right half-plane. -/
/-
**PhragmenLindelof.eqOn_right_half_plane_of_superexponential_decay** 是 Mathlib 中
的一个定理，位于命名空间 `PhragmenLindelof`。
形式化陈述：eqOn_right_half_plane_of_superexponential_decay {g : Complex -> E} (hfd : 
DiffContOnCl Complex f {z | 0 < z.re}) (hgd : DiffContOnCl Complex g {z | 0 < z.
re}) (hfexp : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 {z | 0
 < z.re}] fun z => expR (B * ‖z‖ ^ c)) (hgexp : exists c < (2 : Real), exists B,
 g =O[cobounded Complex ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)) (hre : 
SuperpolynomialDecay atTop expR fun x => ‖f x - g x‖) (hfim : exists C, forall x
 : Real, ‖f (x * I)‖ <= C)
参数：hfd : DiffContOnCl Complex f {z | 0 < z.re}；hgd : DiffContOnCl Complex g {z |
 0 < z.re}；hfexp : exists c < (2 : Real), exists B, f =O[cobounded Complex ⊓ 𝓟 {
z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)；hgexp : exists c < (2 : Real), exists
 B, g =O[cobounded Complex ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c)；hre :
 SuperpolynomialDecay atTop expR fun x => ‖f x - g x‖；hfim : exists C, forall x 
: Real, ‖f (x * I)‖ <= C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`：
eq_zero_on_right_half_plane_of_superexponential_decay (hd : DiffContOnCl Complex
 f {z | 0 < z.re}) (hexp : exists c < (2 : Real), exists B, …
· 使用定理 `DiffContOnCl.sub`：sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s
) : DiffContOnCl 𝕜 (f - g) s
· 使用定理 `PhragmenLindelof.isBigO_sub_exp_rpow`：isBigO_sub_exp_rpow {a : Real} {f 
g : Complex -> E} {l : Filter Complex} (hBf : exists c < a, exists B, f =O[cobou
nded Complex ⊓ l] fun z =>…
· 使用定理 `norm_sub_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ - a₂‖ ≤ r₁ + r₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
**Phragmen-Lindelöf principle** in the right half-plane. Let `f g : ℂ → E` be fu
nctions such
that

* `f` and `g` are differentiable in the open right half-plane and are continuous
 on its closure;
* `‖f z‖` and `‖g z‖` are bounded from above by `A * exp(B * ‖z‖ ^ c)` on the op
en right
  half-plane for some `c < 2`;
* `‖f z‖` and `‖g z‖` are bounded from above by constants on the imaginary axis;
* `f x - g x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ‖f x - g x‖` tends to zero as `x → ∞`.

Then `f` is equal to `g` on the closed right half-plane.
-/
theorem eqOn_right_half_plane_of_superexponential_decay {g : ℂ → E}
    (hfd : DiffContOnCl ℂ f {z | 0 < z.re}) (hgd : DiffContOnCl ℂ g {z | 0 < z.re})
    (hfexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hgexp : ∃ c < (2 : ℝ), ∃ B,
      g =O[cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}] fun z => expR (B * ‖z‖ ^ c))
    (hre : SuperpolynomialDecay atTop expR fun x => ‖f x - g x‖)
    (hfim : ∃ C, ∀ x : ℝ, ‖f (x * I)‖ ≤ C) (hgim : ∃ C, ∀ x : ℝ, ‖g (x * I)‖ ≤ C) :
    EqOn f g {z : ℂ | 0 ≤ z.re} := by
  suffices EqOn (f - g) 0 {z : ℂ | 0 ≤ z.re} by
    simpa only [EqOn, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using this
  refine eq_zero_on_right_half_plane_of_superexponential_decay (hfd.sub hgd) ?_ hre ?_
  · exact isBigO_sub_exp_rpow hfexp hgexp
  · rcases hfim with ⟨Cf, hCf⟩; rcases hgim with ⟨Cg, hCg⟩
    exact ⟨Cf + Cg, fun x => norm_sub_le_of_le (hCf x) (hCg x)⟩

end PhragmenLindelof

