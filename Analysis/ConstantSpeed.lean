/-
Copyright (c) 2023 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Constant speed

This file defines the notion of constant (and unit) speed for a function `f : ℝ → E` with
pseudo-emetric structure on `E` with respect to a set `s : Set ℝ` and "speed" `l : ℝ≥0`, and shows
that if `f` has locally bounded variation on `s`, it can be obtained (up to distance zero, on `s`),
as a composite `φ ∘ (variationOnFromTo f s a)`, where `φ` has unit speed and `a ∈ s`.

## Main definitions

* `HasConstantSpeedOnWith f s l`, stating that the speed of `f` on `s` is `l`.
* `HasUnitSpeedOn f s`, stating that the speed of `f` on `s` is `1`.
* `naturalParameterization f s a : ℝ → E`, the unit speed reparameterization of `f` on `s` relative
  to `a`.

## Main statements

* `unique_unit_speed_on_Icc_zero` proves that if `f` and `f ∘ φ` are both naturally
  parameterized on closed intervals starting at `0`, then `φ` must be the identity on
  those intervals.
* `edist_naturalParameterization_eq_zero` proves that if `f` has locally bounded variation, then
  precomposing `naturalParameterization f s a` with `variationOnFromTo f s a` yields a function
  at distance zero from `f` on `s`.
* `has_unit_speed_naturalParameterization` proves that if `f` has locally bounded
  variation, then `naturalParameterization f s a` has unit speed on `s`.

## Tags

arc-length, parameterization
-/

@[expose] public section


open scoped NNReal ENNReal

open Set

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]
variable (f : ℝ → E) (s : Set ℝ) (l : ℝ≥0)

/-- `f` has constant speed `l` on `s` if the variation of `f` on `s ∩ Icc x y` is equal to
`l * (y - x)` for any `x y` in `s`.
-/
/-
**HasConstantSpeedOnWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasConstantSpeedOnWith
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has constant speed `l` on `s` if the variation of `f` on `s ∩ Icc x y` is eq
ual to
`l * (y - x)` for any `x y` in `s`.
-/
def HasConstantSpeedOnWith :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), eVariationOn f (s ∩ Icc x y) = ENNReal.ofReal (l * (y - x))

variable {f s l}
/-
**HasConstantSpeedOnWith.hasLocallyBoundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasConstantSpeedOnWith.hasLocallyBoundedVariationOn (h : HasConstantSpeedO
nWith f s l) : LocallyBoundedVariationOn f s
参数：h : HasConstantSpeedOnWith f s l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem HasConstantSpeedOnWith.hasLocallyBoundedVariationOn (h : HasConstantSpeedOnWith f s l) :
    LocallyBoundedVariationOn f s := fun x y hx hy => by
  simp only [BoundedVariationOn, h hx hy, Ne, ENNReal.ofReal_ne_top, not_false_iff]
/-
**hasConstantSpeedOnWith_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasConstantSpeedOnWith_of_subsingleton (f : Real -> E) {s : Set Real} (hs 
: s.Subsingleton) (l : Real>=0) : HasConstantSpeedOnWith f s l
参数：f : Real -> E；hs : s.Subsingleton；l : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hasConstantSpeedOnWith_of_subsingleton (f : ℝ → E) {s : Set ℝ} (hs : s.Subsingleton)
    (l : ℝ≥0) : HasConstantSpeedOnWith f s l := by
  rintro x hx y hy; cases hs hx hy
  rw [eVariationOn.subsingleton f (fun y hy z hz => hs hy.1 hz.1 : (s ∩ Icc x x).Subsingleton)]
  simp only [sub_self, mul_zero, ENNReal.ofReal_zero]
/-
**hasConstantSpeedOnWith_iff_ordered** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasConstantSpeedOnWith_iff_ordered : HasConstantSpeedOnWith f s l ↔ forall
 ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x <= y -> eVariationOn f (s inter Icc x y) =
 ENNReal.ofReal (l * (y - x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `sub_nonpos_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → a - b ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem hasConstantSpeedOnWith_iff_ordered :
    HasConstantSpeedOnWith f s l ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s),
      x ≤ y → eVariationOn f (s ∩ Icc x y) = ENNReal.ofReal (l * (y - x)) := by
  refine ⟨fun h x xs y ys _ => h xs ys, fun h x xs y ys => ?_⟩
  rcases le_total x y with (xy | yx)
  · exact h xs ys xy
  · rw [eVariationOn.subsingleton, ENNReal.ofReal_of_nonpos]
    · exact mul_nonpos_of_nonneg_of_nonpos l.prop (sub_nonpos_of_le yx)
    · rintro z ⟨zs, xz, zy⟩ w ⟨ws, xw, wy⟩
      cases le_antisymm (zy.trans yx) xz
      cases le_antisymm (wy.trans yx) xw
      rfl
/-
**hasConstantSpeedOnWith_iff_variationOnFromTo_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasConstantSpeedOnWith_iff_variationOnFromTo_eq : HasConstantSpeedOnWith f
 s l ↔ LocallyBoundedVariationOn f s ∧ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s),
 variationOnFromTo f s x y = l * (y - x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasConstantSpeedOnWith.hasLocallyBoundedVariationOn`：HasConstantSpeedOnW
ith.hasLocallyBoundedVariationOn (h : HasConstantSpeedOnWith f s l) : LocallyBou
ndedVariationOn f s
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `hasConstantSpeedOnWith_iff_ordered`：hasConstantSpeedOnWith_iff_ordered :
 HasConstantSpeedOnWith f s l ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x <= y
 -> eVariationOn f (s in…
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `variationOnFromTo.eq_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
b ≤ a → variatio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 47 条，此处仅展示前 30 条）
-/
theorem hasConstantSpeedOnWith_iff_variationOnFromTo_eq :
    HasConstantSpeedOnWith f s l ↔ LocallyBoundedVariationOn f s ∧
      ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), variationOnFromTo f s x y = l * (y - x) := by
  constructor
  · rintro h; refine ⟨h.hasLocallyBoundedVariationOn, fun x xs y ys => ?_⟩
    rw [hasConstantSpeedOnWith_iff_ordered] at h
    rcases le_total x y with (xy | yx)
    · rw [variationOnFromTo.eq_of_le f s xy, h xs ys xy]
      exact ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonneg.mpr xy))
    · rw [variationOnFromTo.eq_of_ge f s yx, h ys xs yx]
      have := ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonneg.mpr yx))
      simp_all only [NNReal.val_eq_coe]; ring
  · rw [hasConstantSpeedOnWith_iff_ordered]
    rintro h x xs y ys xy
    rw [← h.2 xs ys, variationOnFromTo.eq_of_le f s xy, ENNReal.ofReal_toReal (h.1 x y xs ys)]
/-
**HasConstantSpeedOnWith.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasConstantSpeedOnWith.union {t : Set Real} (hfs : HasConstantSpeedOnWith 
f s l) (hft : HasConstantSpeedOnWith f t l) {x : Real} (hs : IsGreatest s x) (ht
 : IsLeast t x) : HasConstantSpeedOnWith f (s union t) l
参数：hfs : HasConstantSpeedOnWith f s l；hft : HasConstantSpeedOnWith f t l；hs : Is
Greatest s x；ht : IsLeast t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasConstantSpeedOnWith_iff_ordered`：hasConstantSpeedOnWith_iff_ordered :
 HasConstantSpeedOnWith f s l ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x <= y
 -> eVariationOn f (s in…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eVariationOn.union`：union (f : α -> E) {s t : Set α} {x : α} (hs : IsGre
atest s x) (ht : IsLeast t x) : eVariationOn f (s union t) = eVariationOn f s + 
eVariati…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 66 条，此处仅展示前 30 条）
-/
theorem HasConstantSpeedOnWith.union {t : Set ℝ} (hfs : HasConstantSpeedOnWith f s l)
    (hft : HasConstantSpeedOnWith f t l) {x : ℝ} (hs : IsGreatest s x) (ht : IsLeast t x) :
    HasConstantSpeedOnWith f (s ∪ t) l := by
  rw [hasConstantSpeedOnWith_iff_ordered] at hfs hft ⊢
  rintro z (zs | zt) y (ys | yt) zy
  · have : (s ∪ t) ∩ Icc z y = s ∩ Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨ws, zw, wy⟩
        · exact ⟨(le_antisymm (wy.trans (hs.2 ys)) (ht.2 wt)).symm ▸ hs.1, zw, wy⟩
      · rintro ⟨ws, zwy⟩; exact ⟨Or.inl ws, zwy⟩
    rw [this, hfs zs ys zy]
  · have : (s ∪ t) ∩ Icc z y = s ∩ Icc z x ∪ t ∩ Icc x y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        exacts [Or.inl ⟨ws, zw, hs.2 ws⟩, Or.inr ⟨wt, ht.2 wt, wy⟩]
      · rintro (⟨ws, zw, wx⟩ | ⟨wt, xw, wy⟩)
        exacts [⟨Or.inl ws, zw, wx.trans (ht.2 yt)⟩, ⟨Or.inr wt, (hs.2 zs).trans xw, wy⟩]
    rw [this, @eVariationOn.union _ _ _ _ f _ _ x, hfs zs hs.1 (hs.2 zs), hft ht.1 yt (ht.2 yt)]
    · have q := ENNReal.ofReal_add (mul_nonneg l.prop (sub_nonneg.mpr (hs.2 zs)))
        (mul_nonneg l.prop (sub_nonneg.mpr (ht.2 yt)))
      simp only [NNReal.val_eq_coe] at q
      rw [← q]
      ring_nf
    exacts [⟨⟨hs.1, hs.2 zs, le_rfl⟩, fun w ⟨_, _, wx⟩ => wx⟩,
      ⟨⟨ht.1, le_rfl, ht.2 yt⟩, fun w ⟨_, xw, _⟩ => xw⟩]
  · cases le_antisymm zy ((hs.2 ys).trans (ht.2 zt))
    simp only [Icc_self, sub_self, mul_zero, ENNReal.ofReal_zero]
    exact eVariationOn.subsingleton _ fun _ ⟨_, uz⟩ _ ⟨_, vz⟩ => uz.trans vz.symm
  · have : (s ∪ t) ∩ Icc z y = t ∩ Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨le_antisymm ((ht.2 zt).trans zw) (hs.2 ws) ▸ ht.1, zw, wy⟩
        · exact ⟨wt, zw, wy⟩
      · rintro ⟨wt, zwy⟩; exact ⟨Or.inr wt, zwy⟩
    rw [this, hft zt yt zy]
/-
**HasConstantSpeedOnWith.Icc_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasConstantSpeedOnWith.Icc_Icc {x y z : Real} (hfs : HasConstantSpeedOnWit
h f (Icc x y) l) (hft : HasConstantSpeedOnWith f (Icc y z) l) : HasConstantSpeed
OnWith f (Icc x z) l
参数：hfs : HasConstantSpeedOnWith f (Icc x y) l；hft : HasConstantSpeedOnWith f (Ic
c y z) l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Icc_eq_Icc`：Icc_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= 
c) : Icc a b union Icc b c = Icc a c
· 使用定理 `HasConstantSpeedOnWith.union`：HasConstantSpeedOnWith.union {t : Set Real
} (hfs : HasConstantSpeedOnWith f s l) (hft : HasConstantSpeedOnWith f t l) {x :
 Real} (hs : IsGre…
· 使用定理 `isGreatest_Icc`：isGreatest_Icc (h : a <= b) : IsGreatest (Icc a b) b
· 使用定理 `isLeast_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ a → IsL
east (Set.Icc b a) b
· 使用定理 `Set.Icc_inter_Icc`：Icc_inter_Icc : Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔
 a₂) (b₁ ⊓ b₂)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem HasConstantSpeedOnWith.Icc_Icc {x y z : ℝ} (hfs : HasConstantSpeedOnWith f (Icc x y) l)
    (hft : HasConstantSpeedOnWith f (Icc y z) l) : HasConstantSpeedOnWith f (Icc x z) l := by
  rcases le_total x y with (xy | yx)
  · rcases le_total y z with (yz | zy)
    · rw [← Set.Icc_union_Icc_eq_Icc xy yz]
      exact hfs.union hft (isGreatest_Icc xy) (isLeast_Icc yz)
    · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
      rw [Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right vz, ←
        hfs ⟨xu, uz.trans zy⟩ ⟨xv, vz.trans zy⟩, Icc_inter_Icc, sup_of_le_right xu,
        inf_of_le_right (vz.trans zy)]
  · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
    rw [Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right vz, ←
      hft ⟨yx.trans xu, uz⟩ ⟨yx.trans xv, vz⟩, Icc_inter_Icc, sup_of_le_right (yx.trans xu),
      inf_of_le_right vz]
/-
**hasConstantSpeedOnWith_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasConstantSpeedOnWith_zero_iff : HasConstantSpeedOnWith f s 0 ↔ forallᵉ (
x in s) (y in s), edist (f x) (f y) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eVariationOn.mono`：mono (f : α -> E) {s t : Set α} (hst : t subseteq s) 
: eVariationOn f t <= eVariationOn f s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem hasConstantSpeedOnWith_zero_iff :
    HasConstantSpeedOnWith f s 0 ↔ ∀ᵉ (x ∈ s) (y ∈ s), edist (f x) (f y) = 0 := by
  dsimp [HasConstantSpeedOnWith]
  simp only [zero_mul, ENNReal.ofReal_zero, ← eVariationOn.eq_zero_iff]
  constructor
  · by_contra! ⟨h, hfs⟩
    simp_rw [ne_eq, eVariationOn.eq_zero_iff] at hfs h
    push Not at hfs
    obtain ⟨x, xs, y, ys, hxy⟩ := hfs
    rcases le_total x y with (xy | yx)
    · exact hxy (h xs ys x ⟨xs, le_rfl, xy⟩ y ⟨ys, xy, le_rfl⟩)
    · rw [edist_comm] at hxy
      exact hxy (h ys xs y ⟨ys, le_rfl, yx⟩ x ⟨xs, yx, le_rfl⟩)
  · rintro h x _ y _
    simpa [h] using eVariationOn.mono (s := s) f inter_subset_left
/-
**HasConstantSpeedOnWith.ratio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasConstantSpeedOnWith.ratio {l' : Real>=0} (hl' : l' != 0) {φ : Real -> R
eal} (φm : MonotoneOn φ s) (hfφ : HasConstantSpeedOnWith (f ∘ φ) s l) (hf : HasC
onstantSpeedOnWith f (φ '' s) l') ⦃x : Real⦄ (xs : x in s) : EqOn φ (fun y => l 
/ l' * (y - x) + φ x) s
参数：hl' : l' != 0；φm : MonotoneOn φ s；hfφ : HasConstantSpeedOnWith (f ∘ φ) s l；hf
 : HasConstantSpeedOnWith f (φ '' s) l'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `hasConstantSpeedOnWith_iff_variationOnFromTo_eq`：hasConstantSpeedOnWith_
iff_variationOnFromTo_eq : HasConstantSpeedOnWith f s l ↔ LocallyBoundedVariatio
nOn f s ∧ forall ⦃x⦄ (_ : x in s) ⦃y⦄…
· 使用定理 `variationOnFromTo.comp_eq_of_monotoneOn`：∀ {α : Type u_1} [inst : Linear
Order α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {β : Type u_3}   [inst_2
 : LinearOrder β] (f : α → E)…
-/
theorem HasConstantSpeedOnWith.ratio {l' : ℝ≥0} (hl' : l' ≠ 0) {φ : ℝ → ℝ} (φm : MonotoneOn φ s)
    (hfφ : HasConstantSpeedOnWith (f ∘ φ) s l) (hf : HasConstantSpeedOnWith f (φ '' s) l') ⦃x : ℝ⦄
    (xs : x ∈ s) : EqOn φ (fun y => l / l' * (y - x) + φ x) s := by
  rintro y ys
  rw [← sub_eq_iff_eq_add, mul_comm, ← mul_div_assoc, eq_div_iff (NNReal.coe_ne_zero.mpr hl')]
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hf
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hfφ
  symm
  calc
    (y - x) * l = l * (y - x) := by rw [mul_comm]
    _ = variationOnFromTo (f ∘ φ) s x y := (hfφ.2 xs ys).symm
    _ = variationOnFromTo f (φ '' s) (φ x) (φ y) :=
      (variationOnFromTo.comp_eq_of_monotoneOn f φ φm xs ys)
    _ = l' * (φ y - φ x) := (hf.2 ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩)
    _ = (φ y - φ x) * l' := by rw [mul_comm]

/-- `f` has unit speed on `s` if it is linearly parameterized by `l = 1` on `s`. -/
/-
**HasUnitSpeedOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasUnitSpeedOn (f : Real -> E) (s : Set Real)
参数：f : Real -> E；s : Set Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` has unit speed on `s` if it is linearly parameterized by `l = 1` on `s`.
-/
def HasUnitSpeedOn (f : ℝ → E) (s : Set ℝ) :=
  HasConstantSpeedOnWith f s 1
/-
**HasUnitSpeedOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasUnitSpeedOn.union {t : Set Real} {x : Real} (hfs : HasUnitSpeedOn f s) 
(hft : HasUnitSpeedOn f t) (hs : IsGreatest s x) (ht : IsLeast t x) : HasUnitSpe
edOn f (s union t)
参数：hfs : HasUnitSpeedOn f s；hft : HasUnitSpeedOn f t；hs : IsGreatest s x；ht : Is
Least t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasConstantSpeedOnWith.union`：HasConstantSpeedOnWith.union {t : Set Real
} (hfs : HasConstantSpeedOnWith f s l) (hft : HasConstantSpeedOnWith f t l) {x :
 Real} (hs : IsGre…
-/
theorem HasUnitSpeedOn.union {t : Set ℝ} {x : ℝ} (hfs : HasUnitSpeedOn f s)
    (hft : HasUnitSpeedOn f t) (hs : IsGreatest s x) (ht : IsLeast t x) :
    HasUnitSpeedOn f (s ∪ t) :=
  HasConstantSpeedOnWith.union hfs hft hs ht
/-
**HasUnitSpeedOn.Icc_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasUnitSpeedOn.Icc_Icc {x y z : Real} (hfs : HasUnitSpeedOn f (Icc x y)) (
hft : HasUnitSpeedOn f (Icc y z)) : HasUnitSpeedOn f (Icc x z)
参数：hfs : HasUnitSpeedOn f (Icc x y)；hft : HasUnitSpeedOn f (Icc y z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasConstantSpeedOnWith.Icc_Icc`：HasConstantSpeedOnWith.Icc_Icc {x y z : 
Real} (hfs : HasConstantSpeedOnWith f (Icc x y) l) (hft : HasConstantSpeedOnWith
 f (Icc y z) l) : Ha…
-/
theorem HasUnitSpeedOn.Icc_Icc {x y z : ℝ} (hfs : HasUnitSpeedOn f (Icc x y))
    (hft : HasUnitSpeedOn f (Icc y z)) : HasUnitSpeedOn f (Icc x z) :=
  HasConstantSpeedOnWith.Icc_Icc hfs hft

/-- If both `f` and `f ∘ φ` have unit speed (on `t` and `s` respectively) and `φ`
monotonically maps `s` onto `t`, then `φ` is just a translation (on `s`).
-/
/-
**unique_unit_speed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_unit_speed {φ : Real -> Real} (φm : MonotoneOn φ s) (hfφ : HasUnitS
peedOn (f ∘ φ) s) (hf : HasUnitSpeedOn f (φ '' s)) ⦃x : Real⦄ (xs : x in s) : Eq
On φ (fun y => y - x + φ x) s
参数：φm : MonotoneOn φ s；hfφ : HasUnitSpeedOn (f ∘ φ) s；hf : HasUnitSpeedOn f (φ '
' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasConstantSpeedOnWith.ratio`：HasConstantSpeedOnWith.ratio {l' : Real>=0
} (hl' : l' != 0) {φ : Real -> Real} (φm : MonotoneOn φ s) (hfφ : HasConstantSpe
edOnWith (f ∘ φ) s…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
If both `f` and `f ∘ φ` have unit speed (on `t` and `s` respectively) and `φ`
monotonically maps `s` onto `t`, then `φ` is just a translation (on `s`).
-/
theorem unique_unit_speed {φ : ℝ → ℝ} (φm : MonotoneOn φ s) (hfφ : HasUnitSpeedOn (f ∘ φ) s)
    (hf : HasUnitSpeedOn f (φ '' s)) ⦃x : ℝ⦄ (xs : x ∈ s) : EqOn φ (fun y => y - x + φ x) s := by
  dsimp only [HasUnitSpeedOn] at hf hfφ
  convert HasConstantSpeedOnWith.ratio one_ne_zero φm hfφ hf xs
  simp

/-- If both `f` and `f ∘ φ` have unit speed (on `Icc 0 t` and `Icc 0 s` respectively)
and `φ` monotonically maps `Icc 0 s` onto `Icc 0 t`, then `φ` is the identity on `Icc 0 s`
-/
/-
**unique_unit_speed_on_Icc_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_unit_speed_on_Icc_zero {s t : Real} (hs : 0 <= s) (ht : 0 <= t) {φ 
: Real -> Real} (φm : MonotoneOn φ <| Icc 0 s) (φst : φ '' Icc 0 s = Icc 0 t) (h
fφ : HasUnitSpeedOn (f ∘ φ) (Icc 0 s)) (hf : HasUnitSpeedOn f (Icc 0 t)) : EqOn 
φ id (Icc 0 s)
参数：hs : 0 <= s；ht : 0 <= t；φm : MonotoneOn φ <| Icc 0 s；φst : φ '' Icc 0 s = Icc
 0 t；hfφ : HasUnitSpeedOn (f ∘ φ) (Icc 0 s)；hf : HasUnitSpeedOn f (Icc 0 t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `unique_unit_speed`：unique_unit_speed {φ : Real -> Real} (φm : MonotoneOn
 φ s) (hfφ : HasUnitSpeedOn (f ∘ φ) s) (hf : HasUnitSpeedOn f (φ '' s)) ⦃x : Rea
l⦄ (xs …

--- 原说明 ---
If both `f` and `f ∘ φ` have unit speed (on `Icc 0 t` and `Icc 0 s` respectively
)
and `φ` monotonically maps `Icc 0 s` onto `Icc 0 t`, then `φ` is the identity on
 `Icc 0 s`
-/
theorem unique_unit_speed_on_Icc_zero {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {φ : ℝ → ℝ}
    (φm : MonotoneOn φ <| Icc 0 s) (φst : φ '' Icc 0 s = Icc 0 t)
    (hfφ : HasUnitSpeedOn (f ∘ φ) (Icc 0 s)) (hf : HasUnitSpeedOn f (Icc 0 t)) :
    EqOn φ id (Icc 0 s) := by
  rw [← φst] at hf
  convert unique_unit_speed φm hfφ hf ⟨le_rfl, hs⟩
  have : φ 0 = 0 := by
    have hm : 0 ∈ φ '' Icc 0 s := by simp only [φst, ht, mem_Icc, le_refl, and_self]
    obtain ⟨x, xs, hx⟩ := hm
    apply le_antisymm ((φm ⟨le_rfl, hs⟩ xs xs.1).trans_eq hx) _
    have := φst ▸ mapsTo_image φ (Icc 0 s)
    exact (mem_Icc.mp (@this 0 (by rw [mem_Icc]; exact ⟨le_rfl, hs⟩))).1
  simp only [tsub_zero, this, add_zero]
  rfl

/-- The natural parameterization of `f` on `s`, which, if `f` has locally bounded variation on `s`,
* has unit speed on `s` (by `has_unit_speed_naturalParameterization`).
* composed with `variationOnFromTo f s a`, is at distance zero from `f`
  (by `edist_naturalParameterization_eq_zero`).
-/
/-
**naturalParameterization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：naturalParameterization (f : α -> E) (s : Set α) (a : α) : Real -> E
参数：f : α -> E；s : Set α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural parameterization of `f` on `s`, which, if `f` has locally bounded va
riation on `s`,
* has unit speed on `s` (by `has_unit_speed_naturalParameterization`).
* composed with `variationOnFromTo f s a`, is at distance zero from `f`
  (by `edist_naturalParameterization_eq_zero`).
-/
noncomputable def naturalParameterization (f : α → E) (s : Set α) (a : α) : ℝ → E :=
  f ∘ @Function.invFunOn _ _ ⟨a⟩ (variationOnFromTo f s a) s
/-
**edist_naturalParameterization_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_naturalParameterization_eq_zero {f : α -> E} {s : Set α} (hf : Local
lyBoundedVariationOn f s) {a : α} (as : a in s) {b : α} (bs : b in s) : edist (n
aturalParameterization f s a (variationOnFromTo f s a b)) (f b) = 0
参数：hf : LocallyBoundedVariationOn f s；as : a in s；bs : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFunOn_pos`：invFunOn_pos (h : exists a in s, f a = b) : invFu
nOn f s b in s ∧ f (invFunOn f s b) = b
· 使用定理 `variationOnFromTo.edist_zero_of_eq_zero`：∀ {α : Type u_1} [inst : Linear
Order α] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},
   LocallyBoundedVariationOn …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `variationOnFromTo.eq_left_iff`：∀ {α : Type u_1} [inst : LinearOrder α] {
E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   Locally
BoundedVariationOn …
-/
theorem edist_naturalParameterization_eq_zero {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) {b : α} (bs : b ∈ s) :
    edist (naturalParameterization f s a (variationOnFromTo f s a b)) (f b) = 0 := by
  dsimp only [naturalParameterization]
  have : Nonempty α := ⟨a⟩
  obtain ⟨cs, hc⟩ := Function.invFunOn_pos (b := variationOnFromTo f s a b) ⟨b, bs, rfl⟩
  rw [variationOnFromTo.eq_left_iff hf as cs bs] at hc
  apply variationOnFromTo.edist_zero_of_eq_zero hf cs bs hc
/-
**has_unit_speed_naturalParameterization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：has_unit_speed_naturalParameterization (f : α -> E) {s : Set α} (hf : Loca
llyBoundedVariationOn f s) {a : α} (as : a in s) : HasUnitSpeedOn (naturalParame
terization f s a) (variationOnFromTo f s a '' s)
参数：f : α -> E；hf : LocallyBoundedVariationOn f s；as : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasConstantSpeedOnWith_iff_ordered`：hasConstantSpeedOnWith_iff_ordered :
 HasConstantSpeedOnWith f s l ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x <= y
 -> eVariationOn f (s in…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `variationOnFromTo.monotoneOn`：∀ {α : Type u_1} [inst : LinearOrder α] {E
 : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyB
oundedVariationOn …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `variationOnFromTo.eq_neg_swap`：∀ {α : Type u_1} [inst : LinearOrder α] {
E : Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   (a b : α
), variationOnFromT…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `variationOnFromTo.add`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type
 u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   LocallyBoundedV
ariationOn …
· 使用定理 `eVariationOn.comp_inter_Icc_eq_of_monotoneOn`：comp_inter_Icc_eq_of_monot
oneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t) {x y : β} (hx 
: x in t) (hy : y in t) : eVariati…
· 使用定理 `eVariationOn.eq_of_edist_zero_on`：eq_of_edist_zero_on {f f' : α -> E} {s
 : Set α} (h : forall ⦃x⦄, x in s -> edist (f x) (f' x) = 0) : eVariationOn f s 
= eVariationOn f' s
· 使用定理 `edist_naturalParameterization_eq_zero`：edist_naturalParameterization_eq_
zero {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a : α} (as :
 a in s) {b : α} (bs : b in…
· 使用定理 `variationOnFromTo.eq_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α)   {a b : α}, 
a ≤ b → variatio…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
-/
theorem has_unit_speed_naturalParameterization (f : α → E) {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) :
    HasUnitSpeedOn (naturalParameterization f s a) (variationOnFromTo f s a '' s) := by
  dsimp only [HasUnitSpeedOn]
  rw [hasConstantSpeedOnWith_iff_ordered]
  rintro _ ⟨b, bs, rfl⟩ _ ⟨c, cs, rfl⟩ h
  rcases le_total c b with (cb | bc)
  · rw [NNReal.coe_one, one_mul, le_antisymm h (variationOnFromTo.monotoneOn hf as cs bs cb),
      sub_self, ENNReal.ofReal_zero, Icc_self, eVariationOn.subsingleton]
    exact fun x hx y hy => hx.2.trans hy.2.symm
  · rw [NNReal.coe_one, one_mul, sub_eq_add_neg, variationOnFromTo.eq_neg_swap, neg_neg, add_comm,
      variationOnFromTo.add hf bs as cs, ← variationOnFromTo.eq_neg_swap f]
    rw [←
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn (naturalParameterization f s a) _
        (variationOnFromTo.monotoneOn hf as) bs cs]
    rw [@eVariationOn.eq_of_edist_zero_on _ _ _ _ _ f]
    · rw [variationOnFromTo.eq_of_le _ _ bc, ENNReal.ofReal_toReal (hf b c bs cs)]
    · rintro x ⟨xs, _, _⟩
      exact edist_naturalParameterization_eq_zero hf as xs
