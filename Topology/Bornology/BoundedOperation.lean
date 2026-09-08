/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations.

In particular, when combined with type classes which guarantee continuity of the same operations,
we can equip bounded continuous functions with the corresponding operations.

## Main definitions

* `BoundedAdd R`: a class guaranteeing boundedness of addition.
* `BoundedSub R`: a class guaranteeing boundedness of subtraction.
* `BoundedMul R`: a class guaranteeing boundedness of multiplication.

-/

public section

open scoped NNReal

section bounded_sub
/-!
### Bounded subtraction
-/

open scoped Pointwise

/-- A typeclass saying that `(p : R × R) ↦ p.1 - p.2` maps any product of bounded sets to a bounded
set. This property automatically holds for seminormed additive groups, but it also holds, e.g.,
for `ℝ≥0`. -/
/-
**BoundedSub** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Bornology R] → [Sub R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `(p : R × R) ↦ p.1 - p.2` maps any product of bounded se
ts to a bounded
set. This property automatically holds for seminormed additive groups, but it al
so holds, e.g.,
for `ℝ≥0`.
-/
class BoundedSub (R : Type*) [Bornology R] [Sub R] : Prop where
  isBounded_sub : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s - t)

variable {R : Type*}
/-
**isBounded_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t : Set R} (hs : Bor
nology.IsBounded s) (ht : Bornology.IsBounded t) : Bornology.IsBounded (s - t)
参数：hs : Bornology.IsBounded s；ht : Bornology.IsBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedSub.isBounded_sub`：∀ {R : Type u_1} {inst : Bornology R} {inst_1 
: Sub R} [self : BoundedSub R] {s t : Set R},   Bornology.IsBounded s → Bornolog
y.IsBounded t …
-/
lemma isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s - t) := BoundedSub.isBounded_sub hs ht
/-
**sub_bounded_of_bounded_of_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Sub R
] [BoundedSub R] {f g : X -> R} (f_bdd : exists C, forall x y, dist (f x) (f y) 
<= C) (g_bdd : exists C, forall x y, dist (g x) (g y) <= C) : exists C, forall x
 y, dist ((f - g) x) ((f - g) y) <= C
参数：f_bdd : exists C, forall x y, dist (f x) (f y) <= C；g_bdd : exists C, forall 
x y, dist (g x) (g y) <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用引理 `isBounded_sub`：isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t :
 Set R} (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) : Bornology.Is
Bou…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_range_iff`：isBounded_range_iff {f : β -> α} : IsBounded
 (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
· 使用定理 `Set.sub_mem_sub`：∀ {α : Type u_2} [inst : Sub α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a - b ∈ s - t
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma sub_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f - g) x) ((f - g) y) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <|
    isBounded_sub (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))
/-
**boundedSub_of_lipschitzWith_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：boundedSub_of_lipschitzWith_sub [PseudoMetricSpace R] [Sub R] {K : NNReal}
 (lip : LipschitzWith K (fun (p : R × R) => p.1 - p.2)) : BoundedSub R where isB
ounded_sub {s t} s_bdd t_bdd
参数：lip : LipschitzWith K (fun (p : R × R) => p.1 - p.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.prod`：∀ {α : Type u_1} {β : Type u_2} [inst : Bornol
ogy α] [inst_1 : Bornology β] {s : Set α} {t : Set β},   Bornology.IsBounded s →
 Bornology.IsB…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LipschitzWith.isBounded_image`：isBounded_image (hf : LipschitzWith K f) 
{s : Set α} (hs : IsBounded s) : IsBounded (f '' s)
-/
lemma boundedSub_of_lipschitzWith_sub [PseudoMetricSpace R] [Sub R] {K : NNReal}
    (lip : LipschitzWith K (fun (p : R × R) ↦ p.1 - p.2)) :
    BoundedSub R where
  isBounded_sub {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    convert! lip.isBounded_image bdd
    simp

end bounded_sub

section bounded_mul
/-!
### Bounded multiplication and addition
-/

open scoped Pointwise
open Set

/-- A typeclass saying that `(p : R × R) ↦ p.1 + p.2` maps any product of bounded sets to a bounded
set. This property follows from `LipschitzAdd`, and thus automatically holds, e.g., for seminormed
additive groups. -/
/-
**BoundedAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Bornology R] → [Add R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `(p : R × R) ↦ p.1 + p.2` maps any product of bounded se
ts to a bounded
set. This property follows from `LipschitzAdd`, and thus automatically holds, e.
g., for seminormed
additive groups.
-/
class BoundedAdd (R : Type*) [Bornology R] [Add R] : Prop where
  isBounded_add : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s + t)

/-- A typeclass saying that `(p : R × R) ↦ p.1 * p.2` maps any product of bounded sets to a bounded
set. This property automatically holds for non-unital seminormed rings, but it also holds, e.g.,
for `ℝ≥0`. -/
@[to_additive]
/-
**BoundedMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Bornology R] → [Mul R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass saying that `(p : R × R) ↦ p.1 * p.2` maps any product of bounded se
ts to a bounded
set. This property automatically holds for non-unital seminormed rings, but it a
lso holds, e.g.,
for `ℝ≥0`.
-/
class BoundedMul (R : Type*) [Bornology R] [Mul R] : Prop where
  isBounded_mul : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s * t)

variable {R : Type*}

@[to_additive]
/-
**isBounded_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t : Set R} (hs : Bor
nology.IsBounded s) (ht : Bornology.IsBounded t) : Bornology.IsBounded (s * t)
参数：hs : Bornology.IsBounded s；ht : Bornology.IsBounded t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedMul.isBounded_mul`：∀ {R : Type u_1} {inst : Bornology R} {inst_1 
: Mul R} [self : BoundedMul R] {s t : Set R},   Bornology.IsBounded s → Bornolog
y.IsBounded t …
-/
lemma isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s * t) := BoundedMul.isBounded_mul hs ht

@[to_additive]
/-
**isBounded_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBounded_pow {R : Type*} [Bornology R] [Monoid R] [BoundedMul R] {s : Set
 R} (s_bdd : Bornology.IsBounded s) (n : Nat) : Bornology.IsBounded ((fun x => x
 ^ n) '' s)
参数：s_bdd : Bornology.IsBounded s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用引理 `isBounded_mul`：isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t :
 Set R} (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) : Bornology.Is
Bou…
-/
lemma isBounded_pow {R : Type*} [Bornology R] [Monoid R] [BoundedMul R] {s : Set R}
    (s_bdd : Bornology.IsBounded s) (n : ℕ) :
    Bornology.IsBounded ((fun x ↦ x ^ n) '' s) := by
  induction n with
  | zero =>
    by_cases s_empty : s = ∅
    · simp [s_empty]
    simp_rw [← nonempty_iff_ne_empty] at s_empty
    simp [s_empty]
  | succ n hn =>
    have obs : ((fun x ↦ x ^ (n + 1)) '' s) ⊆ ((fun x ↦ x ^ n) '' s) * s := by
      intro x hx
      simp only [mem_image] at hx
      obtain ⟨y, y_in_s, ypow_eq_x⟩ := hx
      rw [← ypow_eq_x, pow_succ y n]
      apply Set.mul_mem_mul _ y_in_s
      use y
    exact (isBounded_mul hn s_bdd).subset obs

@[to_additive]
/-
**mul_bounded_of_bounded_of_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Mul R
] [BoundedMul R] {f g : X -> R} (f_bdd : exists C, forall x y, dist (f x) (f y) 
<= C) (g_bdd : exists C, forall x y, dist (g x) (g y) <= C) : exists C, forall x
 y, dist ((f * g) x) ((f * g) y) <= C
参数：f_bdd : exists C, forall x y, dist (f x) (f y) <= C；g_bdd : exists C, forall 
x y, dist (g x) (g y) <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用引理 `isBounded_mul`：isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t :
 Set R} (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) : Bornology.Is
Bou…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_range_iff`：isBounded_range_iff {f : β -> α} : IsBounded
 (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma mul_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Mul R] [BoundedMul R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f * g) x) ((f * g) y) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <|
    isBounded_mul (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.mul_mem_mul (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.mul_mem_mul (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoMetricSpace R] [Monoid R] [LipschitzMul R] : BoundedMul R where
  isBounded_mul {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    obtain ⟨C, mul_lip⟩ := ‹LipschitzMul R›.lipschitz_mul
    convert! mul_lip.isBounded_image bdd
    ext p
    simp only [Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro ⟨a, a_in_s, b, b_in_t, eq_p⟩
      exact ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
    · intro ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
      simpa [← eq_p] using Set.mul_mem_mul a_in_s b_in_t

end bounded_mul

section SeminormedAddCommGroup
/-!
### Bounded operations in seminormed additive commutative groups
-/

variable {R : Type*} [SeminormedAddCommGroup R]

/-
**SeminormedAddCommGroup.lipschitzWith_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SeminormedAddCommGroup.lipschitzWith_sub : LipschitzWith 2 (fun (p : R × R
) => p.1 - p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LipschitzWith.sub`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] [inst_1 : PseudoEMetricSpace α] {Kf Kg : NNReal}   {f g : α → E}, L
ipschit…
· 使用定理 `LipschitzWith.prod_fst`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.fst
· 使用定理 `LipschitzWith.prod_snd`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.snd
-/
lemma SeminormedAddCommGroup.lipschitzWith_sub :
    LipschitzWith 2 (fun (p : R × R) ↦ p.1 - p.2) := by
  convert! LipschitzWith.prod_fst.sub LipschitzWith.prod_snd
  norm_num
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedSub R := boundedSub_of_lipschitzWith_sub SeminormedAddCommGroup.lipschitzWith_sub

open Filter Pointwise Bornology

/-
TODO:
* Generalize the following to bornologies and `BoundedFoo` classes.
* Add `BoundedNeg`, `BoundedInv` and `BoundedDiv` in the process.
-/

@[simp]
/-
**tendsto_add_const_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_add_const_cobounded (x : R) : Tendsto (· + x) (cobounded R) (cobou
nded R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isCobounded_def`：isCobounded_def {s : Set α} : IsCobounded s ↔
 s in cobounded α
· 使用定理 `Bornology.isBounded_compl_iff`：isBounded_compl_iff : IsBounded sᶜ ↔ IsCo
bounded s
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sub_singleton`：∀ {α : Type u_2} [inst : Sub α] {s : Set α} {b : α}, 
s - {b} = (fun x => x - b) '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `isBounded_sub`：isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t :
 Set R} (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) : Bornology.Is
Bou…
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `Bornology.isBounded_singleton`：isBounded_singleton : IsBounded ({x} : Se
t α)

--- 原说明 ---
TODO:
* Generalize the following to bornologies and `BoundedFoo` classes.
* Add `BoundedNeg`, `BoundedInv` and `BoundedDiv` in the process.
-/
lemma tendsto_add_const_cobounded (x : R) :
    Tendsto (· + x) (cobounded R) (cobounded R) := by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def, ← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_sub hs (t := { x }) isBounded_singleton using 1
  ext y
  simp [sub_eq_iff_eq_add]

@[simp]
/-
**tendsto_const_add_cobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_const_add_cobounded (x : R) : Tendsto (x + ·) (cobounded R) (cobou
nded R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isCobounded_def`：isCobounded_def {s : Set α} : IsCobounded s ↔
 s in cobounded α
· 使用定理 `Bornology.isBounded_compl_iff`：isBounded_compl_iff : IsBounded sᶜ ↔ IsCo
bounded s
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `isBounded_add`：∀ {R : Type u_1} [inst : Bornology R] [inst_1 : Add R] [B
oundedAdd R] {s t : Set R},   Bornology.IsBounded s → Bornology.IsBounded t → Bo
rno…
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `Bornology.isBounded_singleton`：isBounded_singleton : IsBounded ({x} : Se
t α)
-/
lemma tendsto_const_add_cobounded (x : R) :
    Tendsto (x + ·) (cobounded R) (cobounded R) := by
  intro s hs
  rw [mem_map]
  rw [← isCobounded_def, ← isBounded_compl_iff] at hs ⊢
  rw [← Set.preimage_compl]
  convert! isBounded_add isBounded_singleton (s := {-x}) hs using 1
  ext y
  simp

@[simp]
/-
**tendsto_sub_const_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_sub_const_cobounded (x : R) : Tendsto (· - x) (cobounded R) (cobou
nded R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `tendsto_add_const_cobounded`：tendsto_add_const_cobounded (x : R) : Tends
to (· + x) (cobounded R) (cobounded R)
-/
theorem tendsto_sub_const_cobounded (x : R) :
    Tendsto (· - x) (cobounded R) (cobounded R) := by
  simpa only [sub_eq_add_neg] using tendsto_add_const_cobounded (-x)

@[simp]
/-
**tendsto_const_sub_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_sub_cobounded (x : R) : Tendsto (x - ·) (cobounded R) (cobou
nded R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_const_add_cobounded`：tendsto_const_add_cobounded (x : R) : Tends
to (x + ·) (cobounded R) (cobounded R)
· 使用定理 `Filter.tendsto_neg_cobounded`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto Neg.neg (Bornology.cobounded E) (Bornology.cobounded E)
-/
theorem tendsto_const_sub_cobounded (x : R) :
    Tendsto (x - ·) (cobounded R) (cobounded R) := by
  simpa only [sub_eq_add_neg] using! (tendsto_const_add_cobounded x).comp tendsto_neg_cobounded

end SeminormedAddCommGroup

section NonUnitalSeminormedRing
/-!
### Bounded operations in non-unital seminormed rings
-/

variable {R : Type*} [NonUnitalSeminormedRing R]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedMul R where
  isBounded_mul {s t} hs ht := by
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := Set.mem_mul.mp hw
    rw [← w_eq, ← z_eq, dist_eq_norm]
    have hAf' : 0 ≤ Af := Metric.nonempty_closedBall.mp ⟨_, hAf hx₁⟩
    have aux : ∀ {x y}, x ∈ s → y ∈ t → ‖x * y‖ ≤ Af * Ag := by
      intro x y x_in_s y_in_t
      apply (norm_mul_le _ _).trans (mul_le_mul _ _ (norm_nonneg _) hAf')
      · exact mem_closedBall_zero_iff.mp (hAf x_in_s)
      · exact mem_closedBall_zero_iff.mp (hAg y_in_t)
    calc ‖x₁ * y₁ - x₂ * y₂‖
     _ ≤ ‖x₁ * y₁‖ + ‖x₂ * y₂‖ := norm_sub_le _ _
     _ ≤ Af * Ag + Af * Ag     := add_le_add (aux hx₁ hy₁) (aux hx₂ hy₂)
     _ = 2 * Af * Ag           := by simp [← two_mul, mul_assoc]

end NonUnitalSeminormedRing

section NNReal
/-!
### Bounded operations in ℝ≥0
-/

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Bounded operations in ℝ≥0
-/
instance : BoundedSub ℝ≥0 := boundedSub_of_lipschitzWith_sub NNReal.lipschitzWith_sub

open Metric in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedMul ℝ≥0 where
  isBounded_mul {s t} hs ht := by
    obtain ⟨Af, hAf⟩ := (isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (isBounded_iff_subset_closedBall 0).mp ht
    have key : IsCompact (closedBall (0 : ℝ≥0) Af ×ˢ closedBall (0 : ℝ≥0) Ag) :=
      IsCompact.prod (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    apply Bornology.IsBounded.subset (key.image continuous_mul).isBounded
    intro _ ⟨x, x_in_s, y, y_in_t, xy_eq⟩
    exact ⟨⟨x, y⟩, by simpa only [Set.mem_prod] using ⟨⟨hAf x_in_s, hAg y_in_t⟩, xy_eq⟩⟩

end NNReal

