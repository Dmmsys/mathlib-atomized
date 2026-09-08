/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Dot product of two vectors

This file contains some results on the map `dotProduct`, which maps two
vectors `v w : n → R` to the sum of the entrywise products `v i * w i`.

## Main results

* `dotProduct_stdBasis_one`: the dot product of `v` with the `i`th
  standard basis vector is `v i`
* `dotProduct_eq_zero_iff`: if `v`'s dot product with all `w` is zero,
  then `v` is zero

## Tags

matrix

-/

public section


variable {m n p R : Type*}

section Semiring

variable [Semiring R] [Fintype n]

/-
**dotProduct_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_eq (v w : n -> R) (h : forall u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w
参数：v w : n -> R；h : forall u, v ⬝ᵥ u = w ⬝ᵥ u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dotProduct_single_one`：dotProduct_single_one [DecidableEq n] (v : n -> α
) (i : n) : v ⬝ᵥ Pi.single i 1 = v i
-/
theorem dotProduct_eq (v w : n → R) (h : ∀ u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w := by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]
/-
**dotProduct_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_eq_iff {v w : n -> R} : (forall u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_eq`：dotProduct_eq (v w : n -> R) (h : forall u, v ⬝ᵥ u = w ⬝ᵥ
 u) : v = w
-/
theorem dotProduct_eq_iff {v w : n → R} : (∀ u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w :=
  ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩
/-
**dotProduct_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_eq_zero (v : n -> R) (h : forall w, v ⬝ᵥ w = 0) : v = 0
参数：v : n -> R；h : forall w, v ⬝ᵥ w = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_eq`：dotProduct_eq (v w : n -> R) (h : forall u, v ⬝ᵥ u = w ⬝ᵥ
 u) : v = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
-/
theorem dotProduct_eq_zero (v : n → R) (h : ∀ w, v ⬝ᵥ w = 0) : v = 0 :=
  dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm
/-
**dotProduct_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_eq_zero_iff {v : n -> R} : (forall w, v ⬝ᵥ w = 0) ↔ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_eq_zero`：dotProduct_eq_zero (v : n -> R) (h : forall w, v ⬝ᵥ 
w = 0) : v = 0
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dotProduct_eq_zero_iff {v : n → R} : (∀ w, v ⬝ᵥ w = 0) ↔ v = 0 :=
  ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

end Semiring

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n]

/-
**dotProduct_nonneg_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dotProduct_nonneg_of_nonneg {v w : n -> R} (hv : 0 <= v) (hw : 0 <= w) : 0
 <= v ⬝ᵥ w
参数：hv : 0 <= v；hw : 0 <= w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma dotProduct_nonneg_of_nonneg {v w : n → R} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))
/-
**dotProduct_le_dotProduct_of_nonneg_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dotProduct_le_dotProduct_of_nonneg_right {u v w : n -> R} (huv : u <= v) (
hw : 0 <= w) : u ⬝ᵥ w <= v ⬝ᵥ w
参数：huv : u <= v；hw : 0 <= w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
-/
lemma dotProduct_le_dotProduct_of_nonneg_right {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w := by
  unfold dotProduct; gcongr <;> apply_rules
/-
**dotProduct_le_dotProduct_of_nonneg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dotProduct_le_dotProduct_of_nonneg_left {u v w : n -> R} (huv : u <= v) (h
w : 0 <= w) : w ⬝ᵥ u <= w ⬝ᵥ v
参数：huv : u <= v；hw : 0 <= w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma dotProduct_le_dotProduct_of_nonneg_left {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    w ⬝ᵥ u ≤ w ⬝ᵥ v := by
  unfold dotProduct; gcongr <;> apply_rules

end OrderedSemiring

section Self

variable [Fintype m] [Fintype n] [Fintype p]

@[simp]
/-
**dotProduct_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_self_eq_zero [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {
v : n -> R} : v ⬝ᵥ v = 0 ↔ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dotProduct_self_eq_zero [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {v : n → R} :
    v ⬝ᵥ v = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans <| by
    simp [funext_iff]

section StarOrderedRing

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/-
**dotProduct_star_self_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_star_self_nonneg (v : n -> R) : 0 <= star v ⬝ᵥ v
参数：v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_nonneg`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Preorder M] [AddLeftMono M]   {f : ι → M}, 0
 ≤ f → 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r

--- 原说明 ---
Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`.
-/
theorem dotProduct_star_self_nonneg (v : n → R) : 0 ≤ star v ⬝ᵥ v :=
  Fintype.sum_nonneg fun _ => star_mul_self_nonneg _

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/-
**dotProduct_self_star_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_self_star_nonneg (v : n -> R) : 0 <= v ⬝ᵥ star v
参数：v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_nonneg`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Preorder M] [AddLeftMono M]   {f : ι → M}, 0
 ≤ f → 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `mul_star_self_nonneg`：mul_star_self_nonneg (r : R) : 0 <= r * star r

--- 原说明 ---
Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`.
-/
theorem dotProduct_self_star_nonneg (v : n → R) : 0 ≤ v ⬝ᵥ star v :=
  Fintype.sum_nonneg fun _ => mul_star_self_nonneg _

variable [NoZeroDivisors R]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/-
**dotProduct_star_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_star_self_eq_zero {v : n -> R} : star v ⬝ᵥ v = 0 ↔ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fintype.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_9} {M : Type u_10} [ins
t : Fintype ι] [inst_1 : AddCommMonoid M] [inst_2 : PartialOrder M] [AddLeftMono
 M]   {f : ι → M}, 0 ≤ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`.
-/
theorem dotProduct_star_self_eq_zero {v : n → R} : star v ⬝ᵥ v = 0 ↔ v = 0 :=
  (Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans <|
    by simp [funext_iff, mul_eq_zero]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/-
**dotProduct_self_star_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_self_star_eq_zero {v : n -> R} : v ⬝ᵥ star v = 0 ↔ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fintype.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_9} {M : Type u_10} [ins
t : Fintype ι] [inst_1 : AddCommMonoid M] [inst_2 : PartialOrder M] [AddLeftMono
 M]   {f : ι → M}, 0 ≤ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `mul_star_self_nonneg`：mul_star_self_nonneg (r : R) : 0 <= r * star r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`.
-/
theorem dotProduct_self_star_eq_zero {v : n → R} : v ⬝ᵥ star v = 0 ↔ v = 0 :=
  (Fintype.sum_eq_zero_iff_of_nonneg fun _ => mul_star_self_nonneg _).trans <|
    by simp [funext_iff, mul_eq_zero]

namespace Matrix

@[simp]
/-
**Matrix.conjTranspose_mul_self_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_mul_self_eq_zero {n} {A : Matrix m n R} : Aᴴ * A = 0 ↔ A = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dotProduct_star_self_eq_zero`：dotProduct_star_self_eq_zero {v : n -> R} 
: star v ⬝ᵥ v = 0 ↔ v = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma conjTranspose_mul_self_eq_zero {n} {A : Matrix m n R} : Aᴴ * A = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_star_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
  fun h => h ▸ Matrix.mul_zero _⟩

@[simp]
/-
**Matrix.self_mul_conjTranspose_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：self_mul_conjTranspose_eq_zero {m} {A : Matrix m n R} : A * Aᴴ = 0 ↔ A = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dotProduct_self_star_eq_zero`：dotProduct_self_star_eq_zero {v : n -> R} 
: v ⬝ᵥ star v = 0 ↔ v = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma self_mul_conjTranspose_eq_zero {m} {A : Matrix m n R} : A * Aᴴ = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩
/-
**Matrix.conjTranspose_mul_self_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_mul_self_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix n p 
R) : (Aᴴ * A) * B = 0 ↔ A * B = 0
参数：A : Matrix m n R；B : Matrix n p R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.conjTranspose_mul_self_eq_zero`：conjTranspose_mul_self_eq_zero {n
} {A : Matrix m n R} : Aᴴ * A = 0 ↔ A = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjTranspose_mul_self_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix n p R) :
    (Aᴴ * A) * B = 0 ↔ A * B = 0 := by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  apply_fun (Bᴴ * ·) at h
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    conjTranspose_mul_self_eq_zero] at h
/-
**Matrix.self_mul_conjTranspose_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：self_mul_conjTranspose_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix m p 
R) : (A * Aᴴ) * B = 0 ↔ Aᴴ * B = 0
参数：A : Matrix m n R；B : Matrix m p R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.conjTranspose_mul_self_mul_eq_zero`：conjTranspose_mul_self_mul_eq
_zero {p} (A : Matrix m n R) (B : Matrix n p R) : (Aᴴ * A) * B = 0 ↔ A * B = 0
-/
lemma self_mul_conjTranspose_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix m p R) :
    (A * Aᴴ) * B = 0 ↔ Aᴴ * B = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mul_eq_zero Aᴴ _
/-
**Matrix.mul_self_mul_conjTranspose_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_self_mul_conjTranspose_eq_zero {p} (A : Matrix m n R) (B : Matrix p m 
R) : B * (A * Aᴴ) = 0 ↔ B * A = 0
参数：A : Matrix m n R；B : Matrix p m R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_eq_zero`：conjTranspose_eq_zero [AddMonoid α] [StarA
ddMonoid α] {M : Matrix m n α} : Mᴴ = 0 ↔ M = 0
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.self_mul_conjTranspose_mul_eq_zero`：self_mul_conjTranspose_mul_eq
_zero {p} (A : Matrix m n R) (B : Matrix m p R) : (A * Aᴴ) * B = 0 ↔ Aᴴ * B = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_self_mul_conjTranspose_eq_zero {p} (A : Matrix m n R) (B : Matrix p m R) :
    B * (A * Aᴴ) = 0 ↔ B * A = 0 := by
  rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    self_mul_conjTranspose_mul_eq_zero, ← conjTranspose_mul, conjTranspose_eq_zero]
/-
**Matrix.mul_conjTranspose_mul_self_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_conjTranspose_mul_self_eq_zero {p} (A : Matrix m n R) (B : Matrix p n 
R) : B * (Aᴴ * A) = 0 ↔ B * Aᴴ = 0
参数：A : Matrix m n R；B : Matrix p n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.mul_self_mul_conjTranspose_eq_zero`：mul_self_mul_conjTranspose_eq
_zero {p} (A : Matrix m n R) (B : Matrix p m R) : B * (A * Aᴴ) = 0 ↔ B * A = 0
-/
lemma mul_conjTranspose_mul_self_eq_zero {p} (A : Matrix m n R) (B : Matrix p n R) :
    B * (Aᴴ * A) = 0 ↔ B * Aᴴ = 0 := by
  simpa only [conjTranspose_conjTranspose] using mul_self_mul_conjTranspose_eq_zero Aᴴ _
/-
**Matrix.conjTranspose_mul_self_mulVec_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
`。
形式化陈述：conjTranspose_mul_self_mulVec_eq_zero (A : Matrix m n R) (v : n -> R) : (A
ᴴ * A) *ᵥ v = 0 ↔ A *ᵥ v = 0
参数：A : Matrix m n R；v : n -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.conjTranspose_mul_self_mul_eq_zero`：conjTranspose_mul_self_mul_eq
_zero {p} (A : Matrix m n R) (B : Matrix n p R) : (Aᴴ * A) * B = 0 ↔ A * B = 0
-/
lemma conjTranspose_mul_self_mulVec_eq_zero (A : Matrix m n R) (v : n → R) :
    (Aᴴ * A) *ᵥ v = 0 ↔ A *ᵥ v = 0 := by
  simpa only [← Matrix.replicateCol_mulVec, replicateCol_eq_zero] using
    conjTranspose_mul_self_mul_eq_zero A (replicateCol (Fin 1) v)
/-
**Matrix.self_mul_conjTranspose_mulVec_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
`。
形式化陈述：self_mul_conjTranspose_mulVec_eq_zero (A : Matrix m n R) (v : m -> R) : (A
 * Aᴴ) *ᵥ v = 0 ↔ Aᴴ *ᵥ v = 0
参数：A : Matrix m n R；v : m -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.conjTranspose_mul_self_mulVec_eq_zero`：conjTranspose_mul_self_mul
Vec_eq_zero (A : Matrix m n R) (v : n -> R) : (Aᴴ * A) *ᵥ v = 0 ↔ A *ᵥ v = 0
-/
lemma self_mul_conjTranspose_mulVec_eq_zero (A : Matrix m n R) (v : m → R) :
    (A * Aᴴ) *ᵥ v = 0 ↔ Aᴴ *ᵥ v = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mulVec_eq_zero Aᴴ _
/-
**Matrix.vecMul_conjTranspose_mul_self_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
`。
形式化陈述：vecMul_conjTranspose_mul_self_eq_zero (A : Matrix m n R) (v : n -> R) : v 
ᵥ* (Aᴴ * A) = 0 ↔ v ᵥ* Aᴴ = 0
参数：A : Matrix m n R；v : n -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.mul_conjTranspose_mul_self_eq_zero`：mul_conjTranspose_mul_self_eq
_zero {p} (A : Matrix m n R) (B : Matrix p n R) : B * (Aᴴ * A) = 0 ↔ B * Aᴴ = 0
-/
lemma vecMul_conjTranspose_mul_self_eq_zero (A : Matrix m n R) (v : n → R) :
    v ᵥ* (Aᴴ * A) = 0 ↔ v ᵥ* Aᴴ = 0 := by
  simpa only [← Matrix.replicateRow_vecMul, replicateRow_eq_zero] using
    mul_conjTranspose_mul_self_eq_zero A (replicateRow (Fin 1) v)
/-
**Matrix.vecMul_self_mul_conjTranspose_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
`。
形式化陈述：vecMul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (v : m -> R) : v 
ᵥ* (A * Aᴴ) = 0 ↔ v ᵥ* A = 0
参数：A : Matrix m n R；v : m -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.vecMul_conjTranspose_mul_self_eq_zero`：vecMul_conjTranspose_mul_s
elf_eq_zero (A : Matrix m n R) (v : n -> R) : v ᵥ* (Aᴴ * A) = 0 ↔ v ᵥ* Aᴴ = 0
-/
lemma vecMul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (v : m → R) :
    v ᵥ* (A * Aᴴ) = 0 ↔ v ᵥ* A = 0 := by
  simpa only [conjTranspose_conjTranspose] using vecMul_conjTranspose_mul_self_eq_zero Aᴴ _

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/-
**Matrix.dotProduct_star_self_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_star_self_pos_iff {v : n -> R} : 0 < star v ⬝ᵥ v ↔ v != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fintype.sum_pos_iff_of_nonneg`：∀ {ι : Type u_1} {M : Type u_4} [inst : F
intype ι] [inst_1 : AddCommMonoid M] [inst_2 : PartialOrder M]   [IsOrderedCance
lAddMonoid M] {f : …
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `star_mul_self_pos`：star_mul_self_pos [Nontrivial R] {x : R} (hx : IsRegu
lar x) : 0 < star x * x
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R

--- 原说明 ---
Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`.
-/
theorem dotProduct_star_self_pos_iff {v : n → R} :
    0 < star v ⬝ᵥ v ↔ v ≠ 0 := by
  nontriviality R
  refine (Fintype.sum_pos_iff_of_nonneg fun i => star_mul_self_nonneg _).trans ?_
  simp_rw [Pi.lt_def, Function.ne_iff, Pi.zero_apply]
  refine (and_iff_right fun i => star_mul_self_nonneg (v i)).trans <| exists_congr fun i => ?_
  constructor
  · rintro h hv
    simp [hv] at h
  · exact (star_mul_self_pos <| .of_ne_zero ·)

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/-
**Matrix.dotProduct_self_star_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_self_star_pos_iff {v : n -> R} : 0 < dotProduct v (star v) ↔ v 
!= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Matrix.dotProduct_star_self_pos_iff`：dotProduct_star_self_pos_iff {v : n
 -> R} : 0 < star v ⬝ᵥ v ↔ v != 0

--- 原说明 ---
Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`.
-/
theorem dotProduct_self_star_pos_iff {v : n → R} : 0 < dotProduct v (star v) ↔ v ≠ 0 := by
  simpa using dotProduct_star_self_pos_iff (v := star v)

end Matrix

end StarOrderedRing

end Self

