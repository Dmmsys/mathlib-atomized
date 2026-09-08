/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : α → R` is nonarchimedean if it satisfies the strong triangle inequality
`f (a + b) ≤ max (f a) (f b)` for all `a b : α`. This file proves basic properties of
nonarchimedean functions.
-/

public section

/- TODO: Remove the Funlike hypothesis on these statements and turn them all into the form
  {f : α → R} + properties on f. -/

namespace IsNonarchimedean

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

/-- A nonnegative nonarchimedean function satisfies the triangle inequality. -/
/-
**IsNonarchimedean.add_le** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimedean`。
形式化陈述：add_le [IsStrictOrderedRing R] {α : Type*} [Add α] {f : α -> R} (hf : fora
ll x : α, 0 <= f x) (hna : IsNonarchimedean f) {a b : α} : f (a + b) <= f a + f 
b
参数：hf : forall x : α, 0 <= f x；hna : IsNonarchimedean f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `le_add_iff_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a ≤ a + b ↔ 0 
≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `le_add_iff_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddRightMono α] [AddRightReflectLE α] (a : α) {b : α},   a ≤ b + a ↔ 0
 ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …

--- 原说明 ---
A nonnegative nonarchimedean function satisfies the triangle inequality.
-/
theorem add_le [IsStrictOrderedRing R] {α : Type*} [Add α] {f : α → R} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

/-- If `f` is a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, then for every
  `n : ℕ` and `a : α`, we have `f (n • a) ≤ (f a)`. -/
/-
**IsNonarchimedean.nsmul_le** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimedean`。
形式化陈述：nsmul_le {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R] 
[NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : Nat} {a : α} : f 
(n • a) <= f a
参数：hna : IsNonarchimedean f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
If `f` is a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, the
n for every
  `n : ℕ` and `a : α`, we have `f (n • a) ≤ (f a)`.
-/
theorem nsmul_le {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
    apply le_trans <| hna (n • a) (1 • a)
    simpa

/-- If `f` is a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, then for every
  `n : ℕ` and `a : α`, we have `f (n * a) ≤ (f a)`. -/
/-
**IsNonarchimedean.nmul_le** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimedean`。
形式化陈述：nmul_le {F α : Type*} [NonAssocSemiring α] [FunLike F α R] [ZeroHomClass F
 α R] [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : Nat} {a : α
} : f (n * a) <= f a
参数：hna : IsNonarchimedean f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `IsNonarchimedean.nsmul_le`：nsmul_le {F α : Type*} [AddMonoid α] [FunLike
 F α R] [ZeroHomClass F α R] [NonnegHomClass F α R] {f : F} (hna : IsNonarchimed
ean f) {n : Nat…

--- 原说明 ---
If `f` is a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, the
n for every
  `n : ℕ` and `a : α`, we have `f (n * a) ≤ (f a)`.
-/
theorem nmul_le {F α : Type*} [NonAssocSemiring α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna
/-
**IsNonarchimedean.apply_natCast_le_one** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimed
ean`。
形式化陈述：apply_natCast_le_one {F α : Type*} [AddMonoidWithOne α] [FunLike F α R] [Z
eroHomClass F α R] [NonnegHomClass F α R] [OneHomClass F α R] {f : F} (hna : IsN
onarchimedean f) {n : Nat} : f n <= 1
参数：hna : IsNonarchimedean f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `IsNonarchimedean.nsmul_le`：nsmul_le {F α : Type*} [AddMonoid α] [FunLike
 F α R] [ZeroHomClass F α R] [NonnegHomClass F α R] {f : F} (hna : IsNonarchimed
ean f) {n : Nat…
-/
lemma apply_natCast_le_one {F α : Type*} [AddMonoidWithOne α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℕ} : f n ≤ 1 := by
  rw [← nsmul_one n, ← map_one f]
  exact nsmul_le hna

@[deprecated (since := "2026-04-27")]
alias apply_natCast_le_one_of_isNonarchimedean := apply_natCast_le_one

/-- If `f` is a nonarchimedean additive group seminorm on `α` with `f 1 = 1`, then for every `n : ℤ`
  we have `f n ≤ 1`. -/
/-
**IsNonarchimedean.apply_intCast_le_one** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimed
ean`。
形式化陈述：apply_intCast_le_one [IsStrictOrderedRing R] {F α : Type*} [AddGroupWithOn
e α] [FunLike F α R] [AddGroupSeminormClass F α R] [OneHomClass F α R] {f : F} (
hna : IsNonarchimedean f) {n : Int} : f n <= 1
参数：hna : IsNonarchimedean f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `IsNonarchimedean.apply_natCast_le_one`：apply_natCast_le_one {F α : Type*
} [AddMonoidWithOne α] [FunLike F α R] [ZeroHomClass F α R] [NonnegHomClass F α 
R] [OneHomClass F α R] {f :…
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…

--- 原说明 ---
If `f` is a nonarchimedean additive group seminorm on `α` with `f 1 = 1`, then f
or every `n : ℤ`
  we have `f n ≤ 1`.
-/
theorem apply_intCast_le_one [IsStrictOrderedRing R]
    {F α : Type*} [AddGroupWithOne α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℤ} : f n ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [apply_natCast_le_one hna]

@[deprecated (since := "2026-04-27")]
alias apply_intCast_le_one_of_isNonarchimedean := apply_intCast_le_one

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**IsNonarchimedean.add_eq_right_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedea
n`。
形式化陈述：add_eq_right_of_lt {F α : Type*} [AddGroup α] [FunLike F α R] [AddGroupSem
inormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (h_lt : f x < f y
) : f (x + y) = f y
参数：hna : IsNonarchimedean f；h_lt : f x < f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `max_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a
 < b → max a b = b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
lemma add_eq_right_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f x < f y) : f (x + y) = f y := by
  by_contra! h
  have h1 : f (x + y) ≤ f y := (hna x y).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _   ≤ max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _   < max (f y) (f y) := by
      rw [max_self, map_neg_eq_map]
      exact max_lt h_lt <| lt_of_le_of_ne h1 h
    _   = f y := max_self (f y)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**IsNonarchimedean.add_eq_left_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedean
`。
形式化陈述：add_eq_left_of_lt {F α : Type*} [AddGroup α] [FunLike F α R] [AddGroupSemi
normClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (h_lt : f y < f x)
 : f (x + y) = f x
参数：hna : IsNonarchimedean f；h_lt : f y < f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
lemma add_eq_left_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f y < f x) : f (x + y) = f x := by
  by_contra! h
  have h1 : f (x + y) ≤ f x := (hna x y).trans_eq (max_eq_left_of_lt h_lt)
  apply lt_irrefl (f x)
  calc
    f x = f (x + y + -y) := by simp
    _   ≤ max (f (x + y)) (f (-y)) := hna (x + y) (-y)
    _   < max (f x) (f x) := by
      rw [max_self, map_neg_eq_map]
      apply max_lt (lt_of_le_of_ne h1 h) h_lt
    _   = f x := max_self (f x)

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f x ≠ f y`, then `f (x + y) = max (f x) (f y)`. -/
/-
**IsNonarchimedean.add_eq_max_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimedean`
。
形式化陈述：add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R] [AddGroupSemin
ormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x != f y) 
: f (x + y) = max (f x) (f y)
参数：hna : IsNonarchimedean f；hne : f x != f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsNonarchimedean.add_eq_right_of_lt`：add_eq_right_of_lt {F α : Type*} [A
ddGroup α] [FunLike F α R] [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarc
himedean f) {x y : α} (h_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a
 < b → max a b = b
· 使用引理 `IsNonarchimedean.add_eq_left_of_lt`：add_eq_left_of_lt {F α : Type*} [Add
Group α] [FunLike F α R] [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchi
medean f) {x y : α} (h_l…
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a

--- 原说明 ---
If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such
 that
  `f x ≠ f y`, then `f (x + y) = max (f x) (f y)`.
-/
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [add_eq_right_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [add_eq_left_of_lt hna h_lt]
    exact (max_eq_left_of_lt h_lt).symm

/- TODO: Remove the funlike conditions on the lemmas required for add_max_of_ne, this will allow us
  to remove the CommGroup part in the below which is unnecessary. -/

/-
**IsNonarchimedean.add_eq_max_of_ne'** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedean
`。
形式化陈述：add_eq_max_of_ne' {α S : Type*} [LinearOrder S] [AddCommGroup α] (f : α ->
 S) (fna : IsNonarchimedean f) (Neg : forall a, f a = f (-a)) {a b : α} (hne : f
 a != f b) : f (a + b) = max (f a) (f b)
参数：f : α -> S；fna : IsNonarchimedean f；Neg : forall a, f a = f (-a)；hne : f a !=
 f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a

--- 原说明 ---
TODO: Remove the funlike conditions on the lemmas required for add_max_of_ne, th
is will allow us
  to remove the CommGroup part in the below which is unnecessary.
-/
lemma add_eq_max_of_ne' {α S : Type*} [LinearOrder S] [AddCommGroup α]
    (f : α → S) (fna : IsNonarchimedean f) (Neg : ∀ a, f a = f (-a)) {a b : α}
    (hne : f a ≠ f b) : f (a + b) = max (f a) (f b) := by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (fna a b)
  rcases le_max_iff.mp (fna (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa [Neg b] using hab))

omit [Semiring R] in
open Finset in
/-- Ultrametric inequality with `Finset.sum`. -/
/-
**IsNonarchimedean.apply_sum_le_sup** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedean`
。
形式化陈述：apply_sum_le_sup {α β : Type*} [AddCommMonoid α] {f : α -> R} (nonarch : I
sNonarchimedean f) {s : Finset β} (hnonempty : s.Nonempty) {l : β -> α} : f (∑ i
 in s, l i) <= s.sup' hnonempty fun i => f (l i)
参数：nonarch : IsNonarchimedean f；hnonempty : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.le_sup'_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder 
α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α},   a ≤ s.sup' H f ↔ ∃ b ∈
 s, a ≤ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c

--- 原说明 ---
Ultrametric inequality with `Finset.sum`.
-/
lemma apply_sum_le_sup {α β : Type*} [AddCommMonoid α] {f : α → R}
    (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempty : s.Nonempty) {l : β → α} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| nonarch (l i) (∑ i ∈ s, l i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

@[deprecated (since := "2026-04-27")]
alias apply_sum_le_sup_of_isNonarchimedean := apply_sum_le_sup

omit [Semiring R] in
/-- Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty multiset
  `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)` . -/
/-
**IsNonarchimedean.multiset_image_add_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `IsN
onarchimedean`。
形式化陈述：multiset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β
] {f : α -> R} (hna : IsNonarchimedean f) (g : β -> α) {s : Multiset β} (hs : s 
!= 0) : exists b : β, (b in s) ∧ f (Multiset.map g s).sum <= f (g b)
参数：hna : IsNonarchimedean f；g : β -> α；hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c

--- 原说明 ---
Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty m
ultiset
  `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)` .
-/
theorem multiset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α → R}
    (hna : IsNonarchimedean f) (g : β → α) {s : Multiset β} (hs : s ≠ 0) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
      rcases le_max_iff.mp <| hna (g a) (Multiset.map g s).sum with h4 | h4
      · exact .inl h4
      · exact .inr ⟨w, h2, le_trans h4 h3⟩

omit [Semiring R] in
/-- Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty finset
  `t : Finset β`, we can always find `b : β` belonging to `t` such that `f (t.sum g) ≤ f (g b)` . -/
/-
**IsNonarchimedean.finset_image_add_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `IsNon
archimedean`。
形式化陈述：finset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] {f : α -> R} 
(hna : IsNonarchimedean f) (g : β -> α) {t : Finset β} (ht : t.Nonempty) : exist
s b in t, f (t.sum g) <= f (g b)
参数：hna : IsNonarchimedean f；g : β -> α；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `IsNonarchimedean.apply_sum_le_sup`：apply_sum_le_sup {α β : Type*} [AddCo
mmMonoid α] {f : α -> R} (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempt
y : s.Nonempty) {l : β …

--- 原说明 ---
Given a nonarchimedean function `α → R`, a function `g : β → α` and a nonempty f
inset
  `t : Finset β`, we can always find `b : β` belonging to `t` such that `f (t.su
m g) ≤ f (g b)` .
-/
theorem finset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] {f : α → R}
    (hna : IsNonarchimedean f) (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b ∈ t, f (t.sum g) ≤ f (g b) := by
  simpa [Finset.le_sup'_iff] using IsNonarchimedean.apply_sum_le_sup hna ht

/-- Given a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, a function `g : β → α`
  and a multiset `s : Multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty,
  such that `f (s.sum g) ≤ f (g b)` . -/
/-
**IsNonarchimedean.multiset_image_add** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimedea
n`。
形式化陈述：multiset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R] [Zero
HomClass F α R] [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimed
ean f) (g : β -> α) (s : Multiset β) : exists b : β, (s != 0 -> b in s) ∧ f (Mul
tiset.map g s).sum <= f (g b)
参数：hna : IsNonarchimedean f；g : β -> α；s : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsNonarchimedean.multiset_image_add_of_nonempty`：multiset_image_add_of_n
onempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α -> R} (hna : IsNonar
chimedean f) (g : β -> α) {s : Multis…
· 使用定理 `Multiset.cons_ne_zero`：cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m !
= 0

--- 原说明 ---
Given a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, a funct
ion `g : β → α`
  and a multiset `s : Multiset β`, we can always find `b : β`, belonging to `s` 
if `s` is nonempty,
  such that `f (s.sum g) ≤ f (g b)` .
-/
theorem multiset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f) (g : β → α)
    (s : Multiset β) : ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := multiset_image_add_of_nonempty (s := a ::ₘ s)
      hna g Multiset.cons_ne_zero
    exact ⟨b, fun _ ↦ hb1, hb2⟩

/-- Given a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, a function `g : β → α`
  and a finset `t : Finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` . -/
/-
**IsNonarchimedean.finset_image_add** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedean`
。
形式化陈述：finset_image_add {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α -> R}
 (f_zero : f 0 = 0) (f_nonneg : forall x, 0 <= f x) (hna : IsNonarchimedean f) (
g : β -> α) (t : Finset β) : exists i, (t.Nonempty -> i in t) ∧ f (t.sum g) <= f
 (g i)
参数：f_zero : f 0 = 0；f_nonneg : forall x, 0 <= f x；hna : IsNonarchimedean f；g : β
 -> α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsNonarchimedean.finset_image_add_of_nonempty`：finset_image_add_of_nonem
pty {α β : Type*} [AddCommMonoid α] {f : α -> R} (hna : IsNonarchimedean f) (g :
 β -> α) {t : Finset β} (ht : t.Non…

--- 原说明 ---
Given a nonnegative nonarchimedean function `α → R` such that `f 0 = 0`, a funct
ion `g : β → α`
  and a finset `t : Finset β`, we can always find `b : β`, belonging to `t` if `
t` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` .
-/
lemma finset_image_add {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α → R} (f_zero : f 0 = 0)
    (f_nonneg : ∀ x, 0 ≤ f x) (hna : IsNonarchimedean f) (g : β → α) (t : Finset β) :
    ∃ i, (t.Nonempty → i ∈ t) ∧ f (t.sum g) ≤ f (g i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [f_zero, f_nonneg]
  · exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <|
      IsNonarchimedean.finset_image_add_of_nonempty hna g ht

open Multiset in
/-
**IsNonarchimedean.multiset_powerset_image_add** 是 Mathlib 中的一个定理，位于命名空间 `IsNona
rchimedean`。
形式化陈述：multiset_powerset_image_add [IsStrictOrderedRing R] {F α : Type*} [CommRin
g α] [FunLike F α R] [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchime
dean f) (s : Multiset α) (m : Nat) : exists t : Multiset α, card t = card s - m 
∧ (forall x : α, x in t -> x in s) ∧ f (map prod (powersetCard (card s - m) s)).
sum <= f t.prod
参数：hf_na : IsNonarchimedean f；s : Multiset α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNonarchimedean.multiset_image_add`：multiset_image_add {F α β : Type*} 
[AddCommMonoid α] [FunLike F α R] [ZeroHomClass F α R] [NonnegHomClass F α R] [N
onempty β] {f : F} (hna :…
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.mem_powersetCard`：mem_powersetCard {n : Nat} {s t : Multiset α}
 : s in powersetCard n t ↔ s <= t ∧ card s = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_pos`：card_pos {s : Multiset α} : 0 < card s ↔ s != 0
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Multiset.card_powersetCard`：card_powersetCard (n : Nat) (s : Multiset α)
 : card (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem multiset_powerset_image_add [IsStrictOrderedRing R]
    {F α : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Multiset α) (m : ℕ) :
    ∃ t : Multiset α, card t = card s - m ∧ (∀ x : α, x ∈ t → x ∈ s) ∧
      f (map prod (powersetCard (card s - m) s)).sum ≤ f t.prod := by
  set g := fun t : Multiset α ↦ t.prod
  obtain ⟨b, hb_in, hb_le⟩ := hf_na.multiset_image_add g (powersetCard (card s - m) s)
  have hb : b ≤ s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    exact hb_in (card_pos.mp
      (card_powersetCard (s.card - m) s ▸ Nat.choose_pos ((card s).sub_le m)))
  exact ⟨b, hb.2, fun x hx ↦ mem_of_le hb.left hx, hb_le⟩

open Finset in
/-
**IsNonarchimedean.finset_powerset_image_add** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarc
himedean`。
形式化陈述：finset_powerset_image_add [IsStrictOrderedRing R] {F α β : Type*} [CommRin
g α] [FunLike F α R] [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchime
dean f) (s : Finset β) (b : β -> α) (m : Nat) : exists u : powersetCard (s.card 
- m) s, f ((powersetCard (s.card - m) s).sum fun t : Finset β => t.prod fun i : 
β => -b i) <= f (u.val.prod fun i : β => -b i)
参数：hf_na : IsNonarchimedean f；s : Finset β；b : β -> α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsNonarchimedean.finset_image_add`：finset_image_add {α β : Type*} [AddCo
mmMonoid α] [Nonempty β] {f : α -> R} (f_zero : f 0 = 0) (f_nonneg : forall x, 0
 <= f x) (hna : IsNonar…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.powersetCard_nonempty`：powersetCard_nonempty : (powersetCard n s)
.Nonempty ↔ n <= s.card
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
-/
theorem finset_powerset_image_add [IsStrictOrderedRing R]
    {F α β : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Finset β)
    (b : β → α) (m : ℕ) :
    ∃ u : powersetCard (s.card - m) s,
      f ((powersetCard (s.card - m) s).sum fun t : Finset β ↦
        t.prod fun i : β ↦ -b i) ≤ f (u.val.prod fun i : β ↦ -b i) := by
  set g := fun t : Finset β ↦ t.prod fun i : β ↦ - b i
  obtain ⟨b, hb_in, hb⟩ := hf_na.finset_image_add (by grind) (apply_nonneg f)
    g (powersetCard (s.card - m) s)
  exact ⟨⟨b, hb_in (powersetCard_nonempty.mpr (Nat.sub_le s.card m))⟩, hb⟩

omit [Semiring R] in
/-
**IsNonarchimedean.apply_sum_eq_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedea
n`。
形式化陈述：apply_sum_eq_of_lt {α β : Type*} [AddCommGroup α] {f : α -> R} (fna : IsNo
narchimedean f) (f_neg : forall a, f a = f (-a)) {s : Finset β} {l : β -> α} {k 
: β} (hk : k in s) (hmax : forall j in s, j != k -> f (l j) < f (l k)) : f (∑ i 
in s, l i) = f (l k)
参数：fna : IsNonarchimedean f；f_neg : forall a, f a = f (-a)；hk : k in s；hmax : fo
rall j in s, j != k -> f (l j) < f (l k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Finset.Nontrivial.erase_nonempty`：∀ {α : Type u_1} [inst : DecidableEq α
] {s : Finset α} {a : α}, s.Nontrivial → (s.erase a).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < #s ↔
 s.Nontrivial
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `IsNonarchimedean.apply_sum_le_sup`：apply_sum_le_sup {α β : Type*} [AddCo
mmMonoid α] {f : α -> R} (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempt
y : s.Nonempty) {l : β …
· 使用引理 `IsNonarchimedean.add_eq_max_of_ne'`：add_eq_max_of_ne' {α S : Type*} [Lin
earOrder S] [AddCommGroup α] (f : α -> S) (fna : IsNonarchimedean f) (Neg : fora
ll a, f a = f (-a)) {a b…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma apply_sum_eq_of_lt {α β : Type*} [AddCommGroup α] {f : α → R} (fna : IsNonarchimedean f)
    (f_neg : ∀ a, f a = f (-a)) {s : Finset β} {l : β → α} {k : β} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≠ k → f (l j) < f (l k)) : f (∑ i ∈ s, l i) = f (l k) := by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := IsNonarchimedean.apply_sum_le_sup fna hNonempty (l := l)
    simp only [Finset.le_sup'_iff, Finset.mem_erase, ne_eq] at hrest_le
    rw [add_eq_max_of_ne' f fna f_neg (by grind), max_eq_left (le_of_lt (by grind))]

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
/-
**IsNonarchimedean.add_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `IsNonarchimedean`。
形式化陈述：add_pow_le {F α : Type*} [CommRing α] [FunLike F α R] [ZeroHomClass F α R]
 [NonnegHomClass F α R] [SubmultiplicativeHomClass F α R] {f : F} (hna : IsNonar
chimedean f) (n : Nat) (a b : α) : exists m < n + 1, f ((a + b) ^ n) <= f (a ^ m
) * f (b ^ (n - m))
参数：hna : IsNonarchimedean f；n : Nat；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsNonarchimedean.finset_image_add`：finset_image_add {α β : Type*} [AddCo
mmMonoid α] [Nonempty β] {f : α -> R} (f_zero : f 0 = 0) (f_nonneg : forall x, 0
 <= f x) (hna : IsNonar…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsNonarchimedean.nmul_le`：nmul_le {F α : Type*} [NonAssocSemiring α] [Fu
nLike F α R] [ZeroHomClass F α R] [NonnegHomClass F α R] {f : F} (hna : IsNonarc
himedean f) {n…
· 使用定理 `SubmultiplicativeHomClass.map_mul_le_mul`：∀ {F : Type u_7} {α : outParam
 (Type u_8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Mul β} {inst_2 :
 LE β}   {inst_3 : FunLike F α…

--- 原说明 ---
If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n
 : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`.
-/
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [SubmultiplicativeHomClass F α R] {f : F} (hna : IsNonarchimedean f)
    (n : ℕ) (a b : α) : ∃ m < n + 1, f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add (by aesop) (by aesop) hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (nmul_le hna) (map_mul_le_mul _ _ _))

end IsNonarchimedean

