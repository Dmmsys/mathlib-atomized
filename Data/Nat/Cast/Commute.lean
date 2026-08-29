/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Ring.Commute

/-!
# Cast of natural numbers: lemmas about `Commute`

-/

public section

variable {α : Type*}

namespace Nat

section AddCommute

variable [AddMonoidWithOne α]

/--
theorem `addCommute_cast` / 定理 `addCommute_cast`

English:
theorem addCommute_cast
  given: (m n : Nat)
  statement: AddCommute (m : α) (n : α)
  proof: by
  rw [addCommute_iff_eq]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [m.add_comm]

中文:
定理 addCommute_cast
  条件: (m n : 自然数)
  结论: AddCommute (m : α) (n : α)
  证明: by
  rw [addCommute_iff_eq]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [m.add_comm]

Depends on / 依赖: Nat.cast_add, addCommute_iff_eq, add_comm, cast_add, m.add_comm
-/
theorem addCommute_cast (m n : Nat) : AddCommute (m : α) (n : α) := by
  rw [addCommute_iff_eq]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [m.add_comm]

/--
theorem `addCommute_cast_one` / 定理 `addCommute_cast_one`

English:
theorem addCommute_cast_one
  given: (n : Nat)
  statement: AddCommute (n : α) 1
  proof: mod_cast addCommute_cast n 1

中文:
定理 addCommute_cast_one
  条件: (n : 自然数)
  结论: AddCommute (n : α) 1
  证明: mod_cast addCommute_cast n 1

Depends on / 依赖: addCommute_cast, mod_cast
-/
theorem addCommute_cast_one (n : Nat) : AddCommute (n : α) 1 :=
  mod_cast addCommute_cast n 1

/--
theorem `cast_add_comm` / 定理 `cast_add_comm`

English:
theorem cast_add_comm
  given: (m n : Nat)
  statement: (m : α) + n = n + m
  proof: addCommute_cast m n

中文:
定理 cast_add_comm
  条件: (m n : 自然数)
  结论: (m : α) + n = n + m
  证明: addCommute_cast m n

Depends on / 依赖: addCommute_cast
-/
theorem cast_add_comm (m n : Nat) : (m : α) + n = n + m :=
  addCommute_cast m n

/--
theorem `cast_add_one_comm` / 定理 `cast_add_one_comm`

English:
theorem cast_add_one_comm
  given: (n : Nat)
  statement: (n : α) + 1 = 1 + n
  proof: addCommute_cast_one n

中文:
定理 cast_add_one_comm
  条件: (n : 自然数)
  结论: (n : α) + 1 = 1 + n
  证明: addCommute_cast_one n

Depends on / 依赖: addCommute_cast_one
-/
theorem cast_add_one_comm (n : Nat) : (n : α) + 1 = 1 + n :=
  addCommute_cast_one n

end AddCommute

section NonAssocSemiring

variable [NonAssocSemiring α]

/--
theorem `cast_commute` / 定理 `cast_commute`

English:
theorem cast_commute
  given: (n : Nat) (x : α)
  statement: Commute (n : α) x
  proof: by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

中文:
定理 cast_commute
  条件: (n : 自然数) (x : α)
  结论: Commute (n : α) x
  证明: by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

Depends on / 依赖: Commute, Commute.one_left, Commute.zero_left, Nat.cast_succ, Nat.cast_zero, add_left, cast_succ, cast_zero, ihn.add_left, one_left, zero_left
-/
theorem cast_commute (n : Nat) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

/--
theorem `_root_.Commute.ofNat_left` / 定理 `_root_.Commute.ofNat_left`

English:
theorem _root_.Commute.ofNat_left
  given: (n : Nat) [n.AtLeastTwo] (x : α)
  statement: Commute (OfNat.ofNat n) x
  proof: n.cast_commute x

中文:
定理 _root_.Commute.ofNat_left
  条件: (n : 自然数) [n.AtLeastTwo] (x : α)
  结论: Commute (Of自然数.of自然数 n) x
  证明: n.cast_commute x

Depends on / 依赖: cast_commute, n.cast_commute
-/
theorem _root_.Commute.ofNat_left (n : Nat) [n.AtLeastTwo] (x : α) : Commute (OfNat.ofNat n) x :=
  n.cast_commute x

/--
theorem `cast_comm` / 定理 `cast_comm`

English:
theorem cast_comm
  given: (n : Nat) (x : α)
  statement: (n : α) * x = x * n
  proof: (cast_commute n x).eq

中文:
定理 cast_comm
  条件: (n : 自然数) (x : α)
  结论: (n : α) * x = x * n
  证明: (cast_commute n x).eq

Depends on / 依赖: cast_commute
-/
theorem cast_comm (n : Nat) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq

/--
theorem `commute_cast` / 定理 `commute_cast`

English:
theorem commute_cast
  given: (x : α) (n : Nat)
  statement: Commute x n
  proof: (n.cast_commute x).symm

中文:
定理 commute_cast
  条件: (x : α) (n : 自然数)
  结论: Commute x n
  证明: (n.cast_commute x).symm

Depends on / 依赖: cast_commute, n.cast_commute
-/
theorem commute_cast (x : α) (n : Nat) : Commute x n :=
  (n.cast_commute x).symm

/--
theorem `_root_.Commute.ofNat_right` / 定理 `_root_.Commute.ofNat_right`

English:
theorem _root_.Commute.ofNat_right
  given: (x : α) (n : Nat) [n.AtLeastTwo]
  statement: Commute x (OfNat.ofNat n)
  proof: n.commute_cast x

中文:
定理 _root_.Commute.ofNat_right
  条件: (x : α) (n : 自然数) [n.AtLeastTwo]
  结论: Commute x (Of自然数.of自然数 n)
  证明: n.commute_cast x

Depends on / 依赖: commute_cast, n.commute_cast
-/
theorem _root_.Commute.ofNat_right (x : α) (n : Nat) [n.AtLeastTwo] : Commute x (OfNat.ofNat n) :=
  n.commute_cast x

end NonAssocSemiring
end Nat

namespace SemiconjBy
variable [Semiring α] {a x y : α}

@[simp]
/--
lemma `natCast_mul_right` / 引理 `natCast_mul_right`

English:
lemma natCast_mul_right
  given: (h : SemiconjBy a x y) (n : Nat)
  statement: SemiconjBy a (n * x) (n * y)
  proof: SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]

中文:
引理 natCast_mul_right
  条件: (h : SemiconjBy a x y) (n : 自然数)
  结论: SemiconjBy a (n * x) (n * y)
  证明: SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]

Depends on / 依赖: Nat.commute_cast, SemiconjBy, SemiconjBy.mul_right, commute_cast, mul_right
-/
lemma natCast_mul_right (h : SemiconjBy a x y) (n : Nat) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]
/--
lemma `natCast_mul_left` / 引理 `natCast_mul_left`

English:
lemma natCast_mul_left
  given: (h : SemiconjBy a x y) (n : Nat)
  statement: SemiconjBy (n * a) x y
  proof: SemiconjBy.mul_left (Nat.cast_commute _ _) h

中文:
引理 natCast_mul_left
  条件: (h : SemiconjBy a x y) (n : 自然数)
  结论: SemiconjBy (n * a) x y
  证明: SemiconjBy.mul_left (Nat.cast_commute _ _) h

Depends on / 依赖: IsPretransitive, MulAction, MulAction.isMinimal_of_pretransitive, Nat.cast_commute, SemiconjBy, SemiconjBy.mul_left, cast_commute, isMinimal_of_pretransitive, mul_left
-/
lemma natCast_mul_left (h : SemiconjBy a x y) (n : Nat) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h

/--
lemma `natCast_mul_natCast_mul` / 引理 `natCast_mul_natCast_mul`

English:
lemma natCast_mul_natCast_mul
  given: (h : SemiconjBy a x y) (m n : Nat)
  proof: by
  simp [h]

中文:
引理 natCast_mul_natCast_mul
  条件: (h : SemiconjBy a x y) (m n : 自然数)
  证明: by
  simp [h]
-/
lemma natCast_mul_natCast_mul (h : SemiconjBy a x y) (m n : Nat) :
    SemiconjBy (m * a) (n * x) (n * y) := by
  simp [h]

end SemiconjBy

namespace Commute
variable [Semiring α] {a b : α}

/--
lemma `natCast_mul_right` / 引理 `natCast_mul_right`

English:
lemma natCast_mul_right
  given: (h : Commute a b) (n : Nat)
  statement: Commute a (n * b)
  proof: SemiconjBy.natCast_mul_right h n

中文:
引理 natCast_mul_right
  条件: (h : Commute a b) (n : 自然数)
  结论: Commute a (n * b)
  证明: SemiconjBy.natCast_mul_right h n
-/
@[simp] lemma natCast_mul_right (h : Commute a b) (n : Nat) : Commute a (n * b) :=
  SemiconjBy.natCast_mul_right h n

/--
lemma `natCast_mul_left` / 引理 `natCast_mul_left`

English:
lemma natCast_mul_left
  given: (h : Commute a b) (n : Nat)
  statement: Commute (n * a) b
  proof: SemiconjBy.natCast_mul_left h n

中文:
引理 natCast_mul_left
  条件: (h : Commute a b) (n : 自然数)
  结论: Commute (n * a) b
  证明: SemiconjBy.natCast_mul_left h n
-/
@[simp] lemma natCast_mul_left (h : Commute a b) (n : Nat) : Commute (n * a) b :=
  SemiconjBy.natCast_mul_left h n

/--
lemma `natCast_mul_natCast_mul` / 引理 `natCast_mul_natCast_mul`

English:
lemma natCast_mul_natCast_mul
  given: (h : Commute a b) (m n : Nat)
  statement: Commute (m * a) (n * b)
  proof: by
  simp [h]

中文:
引理 natCast_mul_natCast_mul
  条件: (h : Commute a b) (m n : 自然数)
  结论: Commute (m * a) (n * b)
  证明: by
  simp [h]
-/
lemma natCast_mul_natCast_mul (h : Commute a b) (m n : Nat) : Commute (m * a) (n * b) := by
  simp [h]

variable (a) (m n : Nat)

/--
lemma `self_natCast_mul` / 引理 `self_natCast_mul`

English:
lemma self_natCast_mul
  statement: Commute a (n * a)
  proof: (Commute.refl a).natCast_mul_right n

中文:
引理 self_natCast_mul
  结论: Commute a (n * a)
  证明: (Commute.refl a).natCast_mul_right n

Depends on / 依赖: Commute, Commute.refl, natCast_mul_right
-/
lemma self_natCast_mul : Commute a (n * a) := (Commute.refl a).natCast_mul_right n

/--
lemma `natCast_mul_self` / 引理 `natCast_mul_self`

English:
lemma natCast_mul_self
  statement: Commute (n * a) a
  proof: (Commute.refl a).natCast_mul_left n

中文:
引理 natCast_mul_self
  结论: Commute (n * a) a
  证明: (Commute.refl a).natCast_mul_left n

Depends on / 依赖: Commute, Commute.refl, natCast_mul_left
-/
lemma natCast_mul_self : Commute (n * a) a := (Commute.refl a).natCast_mul_left n

/--
lemma `self_natCast_mul_natCast_mul` / 引理 `self_natCast_mul_natCast_mul`

English:
lemma self_natCast_mul_natCast_mul
  statement: Commute (m * a) (n * a)
  proof: (Commute.refl a).natCast_mul_natCast_mul m n

中文:
引理 self_natCast_mul_natCast_mul
  结论: Commute (m * a) (n * a)
  证明: (Commute.refl a).natCast_mul_natCast_mul m n

Depends on / 依赖: Commute, Commute.refl, natCast_mul_natCast_mul
-/
lemma self_natCast_mul_natCast_mul : Commute (m * a) (n * a) :=
  (Commute.refl a).natCast_mul_natCast_mul m n

end Commute
