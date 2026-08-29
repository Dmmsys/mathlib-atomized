/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Fintype.Card

/-!
# support of a permutation

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `Disjoint` iff their `support` are disjoint.
* `Equiv.Perm.IsSwap`: `f = swap x y` for `x ≠ y`.
* `Equiv.Perm.support`: the elements `x : α` that are not fixed by `f`.

Assume `α` is a Fintype:
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.support` has at least 2 elements.)

-/

@[expose] public section


open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

/--
Definition of `Disjoint` / `Disjoint` 的定义

English:
definition Disjoint
  signature: (f g : Perm α)
  body: forall x, f x = x ∨ g x = x

中文:
定义 Disjoint
  签名: (f g : 置换 α)
  定义体: forall x, f x = x ∨ g x = x
-/
def Disjoint (f g : Perm α) :=
  forall x, f x = x ∨ g x = x

variable {f g h : Perm α}

@[symm]
/--
theorem `Disjoint.symm` / 定理 `Disjoint.symm`

English:
theorem Disjoint.symm
  statement: Disjoint f g -> Disjoint g f
  proof: by simp only [Disjoint, or_comm, imp_self]

中文:
定理 Disjoint.symm
  结论: Disjoint f g -> Disjoint g f
  证明: by simp only [Disjoint, or_comm, imp_self]
-/
theorem Disjoint.symm : Disjoint f g -> Disjoint g f := by simp only [Disjoint, or_comm, imp_self]

/--
Instance `Disjoint.stdSymm` / 实例 `Disjoint.stdSymm`

English:
instance Disjoint.stdSymm
  signature: : Std.Symm (α := Perm α) Disjoint where
  body: Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm

中文:
实例 Disjoint.stdSymm
  签名: : Std.Symm (α := 置换 α) Disjoint where
  定义体: Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm

Depends on / 依赖: Disjoint
-/
instance Disjoint.stdSymm : Std.Symm (α := Perm α) Disjoint where
  symm _ _ := Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm

/--
theorem `disjoint_comm` / 定理 `disjoint_comm`

English:
theorem disjoint_comm
  statement: Disjoint f g ↔ Disjoint g f
  proof: ⟨Disjoint.symm, Disjoint.symm⟩

中文:
定理 disjoint_comm
  结论: Disjoint f g ↔ Disjoint g f
  证明: ⟨Disjoint.symm, Disjoint.symm⟩

Depends on / 依赖: Disjoint, Disjoint.symm
-/
theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩

/--
theorem `Disjoint.commute` / 定理 `Disjoint.commute`

English:
theorem Disjoint.commute
  given: (h : Disjoint f g)
  statement: Commute f g
  proof: Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]

@[simp]

中文:
定理 Disjoint.commute
  条件: (h : Disjoint f g)
  结论: Commute f g
  证明: Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]

@[simp]

Depends on / 依赖: Equiv.ext, f.injective, g.injective, injective, mul_apply
-/
theorem Disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]

@[simp]
/--
theorem `disjoint_one_left` / 定理 `disjoint_one_left`

English:
theorem disjoint_one_left
  given: (f : Perm α)
  statement: Disjoint 1 f
  proof: fun _ => Or.inl rfl

@[simp]

中文:
定理 disjoint_one_left
  条件: (f : 置换 α)
  结论: Disjoint 1 f
  证明: fun _ => Or.inl rfl

@[simp]

Depends on / 依赖: Or.inl
-/
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl

@[simp]
/--
theorem `disjoint_one_right` / 定理 `disjoint_one_right`

English:
theorem disjoint_one_right
  given: (f : Perm α)
  statement: Disjoint f 1
  proof: fun _ => Or.inr rfl

中文:
定理 disjoint_one_right
  条件: (f : 置换 α)
  结论: Disjoint f 1
  证明: fun _ => Or.inr rfl

Depends on / 依赖: Or.inr
-/
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl

/--
theorem `disjoint_iff_eq_or_eq` / 定理 `disjoint_iff_eq_or_eq`

English:
theorem disjoint_iff_eq_or_eq
  statement: Disjoint f g ↔ forall x : α, f x = x ∨ g x = x
  proof: Iff.rfl

@[simp]

中文:
定理 disjoint_iff_eq_or_eq
  结论: Disjoint f g ↔ 对任意 x : α, f x = x ∨ g x = x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ forall x : α, f x = x ∨ g x = x :=
  Iff.rfl

@[simp]
/--
theorem `disjoint_refl_iff` / 定理 `disjoint_refl_iff`

English:
theorem disjoint_refl_iff
  statement: Disjoint f f ↔ f = 1
  proof: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  rcases h x with hx | hx <;> simp [hx]

中文:
定理 disjoint_refl_iff
  结论: Disjoint f f ↔ f = 1
  证明: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  rcases h x with hx | hx <;> simp [hx]

Depends on / 依赖: disjoint_one_left, h.symm
-/
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  rcases h x with hx | hx <;> simp [hx]

/--
theorem `Disjoint.inv_left` / 定理 `Disjoint.inv_left`

English:
theorem Disjoint.inv_left
  given: (h : Disjoint f g)
  statement: Disjoint f⁻¹ g
  proof: by
  intro x
  rw [inv_eq_iff_eq]; rw [eq_comm]
  exact h x

中文:
定理 Disjoint.inv_left
  条件: (h : Disjoint f g)
  结论: Disjoint f⁻¹ g
  证明: by
  intro x
  rw [inv_eq_iff_eq]; rw [eq_comm]
  exact h x

Depends on / 依赖: eq_comm, inv_eq_iff_eq
-/
theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g := by
  intro x
  rw [inv_eq_iff_eq]; rw [eq_comm]
  exact h x

/--
theorem `Disjoint.inv_right` / 定理 `Disjoint.inv_right`

English:
theorem Disjoint.inv_right
  given: (h : Disjoint f g)
  statement: Disjoint f g⁻¹
  proof: h.symm.inv_left.symm

@[simp]

中文:
定理 Disjoint.inv_right
  条件: (h : Disjoint f g)
  结论: Disjoint f g⁻¹
  证明: h.symm.inv_left.symm

@[simp]

Depends on / 依赖: h.symm.inv_left.symm, inv_left
-/
theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm

@[simp]
/--
theorem `disjoint_inv_left_iff` / 定理 `disjoint_inv_left_iff`

English:
theorem disjoint_inv_left_iff
  statement: Disjoint f⁻¹ g ↔ Disjoint f g
  proof: by
  refine ⟨fun h => ?_, Disjoint.inv_left⟩
  convert! h.inv_left

@[simp]

中文:
定理 disjoint_inv_left_iff
  结论: Disjoint f⁻¹ g ↔ Disjoint f g
  证明: by
  refine ⟨fun h => ?_, Disjoint.inv_left⟩
  convert! h.inv_left

@[simp]

Depends on / 依赖: Disjoint, Disjoint.inv_left, convert, h.inv_left, inv_left
-/
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g := by
  refine ⟨fun h => ?_, Disjoint.inv_left⟩
  convert! h.inv_left

@[simp]
/--
theorem `disjoint_inv_right_iff` / 定理 `disjoint_inv_right_iff`

English:
theorem disjoint_inv_right_iff
  statement: Disjoint f g⁻¹ ↔ Disjoint f g
  proof: by
  rw [disjoint_comm]; rw [disjoint_inv_left_iff]; rw [disjoint_comm]

中文:
定理 disjoint_inv_right_iff
  结论: Disjoint f g⁻¹ ↔ Disjoint f g
  证明: by
  rw [disjoint_comm]; rw [disjoint_inv_left_iff]; rw [disjoint_comm]

Depends on / 依赖: disjoint_comm, disjoint_inv_left_iff
-/
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm]; rw [disjoint_inv_left_iff]; rw [disjoint_comm]

/--
theorem `Disjoint.mul_left` / 定理 `Disjoint.mul_left`

English:
theorem Disjoint.mul_left
  given: (H1 : Disjoint f h) (H2 : Disjoint g h)
  statement: Disjoint (f * g) h
  proof: fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]

中文:
定理 Disjoint.mul_left
  条件: (H1 : Disjoint f h) (H2 : Disjoint g h)
  结论: Disjoint (f * g) h
  证明: fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]
-/
theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]

/--
theorem `Disjoint.mul_right` / 定理 `Disjoint.mul_right`

English:
theorem Disjoint.mul_right
  given: (H1 : Disjoint f g) (H2 : Disjoint f h)
  statement: Disjoint f (g * h)
  proof: by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

@[simp]

中文:
定理 Disjoint.mul_right
  条件: (H1 : Disjoint f g) (H2 : Disjoint f h)
  结论: Disjoint f (g * h)
  证明: by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

@[simp]

Depends on / 依赖: H1.symm.mul_left, H2.symm, disjoint_comm, mul_left
-/
theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

@[simp]
/--
theorem `disjoint_conj` / 定理 `disjoint_conj`

English:
theorem disjoint_conj
  given: (h : Perm α)
  statement: Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g
  proof: (h⁻¹).forall_congr fun {_} => by simp only [mul_apply, eq_inv_iff_eq]

中文:
定理 disjoint_conj
  条件: (h : 置换 α)
  结论: Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g
  证明: (h⁻¹).forall_congr fun {_} => by simp only [mul_apply, eq_inv_iff_eq]

Depends on / 依赖: eq_inv_iff_eq, forall_congr, mul_apply
-/
theorem disjoint_conj (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g :=
  (h⁻¹).forall_congr fun {_} => by simp only [mul_apply, eq_inv_iff_eq]

/--
theorem `Disjoint.conj` / 定理 `Disjoint.conj`

English:
theorem Disjoint.conj
  given: (H : Disjoint f g) (h : Perm α)
  statement: Disjoint (h * f * h⁻¹) (h * g * h⁻¹)
  proof: (disjoint_conj h).2 H

中文:
定理 Disjoint.conj
  条件: (H : Disjoint f g) (h : 置换 α)
  结论: Disjoint (h * f * h⁻¹) (h * g * h⁻¹)
  证明: (disjoint_conj h).2 H

Depends on / 依赖: disjoint_conj
-/
theorem Disjoint.conj (H : Disjoint f g) (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) :=
  (disjoint_conj h).2 H

/--
theorem `disjoint_prod_right` / 定理 `disjoint_prod_right`

English:
theorem disjoint_prod_right
  given: (l : List (Perm α)) (h : forall g in l, Disjoint f g)
  proof: by
  induction l with
  | nil => exact disjoint_one_right _
  | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

中文:
定理 disjoint_prod_right
  条件: (l : 列表 (置换 α)) (h : 对任意 g in l, Disjoint f g)
  证明: by
  induction l with
  | nil => exact disjoint_one_right _
  | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

Depends on / 依赖: List.mem_cons_of_mem, List.mem_cons_self, List.prod_cons, disjoint_one_right, mem_cons_of_mem, mem_cons_self, mul_right, prod_cons
-/
theorem disjoint_prod_right (l : List (Perm α)) (h : forall g in l, Disjoint f g) :
    Disjoint f l.prod := by
  induction l with
  | nil => exact disjoint_one_right _
  | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

/--
theorem `disjoint_noncommProd_right` / 定理 `disjoint_noncommProd_right`

English:
theorem disjoint_noncommProd_right
  statement: {ι : Type*} {k : ι -> Perm α} {s : Finset ι}
  proof: noncommProd_induction s k hs g.Disjoint (fun _ _ => Disjoint.mul_right) (disjoint_one_right g) hg

中文:
定理 disjoint_noncommProd_right
  结论: {ι : 类型} {k : ι -> 置换 α} {s : 有限集 ι}
  证明: noncommProd_induction s k hs g.Disjoint (fun _ _ => Disjoint.mul_right) (disjoint_one_right g) hg

Depends on / 依赖: Disjoint, Disjoint.mul_right, disjoint_one_right, g.Disjoint, mul_right, noncommProd_induction
-/
theorem disjoint_noncommProd_right {ι : Type*} {k : ι -> Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j => Commute (k i) (k j))
    (hg : forall i in s, g.Disjoint (k i)) :
    Disjoint g (s.noncommProd k (hs)) :=
  noncommProd_induction s k hs g.Disjoint (fun _ _ => Disjoint.mul_right) (disjoint_one_right g) hg

open scoped List in
/--
theorem `disjoint_prod_perm` / 定理 `disjoint_prod_perm`

English:
theorem disjoint_prod_perm
  given: {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂)
  proof: hp.prod_eq' hl.imp Disjoint.commute

中文:
定理 disjoint_prod_perm
  条件: {l₁ l₂ : 列表 (置换 α)} (hl : l₁.两两 Disjoint) (hp : l₁ ~ l₂)
  证明: hp.prod_eq' hl.imp Disjoint.commute

Depends on / 依赖: Disjoint, Disjoint.commute, commute, hl.imp, hp.prod_eq, prod_eq
-/
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) :
    l₁.prod = l₂.prod :=
hp.prod_eq' hl.imp Disjoint.commute

/--
theorem `nodup_of_pairwise_disjoint` / 定理 `nodup_of_pairwise_disjoint`

English:
theorem nodup_of_pairwise_disjoint
  statement: {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
  proof: by
  grind [List.Pairwise.imp_of_mem, disjoint_refl_iff]

中文:
定理 nodup_of_pairwise_disjoint
  结论: {l : 列表 (置换 α)} (h1 : (1 : 置换 α) ∉ l)
  证明: by
  grind [List.Pairwise.imp_of_mem, disjoint_refl_iff]

Depends on / 依赖: List.Pairwise.imp_of_mem, Pairwise, disjoint_refl_iff, imp_of_mem
-/
theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Disjoint) : l.Nodup := by
  grind [List.Pairwise.imp_of_mem, disjoint_refl_iff]

/--
theorem `pow_apply_eq_self_of_apply_eq_self` / 定理 `pow_apply_eq_self_of_apply_eq_self`

English:
theorem pow_apply_eq_self_of_apply_eq_self
  given: {x : α} (hfx : f x = x)
  statement: forall n : Nat, (f ^ n) x = x

中文:
定理 pow_apply_eq_self_of_apply_eq_self
  条件: {x : α} (hfx : f x = x)
  结论: 对任意 n : 自然数, (f ^ n) x = x
-/
theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : forall n : Nat, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by rw [pow_succ, mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self hfx n]

/--
theorem `zpow_apply_eq_self_of_apply_eq_self` / 定理 `zpow_apply_eq_self_of_apply_eq_self`

English:
theorem zpow_apply_eq_self_of_apply_eq_self
  given: {x : α} (hfx : f x = x)
  statement: forall n : Int, (f ^ n) x = x

中文:
定理 zpow_apply_eq_self_of_apply_eq_self
  条件: {x : α} (hfx : f x = x)
  结论: 对任意 n : 整数, (f ^ n) x = x
-/
theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : forall n : Int, (f ^ n) x = x
  | (n : Nat) => pow_apply_eq_self_of_apply_eq_self hfx n
  | Int.negSucc n => by rw [zpow_negSucc, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

/--
theorem `pow_apply_eq_of_apply_apply_eq_self` / 定理 `pow_apply_eq_of_apply_apply_eq_self`

English:
theorem pow_apply_eq_of_apply_apply_eq_self
  given: {x : α} (hffx : f (f x) = x)

中文:
定理 pow_apply_eq_of_apply_apply_eq_self
  条件: {x : α} (hffx : f (f x) = x)
-/
theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    forall n : Nat, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self hffx n).elim
      (fun h => Or.inr (by rw [pow_succ', mul_apply, h]))
      fun h => Or.inl (by rw [pow_succ', mul_apply, h, hffx])

/--
theorem `zpow_apply_eq_of_apply_apply_eq_self` / 定理 `zpow_apply_eq_of_apply_apply_eq_self`

English:
theorem zpow_apply_eq_of_apply_apply_eq_self
  given: {x : α} (hffx : f (f x) = x)

中文:
定理 zpow_apply_eq_of_apply_apply_eq_self
  条件: {x : α} (hffx : f (f x) = x)
-/
theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    forall i : Int, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : Nat) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | Int.negSucc n => by
    rw [zpow_negSucc]; rw [inv_eq_iff_eq]; rw [← f.injective.eq_iff]; rw [← mul_apply]; rw [← pow_succ']; rw [eq_comm]; rw [inv_eq_iff_eq]; rw [← mul_apply]; rw [← pow_succ]; rw [@eq_comm _ x]; rw [or_comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _

/--
theorem `Disjoint.mul_apply_eq_iff` / 定理 `Disjoint.mul_apply_eq_iff`

English:
theorem Disjoint.mul_apply_eq_iff
  given: {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α}
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [mul_apply, h.2, h.1]⟩
  rcases hστ a with hσ | hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩

中文:
定理 Disjoint.mul_apply_eq_iff
  条件: {σ τ : 置换 α} (hστ : Disjoint σ τ) {a : α}
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [mul_apply, h.2, h.1]⟩
  rcases hστ a with hσ | hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩

Depends on / 依赖: congr_arg, h.trans, injective, mul_apply, symm.trans
-/
theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} :
    (σ * τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine ⟨fun h => ?_, fun h => by rw [mul_apply, h.2, h.1]⟩
  rcases hστ a with hσ | hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩

/--
theorem `Disjoint.mul_eq_one_iff` / 定理 `Disjoint.mul_eq_one_iff`

English:
theorem Disjoint.mul_eq_one_iff
  given: {σ τ : Perm α} (hστ : Disjoint σ τ)
  proof: by
  simp_rw [Perm.ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]

中文:
定理 Disjoint.mul_eq_one_iff
  条件: {σ τ : 置换 α} (hστ : Disjoint σ τ)
  证明: by
  simp_rw [Perm.ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]

Depends on / 依赖: Perm.ext_iff, ext_iff, forall_and, mul_apply_eq_iff, one_apply, simp_rw
-/
theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) :
    σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [Perm.ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]

/--
theorem `Disjoint.zpow_disjoint_zpow` / 定理 `Disjoint.zpow_disjoint_zpow`

English:
theorem Disjoint.zpow_disjoint_zpow
  given: {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : Int)
  proof: fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)

中文:
定理 Disjoint.zpow_disjoint_zpow
  条件: {σ τ : 置换 α} (hστ : Disjoint σ τ) (m n : 整数)
  证明: fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)
-/
theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : Int) :
    Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)

/--
theorem `Disjoint.pow_disjoint_pow` / 定理 `Disjoint.pow_disjoint_pow`

English:
theorem Disjoint.pow_disjoint_pow
  given: {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : Nat)
  proof: hστ.zpow_disjoint_zpow m n

中文:
定理 Disjoint.pow_disjoint_pow
  条件: {σ τ : 置换 α} (hστ : Disjoint σ τ) (m n : 自然数)
  证明: hστ.zpow_disjoint_zpow m n

Depends on / 依赖: zpow_disjoint_zpow
-/
theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : Nat) :
    Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

end Disjoint

section IsSwap

variable [DecidableEq α]

/--
Definition of `IsSwap` / `IsSwap` 的定义

English:
definition IsSwap
  signature: (f : Perm α)
  body: exists x y, x != y ∧ f = swap x y

@[simp]

中文:
定义 IsSwap
  签名: (f : 置换 α)
  定义体: exists x y, x != y ∧ f = swap x y

@[simp]
-/
def IsSwap (f : Perm α) : Prop :=
  exists x y, x != y ∧ f = swap x y

@[simp]
/--
theorem `ofSubtype_swap_eq` / 定理 `ofSubtype_swap_eq`

English:
theorem ofSubtype_swap_eq
  given: {p : α -> Prop} [DecidablePred p] (x y : Subtype p)
  proof: by
  grind [ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem]

中文:
定理 ofSubtype_swap_eq
  条件: {p : α -> 命题} [DecidablePred p] (x y : 子类型 p)
  证明: by
  grind [ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem]

Depends on / 依赖: ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem
-/
theorem ofSubtype_swap_eq {p : α -> Prop} [DecidablePred p] (x y : Subtype p) :
    ofSubtype (Equiv.swap x y) = Equiv.swap ↑x ↑y := by
  grind [ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem]

/--
theorem `IsSwap.of_subtype_isSwap` / 定理 `IsSwap.of_subtype_isSwap`

English:
theorem IsSwap.of_subtype_isSwap
  statement: {p : α -> Prop} [DecidablePred p] {f : Perm (Subtype p)}
  proof: let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne, Subtype.ext_iff] at hxy
    exact hxy.1, by
    rw [hxy.2]; rw [ofSubtype_swap_eq]⟩

中文:
定理 IsSwap.of_subtype_isSwap
  结论: {p : α -> 命题} [DecidablePred p] {f : 置换 (子类型 p)}
  证明: let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne, Subtype.ext_iff] at hxy
    exact hxy.1, by
    rw [hxy.2]; rw [ofSubtype_swap_eq]⟩

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, ofSubtype_swap_eq
-/
theorem IsSwap.of_subtype_isSwap {p : α -> Prop} [DecidablePred p] {f : Perm (Subtype p)}
    (h : f.IsSwap) : (ofSubtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne, Subtype.ext_iff] at hxy
    exact hxy.1, by
    rw [hxy.2]; rw [ofSubtype_swap_eq]⟩

/--
theorem `ne_and_ne_of_swap_mul_apply_ne_self` / 定理 `ne_and_ne_of_swap_mul_apply_ne_self`

English:
theorem ne_and_ne_of_swap_mul_apply_ne_self
  given: {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y != y)
  proof: by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

中文:
定理 ne_and_ne_of_swap_mul_apply_ne_self
  条件: {f : 置换 α} {x y : α} (hy : (swap x (f x) * f) y != y)
  证明: by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

Depends on / 依赖: eq_iff, f.injective.eq_iff, injective, mul_apply, swap_apply_def
-/
theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y != y) :
    f y != y ∧ y != x := by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

end IsSwap

section support

section Set

variable (p q : Perm α)

/--
lemma `set_support_symm_eq` / 引理 `set_support_symm_eq`

English:
lemma set_support_symm_eq
  statement: {x | p.symm x != x} = {x | p x != x}
  proof: by
  ext; simp [eq_symm_apply, eq_comm]

中文:
引理 set_support_symm_eq
  结论: {x | p.symm x != x} = {x | p x != x}
  证明: by
  ext; simp [eq_symm_apply, eq_comm]

Depends on / 依赖: eq_comm, eq_symm_apply
-/
lemma set_support_symm_eq : {x | p.symm x != x} = {x | p x != x} := by
  ext; simp [eq_symm_apply, eq_comm]

/--
theorem `set_support_apply_mem` / 定理 `set_support_apply_mem`

English:
theorem set_support_apply_mem
  given: {p : Perm α} {a : α}
  proof: by simp

中文:
定理 set_support_apply_mem
  条件: {p : 置换 α} {a : α}
  证明: by simp
-/
theorem set_support_apply_mem {p : Perm α} {a : α} :
    p a in { x | p x != x } ↔ a in { x | p x != x } := by simp

/--
theorem `set_support_zpow_subset` / 定理 `set_support_zpow_subset`

English:
theorem set_support_zpow_subset
  given: (n : Int)
  statement: { x | (p ^ n) x != x } subseteq { x | p x != x }
  proof: by
  intro x
  simp only [Set.mem_ofPred_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx

中文:
定理 set_support_zpow_subset
  条件: (n : 整数)
  结论: { x | (p ^ n) x != x } subseteq { x | p x != x }
  证明: by
  intro x
  simp only [Set.mem_ofPred_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx

Depends on / 依赖: Set.mem_ofPred_eq, mem_ofPred_eq, zpow_apply_eq_self_of_apply_eq_self
-/
theorem set_support_zpow_subset (n : Int) : { x | (p ^ n) x != x } subseteq { x | p x != x } := by
  intro x
  simp only [Set.mem_ofPred_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx

/--
theorem `set_support_mul_subset` / 定理 `set_support_mul_subset`

English:
theorem set_support_mul_subset
  statement: { x | (p * q) x != x } subseteq { x | p x != x } union { x | q x != x }
  proof: by
  simp only [coe_mul]
  grind

中文:
定理 set_support_mul_subset
  结论: { x | (p * q) x != x } subseteq { x | p x != x } union { x | q x != x }
  证明: by
  simp only [coe_mul]
  grind

Depends on / 依赖: coe_mul
-/
theorem set_support_mul_subset : { x | (p * q) x != x } subseteq { x | p x != x } union { x | q x != x } := by
  simp only [coe_mul]
  grind

end Set

@[simp]
/--
theorem `apply_pow_apply_eq_iff` / 定理 `apply_pow_apply_eq_iff`

English:
theorem apply_pow_apply_eq_iff
  given: (f : Perm α) (n : Nat) {x : α}
  proof: by
  rw [← mul_apply]; rw [Commute.self_pow f]; rw [mul_apply]; rw [apply_eq_iff_eq]

@[simp]

中文:
定理 apply_pow_apply_eq_iff
  条件: (f : 置换 α) (n : 自然数) {x : α}
  证明: by
  rw [← mul_apply]; rw [Commute.self_pow f]; rw [mul_apply]; rw [apply_eq_iff_eq]

@[simp]

Depends on / 依赖: Commute, Commute.self_pow, apply_eq_iff_eq, mul_apply, self_pow
-/
theorem apply_pow_apply_eq_iff (f : Perm α) (n : Nat) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply]; rw [Commute.self_pow f]; rw [mul_apply]; rw [apply_eq_iff_eq]

@[simp]
/--
theorem `apply_zpow_apply_eq_iff` / 定理 `apply_zpow_apply_eq_iff`

English:
theorem apply_zpow_apply_eq_iff
  given: (f : Perm α) (n : Int) {x : α}
  proof: by
  rw [← mul_apply]; rw [Commute.self_zpow f]; rw [mul_apply]; rw [apply_eq_iff_eq]

中文:
定理 apply_zpow_apply_eq_iff
  条件: (f : 置换 α) (n : 整数) {x : α}
  证明: by
  rw [← mul_apply]; rw [Commute.self_zpow f]; rw [mul_apply]; rw [apply_eq_iff_eq]

Depends on / 依赖: Commute, Commute.self_zpow, apply_eq_iff_eq, mul_apply, self_zpow
-/
theorem apply_zpow_apply_eq_iff (f : Perm α) (n : Int) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply]; rw [Commute.self_zpow f]; rw [mul_apply]; rw [apply_eq_iff_eq]

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (f : Perm α)
  body: {x | f x != x}

@[simp]

中文:
定义 support
  签名: (f : 置换 α)
  定义体: {x | f x != x}

@[simp]
-/
def support (f : Perm α) : Finset α := {x | f x != x}

@[simp]
/--
theorem `mem_support` / 定理 `mem_support`

English:
theorem mem_support
  given: {x : α}
  statement: x in f.support ↔ f x != x
  proof: by
  rw [support]; rw [mem_filter]; rw [and_iff_right (mem_univ x)]

中文:
定理 mem_support
  条件: {x : α}
  结论: x in f.support ↔ f x != x
  证明: by
  rw [support]; rw [mem_filter]; rw [and_iff_right (mem_univ x)]

Depends on / 依赖: and_iff_right, mem_filter, mem_univ, support
-/
theorem mem_support {x : α} : x in f.support ↔ f x != x := by
  rw [support]; rw [mem_filter]; rw [and_iff_right (mem_univ x)]

/--
theorem `notMem_support` / 定理 `notMem_support`

English:
theorem notMem_support
  given: {x : α}
  statement: x ∉ f.support ↔ f x = x
  proof: by simp

中文:
定理 notMem_support
  条件: {x : α}
  结论: x ∉ f.support ↔ f x = x
  证明: by simp
-/
theorem notMem_support {x : α} : x ∉ f.support ↔ f x = x := by simp

/--
theorem `coe_support_eq_set_support` / 定理 `coe_support_eq_set_support`

English:
theorem coe_support_eq_set_support
  given: (f : Perm α)
  statement: (f.support : Set α) = { x | f x != x }
  proof: by
  ext
  simp

@[simp]

中文:
定理 coe_support_eq_set_support
  条件: (f : 置换 α)
  结论: (f.support : 集合 α) = { x | f x != x }
  证明: by
  ext
  simp

@[simp]
-/
theorem coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x != x } := by
  ext
  simp

@[simp]
/--
theorem `support_eq_empty_iff` / 定理 `support_eq_empty_iff`

English:
theorem support_eq_empty_iff
  given: {σ : Perm α}
  statement: σ.support = ∅ ↔ σ = 1
  proof: by
  simp_rw [Finset.ext_iff, mem_support, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[simp]

中文:
定理 support_eq_empty_iff
  条件: {σ : 置换 α}
  结论: σ.support = ∅ ↔ σ = 1
  证明: by
  simp_rw [Finset.ext_iff, mem_support, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[simp]

Depends on / 依赖: Equiv.Perm.ext_iff, Finset, Finset.ext_iff, Finset.notMem_empty, ext_iff, iff_false, mem_support, notMem_empty, not_not, one_apply, simp_rw
-/
theorem support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[simp]
/--
theorem `support_one` / 定理 `support_one`

English:
theorem support_one
  statement: (1 : Perm α).support = ∅
  proof: by rw [support_eq_empty_iff]

@[simp]

中文:
定理 support_one
  结论: (1 : 置换 α).support = ∅
  证明: by rw [support_eq_empty_iff]

@[simp]

Depends on / 依赖: support_eq_empty_iff
-/
theorem support_one : (1 : Perm α).support = ∅ := by rw [support_eq_empty_iff]

@[simp]
/--
theorem `support_refl` / 定理 `support_refl`

English:
theorem support_refl
  statement: support (Equiv.refl α) = ∅
  proof: support_one

中文:
定理 support_refl
  结论: support (等价.refl α) = ∅
  证明: support_one

Depends on / 依赖: support_one
-/
theorem support_refl : support (Equiv.refl α) = ∅ :=
  support_one

/--
theorem `support_congr` / 定理 `support_congr`

English:
theorem support_congr
  given: (h : f.support subseteq g.support) (h' : forall x in g.support, f x = g x)
  statement: f = g
  proof: by
  grind [notMem_support]

中文:
定理 support_congr
  条件: (h : f.support subseteq g.support) (h' : 对任意 x in g.support, f x = g x)
  结论: f = g
  证明: by
  grind [notMem_support]

Depends on / 依赖: notMem_support
-/
theorem support_congr (h : f.support subseteq g.support) (h' : forall x in g.support, f x = g x) : f = g := by
  grind [notMem_support]

/--
theorem `mem_support_iff_of_commute` / 定理 `mem_support_iff_of_commute`

English:
theorem mem_support_iff_of_commute
  given: {g c : Perm α} (hgc : Commute g c) (x : α)
  proof: by
  simp only [mem_support, not_iff_not, ← mul_apply]
  rw [← hgc]; rw [mul_apply]; rw [Equiv.apply_eq_iff_eq]

中文:
定理 mem_support_iff_of_commute
  条件: {g c : 置换 α} (hgc : Commute g c) (x : α)
  证明: by
  simp only [mem_support, not_iff_not, ← mul_apply]
  rw [← hgc]; rw [mul_apply]; rw [Equiv.apply_eq_iff_eq]

Depends on / 依赖: Equiv.apply_eq_iff_eq, apply_eq_iff_eq, mem_support, mul_apply, not_iff_not
-/
theorem mem_support_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x in c.support ↔ x in c.support := by
  simp only [mem_support, not_iff_not, ← mul_apply]
  rw [← hgc]; rw [mul_apply]; rw [Equiv.apply_eq_iff_eq]

/--
theorem `support_mul_le` / 定理 `support_mul_le`

English:
theorem support_mul_le
  given: (f g : Perm α)
  statement: (f * g).support <= f.support ⊔ g.support
  proof: fun x => by
  simp only [sup_eq_union]
  rw [mem_union]; rw [mem_support]; rw [mem_support]; rw [mem_support]; rw [mul_apply]; rw [← not_and_or]; rw [not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg]; rw [hf]

中文:
定理 support_mul_le
  条件: (f g : 置换 α)
  结论: (f * g).support <= f.support ⊔ g.support
  证明: fun x => by
  simp only [sup_eq_union]
  rw [mem_union]; rw [mem_support]; rw [mem_support]; rw [mem_support]; rw [mul_apply]; rw [← not_and_or]; rw [not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg]; rw [hf]

Depends on / 依赖: mem_support, mem_union, mul_apply, not_and_or, not_imp_not, sup_eq_union
-/
theorem support_mul_le (f g : Perm α) : (f * g).support <= f.support ⊔ g.support := fun x => by
  simp only [sup_eq_union]
  rw [mem_union]; rw [mem_support]; rw [mem_support]; rw [mem_support]; rw [mul_apply]; rw [← not_and_or]; rw [not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg]; rw [hf]

/--
theorem `exists_mem_support_of_mem_support_prod` / 定理 `exists_mem_support_of_mem_support_prod`

English:
theorem exists_mem_support_of_mem_support_prod
  statement: {l : List (Perm α)} {x : α}
  proof: by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons]; rw [mul_apply]; rw [ih]; rw [hx]
    · simp only [List.mem_cons, true_or]
    grind

中文:
定理 存在_mem_support_of_mem_support_prod
  结论: {l : 列表 (置换 α)} {x : α}
  证明: by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons]; rw [mul_apply]; rw [ih]; rw [hx]
    · simp only [List.mem_cons, true_or]
    grind

Depends on / 依赖: List.mem_cons, List.prod_cons, contrapose, mem_cons, mem_support, mul_apply, not_not, prod_cons, simp_rw, true_or
-/
theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x in l.prod.support) : exists f : Perm α, f in l ∧ x in f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons]; rw [mul_apply]; rw [ih]; rw [hx]
    · simp only [List.mem_cons, true_or]
    grind

/--
theorem `support_pow_le` / 定理 `support_pow_le`

English:
theorem support_pow_le
  given: (σ : Perm α) (n : Nat)
  statement: (σ ^ n).support <= σ.support
  proof: fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]

中文:
定理 support_pow_le
  条件: (σ : 置换 α) (n : 自然数)
  结论: (σ ^ n).support <= σ.support
  证明: fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
-/
theorem support_pow_le (σ : Perm α) (n : Nat) : (σ ^ n).support <= σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
/--
theorem `support_inv` / 定理 `support_inv`

English:
theorem support_inv
  given: (σ : Perm α)
  statement: support σ⁻¹ = σ.support
  proof: by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, imp_true_iff]

中文:
定理 support_inv
  条件: (σ : 置换 α)
  结论: support σ⁻¹ = σ.support
  证明: by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, imp_true_iff]

Depends on / 依赖: Finset, Finset.ext_iff, eq_comm, ext_iff, imp_true_iff, inv_eq_iff_eq, inv_eq_iff_eq.trans, mem_support, not_iff_not, simp_rw
-/
theorem support_inv (σ : Perm α) : support σ⁻¹ = σ.support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, imp_true_iff]

/--
theorem `apply_mem_support` / 定理 `apply_mem_support`

English:
theorem apply_mem_support
  given: {x : α}
  statement: f x in f.support ↔ x in f.support
  proof: by
  rw [mem_support]; rw [mem_support]; rw [Ne]; rw [Ne]; rw [apply_eq_iff_eq]

中文:
定理 apply_mem_support
  条件: {x : α}
  结论: f x in f.support ↔ x in f.support
  证明: by
  rw [mem_support]; rw [mem_support]; rw [Ne]; rw [Ne]; rw [apply_eq_iff_eq]

Depends on / 依赖: apply_eq_iff_eq, mem_support
-/
theorem apply_mem_support {x : α} : f x in f.support ↔ x in f.support := by
  rw [mem_support]; rw [mem_support]; rw [Ne]; rw [Ne]; rw [apply_eq_iff_eq]

/--
theorem `isInvariant_of_support_le` / 定理 `isInvariant_of_support_le`

English:
theorem isInvariant_of_support_le
  given: {c : Perm α} {s : Finset α} (hcs : c.support <= s) (x : α)
  proof: by
  by_cases hx' : x in c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [notMem_support.mp hx']

中文:
定理 isInvariant_of_support_le
  条件: {c : 置换 α} {s : 有限集 α} (hcs : c.support <= s) (x : α)
  证明: by
  by_cases hx' : x in c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [notMem_support.mp hx']

Depends on / 依赖: apply_mem_support, apply_mem_support.mpr, c.support, notMem_support, notMem_support.mp, support
-/
theorem isInvariant_of_support_le {c : Perm α} {s : Finset α} (hcs : c.support <= s) (x : α) :
    c x in s ↔ x in s := by
  by_cases hx' : x in c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [notMem_support.mp hx']

/--
lemma `ofSubtype_eq_iff` / 引理 `ofSubtype_eq_iff`

English:
lemma ofSubtype_eq_iff
  statement: {g c : Equiv.Perm α} {s : Finset α}
  proof: by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_support]; rw [← h a]; rw [ofSubtype_apply_of_not_mem (p := (· in s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a]; rw [ofSubtype_apply_of_mem (p := (· in s)) _ ha]; rw [subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a in s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· in s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· in s)) _ ha, eq_comm, ← notMem_support]
      exact Finset.notMem_mono hc ha

中文:
引理 ofSubtype_eq_iff
  结论: {g c : 等价.置换 α} {s : 有限集 α}
  证明: by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_support]; rw [← h a]; rw [ofSubtype_apply_of_not_mem (p := (· in s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a]; rw [ofSubtype_apply_of_mem (p := (· in s)) _ ha]; rw [subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a in s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· in s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· in s)) _ ha, eq_comm, ← notMem_support]
      exact Finset.notMem_mono hc ha

Depends on / 依赖: Equiv.ext_iff, Subtype, Subtype.forall, Subtype.mk.injEq, ext_iff, isInvariant_of_support_le, mem_support, ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem, specialize, subtypePerm, subtypePerm_apply
-/
lemma ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α}
    (hg : forall x, g x in s ↔ x in s) :
    ofSubtype (g.subtypePerm hg) = c ↔
      c.support <= s ∧
      forall (hc' : forall x, c x in s ↔ x in s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_support]; rw [← h a]; rw [ofSubtype_apply_of_not_mem (p := (· in s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a]; rw [ofSubtype_apply_of_mem (p := (· in s)) _ ha]; rw [subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a in s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· in s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· in s)) _ ha, eq_comm, ← notMem_support]
      exact Finset.notMem_mono hc ha

/--
theorem `support_ofSubtype` / 定理 `support_ofSubtype`

English:
theorem support_ofSubtype
  given: {p : α -> Prop} [DecidablePred p] (u : Perm (Subtype p))
  proof: by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

中文:
定理 support_ofSubtype
  条件: {p : α -> 命题} [DecidablePred p] (u : 置换 (子类型 p))
  证明: by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

Depends on / 依赖: Embedding, Finset, Finset.mem_map, Function, Function.Embedding.coe_subtype, Subtype, Subtype.coe_inj, Subtype.exists, coe_inj, coe_subtype, exists_and_right, exists_eq_right, forall_prop_of_false, forall_prop_of_true, mem_map, mem_support, ne_eq, not_exists, not_iff_comm, not_not
-/
theorem support_ofSubtype {p : α -> Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).support = u.support.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_support, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

/--
theorem `mem_support_ofSubtype` / 定理 `mem_support_ofSubtype`

English:
theorem mem_support_ofSubtype
  given: {p : α -> Prop} [DecidablePred p] (x : α) (u : Perm (Subtype p))
  proof: by
  simp [support_ofSubtype]

中文:
定理 mem_support_ofSubtype
  条件: {p : α -> 命题} [DecidablePred p] (x : α) (u : 置换 (子类型 p))
  证明: by
  simp [support_ofSubtype]

Depends on / 依赖: support_ofSubtype
-/
theorem mem_support_ofSubtype {p : α -> Prop} [DecidablePred p] (x : α) (u : Perm (Subtype p)) :
    x in (ofSubtype u).support ↔ exists (hx : p x), ⟨x, hx⟩ in u.support := by
  simp [support_ofSubtype]

/--
theorem `mem_support_of_mem_noncommProd_support` / 定理 `mem_support_of_mem_noncommProd_support`

English:
theorem mem_support_of_mem_noncommProd_support
  statement: {α β : Type*} [DecidableEq β] [Fintype β]
  proof: by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro a s ha ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    apply mt (Finset.mem_of_subset (support_mul_le _ _))
    rw [Finset.sup_eq_union]; rw [Finset.notMem_union]
    exact ⟨hs a (s.mem_insert_self a), ih (fun a ha => hs a (Finset.mem_insert_of_mem ha))⟩

中文:
定理 mem_support_of_mem_noncommProd_support
  结论: {α β : 类型} [DecidableEq β] [有限类型 β]
  证明: by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro a s ha ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    apply mt (Finset.mem_of_subset (support_mul_le _ _))
    rw [Finset.sup_eq_union]; rw [Finset.notMem_union]
    exact ⟨hs a (s.mem_insert_self a), ih (fun a ha => hs a (Finset.mem_insert_of_mem ha))⟩

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_of_subset, Finset.noncommProd_insert_of_notMem, Finset.notMem_union, Finset.sup_eq_union, classical, contrapose, mem_insert_of_mem, mem_insert_self, mem_of_subset, noncommProd_insert_of_notMem, notMem_union, revert, s.mem_insert_self, sup_eq_union, support_mul_le
-/
theorem mem_support_of_mem_noncommProd_support {α β : Type*} [DecidableEq β] [Fintype β]
    {s : Finset α} {f : α -> Perm β}
    {comm : (s : Set α).Pairwise (Commute on f)} {x : β} (hx : x in (s.noncommProd f comm).support) :
    exists a in s, x in (f a).support := by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro a s ha ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    apply mt (Finset.mem_of_subset (support_mul_le _ _))
    rw [Finset.sup_eq_union]; rw [Finset.notMem_union]
    exact ⟨hs a (s.mem_insert_self a), ih (fun a ha => hs a (Finset.mem_insert_of_mem ha))⟩

/--
theorem `pow_apply_mem_support` / 定理 `pow_apply_mem_support`

English:
theorem pow_apply_mem_support
  given: {n : Nat} {x : α}
  statement: (f ^ n) x in f.support ↔ x in f.support
  proof: by
  simp only [mem_support, ne_eq, apply_pow_apply_eq_iff]

中文:
定理 pow_apply_mem_support
  条件: {n : 自然数} {x : α}
  结论: (f ^ n) x in f.support ↔ x in f.support
  证明: by
  simp only [mem_support, ne_eq, apply_pow_apply_eq_iff]

Depends on / 依赖: apply_pow_apply_eq_iff, mem_support, ne_eq
-/
theorem pow_apply_mem_support {n : Nat} {x : α} : (f ^ n) x in f.support ↔ x in f.support := by
  simp only [mem_support, ne_eq, apply_pow_apply_eq_iff]

/--
theorem `zpow_apply_mem_support` / 定理 `zpow_apply_mem_support`

English:
theorem zpow_apply_mem_support
  given: {n : Int} {x : α}
  statement: (f ^ n) x in f.support ↔ x in f.support
  proof: by
  simp only [mem_support, ne_eq, apply_zpow_apply_eq_iff]

中文:
定理 zpow_apply_mem_support
  条件: {n : 整数} {x : α}
  结论: (f ^ n) x in f.support ↔ x in f.support
  证明: by
  simp only [mem_support, ne_eq, apply_zpow_apply_eq_iff]

Depends on / 依赖: apply_zpow_apply_eq_iff, mem_support, ne_eq
-/
theorem zpow_apply_mem_support {n : Int} {x : α} : (f ^ n) x in f.support ↔ x in f.support := by
  simp only [mem_support, ne_eq, apply_zpow_apply_eq_iff]

/--
theorem `pow_eq_on_of_mem_support` / 定理 `pow_eq_on_of_mem_support`

English:
theorem pow_eq_on_of_mem_support
  given: (h : forall x in f.support inter g.support, f x = g x) (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ]; rw [mul_apply]; rw [pow_succ]; rw [mul_apply]; rw [h _ hx]; rw [hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]

中文:
定理 pow_eq_on_of_mem_support
  条件: (h : 对任意 x in f.support inter g.support, f x = g x) (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ]; rw [mul_apply]; rw [pow_succ]; rw [mul_apply]; rw [h _ hx]; rw [hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]

Depends on / 依赖: apply_mem_support, mem_inter, mul_apply, pow_succ
-/
theorem pow_eq_on_of_mem_support (h : forall x in f.support inter g.support, f x = g x) (k : Nat) :
    forall x in f.support inter g.support, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ]; rw [mul_apply]; rw [pow_succ]; rw [mul_apply]; rw [h _ hx]; rw [hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]

/--
theorem `disjoint_iff_disjoint_support` / 定理 `disjoint_iff_disjoint_support`

English:
theorem disjoint_iff_disjoint_support
  statement: Disjoint f g ↔ _root_.Disjoint f.support g.support
  proof: by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]

中文:
定理 disjoint_iff_disjoint_support
  结论: Disjoint f g ↔ _root_.Disjoint f.support g.support
  证明: by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]

Depends on / 依赖: Finset, Finset.ext_iff, disjoint_iff, disjoint_iff_eq_or_eq, ext_iff, imp_iff_not_or
-/
theorem disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.Disjoint f.support g.support := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]

/--
theorem `Disjoint.disjoint_support` / 定理 `Disjoint.disjoint_support`

English:
theorem Disjoint.disjoint_support
  given: (h : Disjoint f g)
  statement: _root_.Disjoint f.support g.support
  proof: disjoint_iff_disjoint_support.1 h

中文:
定理 Disjoint.disjoint_support
  条件: (h : Disjoint f g)
  结论: _root_.Disjoint f.support g.support
  证明: disjoint_iff_disjoint_support.1 h

Depends on / 依赖: disjoint_iff_disjoint_support
-/
theorem Disjoint.disjoint_support (h : Disjoint f g) : _root_.Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h

/--
theorem `Disjoint.support_mul` / 定理 `Disjoint.support_mul`

English:
theorem Disjoint.support_mul
  given: (h : Disjoint f g)
  statement: (f * g).support = f.support union g.support
  proof: by
  refine le_antisymm (support_mul_le _ _) fun a => ?_
  rw [mem_union]; rw [mem_support]; rw [mem_support]; rw [mem_support]; rw [mul_apply]; rw [← not_and_or]; rw [not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩

中文:
定理 Disjoint.support_mul
  条件: (h : Disjoint f g)
  结论: (f * g).support = f.support union g.support
  证明: by
  refine le_antisymm (support_mul_le _ _) fun a => ?_
  rw [mem_union]; rw [mem_support]; rw [mem_support]; rw [mem_support]; rw [mul_apply]; rw [← not_and_or]; rw [not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩

Depends on / 依赖: apply_eq_iff_eq, congr_arg, f.apply_eq_iff_eq.mp, h.trans, hf.symm, le_antisymm, mem_support, mem_union, mul_apply, not_and_or, not_imp_not, support_mul_le, symm.trans
-/
theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).support = f.support union g.support := by
  refine le_antisymm (support_mul_le _ _) fun a => ?_
  rw [mem_union]; rw [mem_support]; rw [mem_support]; rw [mem_support]; rw [mul_apply]; rw [← not_and_or]; rw [not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩

/--
theorem `support_prod_of_pairwise_disjoint` / 定理 `support_prod_of_pairwise_disjoint`

English:
theorem support_prod_of_pairwise_disjoint
  given: (l : List (Perm α)) (h : l.Pairwise Disjoint)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]

中文:
定理 support_prod_of_pairwise_disjoint
  条件: (l : 列表 (置换 α)) (h : l.两两 Disjoint)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]

Depends on / 依赖: Disjoint, List.pairwise_cons, disjoint_prod_right, h.left, h.right, pairwise_cons, support_mul, this.support_mul, tl.prod
-/
theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.support = (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]

/--
theorem `support_noncommProd` / 定理 `support_noncommProd`

English:
theorem support_noncommProd
  statement: {ι : Type*} {k : ι -> Perm α} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j => Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.support_mul]; rw [hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

中文:
定理 support_noncommProd
  结论: {ι : 类型} {k : ι -> 置换 α} {s : 有限集 ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j => Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.support_mul]; rw [hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

Depends on / 依赖: Disjoint, Equiv.Perm.Disjoint.support_mul, Finset, Finset.biUnion_insert, Finset.coe_insert, Finset.induction_on, Finset.noncommProd_insert_of_notMem, Pairwise, Set.mem_insert_iff, Set.subset_insert, biUnion_insert, classical, coe_insert, disjoint_noncommProd_right, hs.mono, induction_on, insert, mem_insert_iff, ne_of_mem_of_not_mem, noncommProd_insert_of_notMem
-/
theorem support_noncommProd {ι : Type*} {k : ι -> Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j => Disjoint (k i) (k j)) :
    (s.noncommProd k (hs.imp (fun _ _ => Perm.Disjoint.commute))).support =
      s.biUnion fun i => (k i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j => Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.support_mul]; rw [hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

/--
theorem `support_prod_le` / 定理 `support_prod_le`

English:
theorem support_prod_le
  given: (l : List (Perm α))
  statement: l.prod.support <= (l.map support).foldr (· ⊔ ·) ⊥
  proof: by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.foldr_cons]
    refine (support_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

中文:
定理 support_prod_le
  条件: (l : 列表 (置换 α))
  结论: l.乘积.support <= (l.map support).foldr (· ⊔ ·) ⊥
  证明: by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.foldr_cons]
    refine (support_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

Depends on / 依赖: List.foldr_cons, List.map_cons, List.prod_cons, foldr_cons, le_rfl, map_cons, prod_cons, sup_le_sup, support_mul_le, tl.prod
-/
theorem support_prod_le (l : List (Perm α)) : l.prod.support <= (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.foldr_cons]
    refine (support_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

/--
theorem `support_zpow_le` / 定理 `support_zpow_le`

English:
theorem support_zpow_le
  given: (σ : Perm α) (n : Int)
  statement: (σ ^ n).support <= σ.support
  proof: fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]

中文:
定理 support_zpow_le
  条件: (σ : 置换 α) (n : 整数)
  结论: (σ ^ n).support <= σ.support
  证明: fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
-/
theorem support_zpow_le (σ : Perm α) (n : Int) : (σ ^ n).support <= σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
/--
theorem `support_swap` / 定理 `support_swap`

English:
theorem support_swap
  given: {x y : α} (h : x != y)
  statement: support (swap x y) = {x, y}
  proof: by
  grind [support]

中文:
定理 support_swap
  条件: {x y : α} (h : x != y)
  结论: support (swap x y) = {x, y}
  证明: by
  grind [support]

Depends on / 依赖: support
-/
theorem support_swap {x y : α} (h : x != y) : support (swap x y) = {x, y} := by
  grind [support]

/--
theorem `support_swap_iff` / 定理 `support_swap_iff`

English:
theorem support_swap_iff
  given: (x y : α)
  statement: support (swap x y) = {x, y} ↔ x != y
  proof: by
  refine ⟨fun h => ?_, fun h => support_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h

中文:
定理 support_swap_iff
  条件: (x y : α)
  结论: support (swap x y) = {x, y} ↔ x != y
  证明: by
  refine ⟨fun h => ?_, fun h => support_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h

Depends on / 依赖: Finset, Finset.ext_iff, ext_iff, support_swap
-/
theorem support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x != y := by
  refine ⟨fun h => ?_, fun h => support_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h

/--
theorem `support_swap_mul_swap` / 定理 `support_swap_mul_swap`

English:
theorem support_swap_mul_swap
  given: {x y z : α} (h : List.Nodup [x, y, z])
  proof: by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert! support_mul_le (swap x y) (swap y z) using 1
    rw [support_swap h.left.left]; rw [support_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

中文:
定理 support_swap_mul_swap
  条件: {x y z : α} (h : 列表.Nodup [x, y, z])
  证明: by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert! support_mul_le (swap x y) (swap y z) using 1
    rw [support_swap h.left.left]; rw [support_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

Depends on / 依赖: Finset, Finset.union_singleton, List.mem_cons, List.nodup_cons, List.nodup_nil, List.not_mem_nil, and_self_iff, and_true, convert, h.left.left, h.left.left.symm, h.left.right.left.symm, h.left.right.symm, h.right.left, le_antisymm, mem_cons, mem_insert, mem_singleton, nodup_cons, nodup_nil
-/
theorem support_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert! support_mul_le (swap x y) (swap y z) using 1
    rw [support_swap h.left.left]; rw [support_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

/--
theorem `support_swap_mul_ge_support_sdiff` / 定理 `support_swap_mul_ge_support_sdiff`

English:
theorem support_swap_mul_ge_support_sdiff
  given: (f : Perm α) (x y : α)
  proof: by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff]; rw [swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := support_swap_mul_ge_support_sdiff

中文:
定理 support_swap_mul_ge_support_sdiff
  条件: (f : 置换 α) (x y : α)
  证明: by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff]; rw [swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := support_swap_mul_ge_support_sdiff

Depends on / 依赖: Function, Function.comp_apply, Perm.coe_mul, and_imp, coe_mul, comp_apply, mem_insert, mem_sdiff, mem_singleton, mem_support, swap_apply_eq_iff, swap_apply_of_ne_of_ne
-/
theorem support_swap_mul_ge_support_sdiff (f : Perm α) (x y : α) :
    f.support \ {x, y} <= (swap x y * f).support := by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff]; rw [swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := support_swap_mul_ge_support_sdiff

/--
theorem `support_swap_mul_eq` / 定理 `support_swap_mul_eq`

English:
theorem support_swap_mul_eq
  given: (f : Perm α) (x : α) (h : f (f x) != x)
  proof: by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_support.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

中文:
定理 support_swap_mul_eq
  条件: (f : 置换 α) (x : α) (h : f (f x) != x)
  证明: by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_support.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

Depends on / 依赖: Ne.symm, erase_eq_of_notMem, f.injective.ne, injective, notMem_support, notMem_support.mpr, pull_end, sdiff_singleton_eq_erase, swap_apply_of_ne_of_ne
-/
theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) != x) :
    (swap x (f x) * f).support = f.support \ {x} := by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_support.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

/--
theorem `mem_support_swap_mul_imp_mem_support_ne` / 定理 `mem_support_swap_mul_imp_mem_support_ne`

English:
theorem mem_support_swap_mul_imp_mem_support_ne
  given: {x y : α} (hy : y in support (swap x (f x) * f))
  proof: by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

omit [Fintype α] in

中文:
定理 mem_support_swap_mul_imp_mem_support_ne
  条件: {x y : α} (hy : y in support (swap x (f x) * f))
  证明: by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

omit [Fintype α] in

Depends on / 依赖: eq_iff, f.injective.eq_iff, injective, mem_support, mul_apply, swap_apply_def
-/
theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y in support (swap x (f x) * f)) :
    y in support f ∧ y != x := by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

omit [Fintype α] in
/--
theorem `disjoint_swap_swap` / 定理 `disjoint_swap_swap`

English:
theorem disjoint_swap_swap
  given: {x y z t : α} (h : [x, y, z, t].Nodup)
  proof: by
  intro; grind

中文:
定理 disjoint_swap_swap
  条件: {x y z t : α} (h : [x, y, z, t].Nodup)
  证明: by
  intro; grind
-/
theorem disjoint_swap_swap {x y z t : α} (h : [x, y, z, t].Nodup) :
    Disjoint (swap x y) (swap z t) := by
  intro; grind

/--
theorem `Disjoint.mem_imp` / 定理 `Disjoint.mem_imp`

English:
theorem Disjoint.mem_imp
  given: (h : Disjoint f g) {x : α} (hx : x in f.support)
  statement: x ∉ g.support
  proof: disjoint_left.mp h.disjoint_support hx

中文:
定理 Disjoint.mem_imp
  条件: (h : Disjoint f g) {x : α} (hx : x in f.support)
  结论: x ∉ g.support
  证明: disjoint_left.mp h.disjoint_support hx

Depends on / 依赖: disjoint_left, disjoint_left.mp, disjoint_support, h.disjoint_support
-/
theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x in f.support) : x ∉ g.support :=
  disjoint_left.mp h.disjoint_support hx

/--
theorem `eq_on_support_mem_disjoint` / 定理 `eq_on_support_mem_disjoint`

English:
theorem eq_on_support_mem_disjoint
  given: {l : List (Perm α)} (h : f in l) (hl : l.Pairwise Disjoint)
  proof: by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_support]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx

中文:
定理 eq_on_support_mem_disjoint
  条件: {l : 列表 (置换 α)} (h : f in l) (hl : l.两两 Disjoint)
  证明: by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_support]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx

Depends on / 依赖: List.mem_cons, List.pairwise_cons, List.prod_cons, disjoint_prod_right, eq_comm, hl.left, hl.right, mem_cons, mem_imp, mul_apply, notMem_support, notMem_support.mp, pairwise_cons, prod_cons, symm.mem_imp
-/
theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f in l) (hl : l.Pairwise Disjoint) :
    forall x in f.support, f x = l.prod x := by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_support]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx

/--
theorem `Disjoint.mono` / 定理 `Disjoint.mono`

English:
theorem Disjoint.mono
  statement: {x y : Perm α} (h : Disjoint f g) (hf : x.support <= f.support)
  proof: by
  rw [disjoint_iff_disjoint_support] at h ⊢
  exact h.mono hf hg

中文:
定理 Disjoint.mono
  结论: {x y : 置换 α} (h : Disjoint f g) (hf : x.support <= f.support)
  证明: by
  rw [disjoint_iff_disjoint_support] at h ⊢
  exact h.mono hf hg

Depends on / 依赖: disjoint_iff_disjoint_support, h.mono
-/
theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support <= f.support)
    (hg : y.support <= g.support) : Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h ⊢
  exact h.mono hf hg

/--
theorem `support_le_prod_of_mem` / 定理 `support_le_prod_of_mem`

English:
theorem support_le_prod_of_mem
  given: {l : List (Perm α)} (h : f in l) (hl : l.Pairwise Disjoint)
  proof: by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

中文:
定理 support_le_prod_of_mem
  条件: {l : 列表 (置换 α)} (h : f in l) (hl : l.两两 Disjoint)
  证明: by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

Depends on / 依赖: eq_on_support_mem_disjoint, mem_support
-/
theorem support_le_prod_of_mem {l : List (Perm α)} (h : f in l) (hl : l.Pairwise Disjoint) :
    f.support <= l.prod.support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β -> Prop} [DecidablePred p]

@[simp]
/--
theorem `support_extend_domain` / 定理 `support_extend_domain`

English:
theorem support_extend_domain
  given: (f : α ≃ Subtype p) {g : Perm α}
  proof: by
  ext b
  simp only [mem_map, Ne,
    mem_support]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)

中文:
定理 support_extend_domain
  条件: (f : α ≃ 子类型 p) {g : 置换 α}
  证明: by
  ext b
  simp only [mem_map, Ne,
    mem_support]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)

Depends on / 依赖: Subtype, Subtype.prop, asEmbedding_apply, extendDomain_apply_not_subtype, extendDomain_apply_subtype, false_iff, mem_map, mem_support, not_and, not_exists, not_true
-/
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = g.support.map f.asEmbedding := by
  ext b
  simp only [mem_map, Ne,
    mem_support]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)

/--
theorem `card_support_extend_domain` / 定理 `card_support_extend_domain`

English:
theorem card_support_extend_domain
  given: (f : α ≃ Subtype p) {g : Perm α}
  proof: by simp

中文:
定理 card_support_extend_domain
  条件: (f : α ≃ 子类型 p) {g : 置换 α}
  证明: by simp
-/
theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    #(g.extendDomain f).support = #g.support := by simp

end ExtendDomain

section Card

/--
theorem `card_support_eq_zero` / 定理 `card_support_eq_zero`

English:
theorem card_support_eq_zero
  given: {f : Perm α}
  statement: #f.support = 0 ↔ f = 1
  proof: by
  rw [Finset.card_eq_zero]; rw [support_eq_empty_iff]

中文:
定理 card_support_eq_zero
  条件: {f : 置换 α}
  结论: #f.support = 0 ↔ f = 1
  证明: by
  rw [Finset.card_eq_zero]; rw [support_eq_empty_iff]

Depends on / 依赖: Finset, Finset.card_eq_zero, card_eq_zero, support_eq_empty_iff
-/
theorem card_support_eq_zero {f : Perm α} : #f.support = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero]; rw [support_eq_empty_iff]

/--
theorem `one_lt_card_support_of_ne_one` / 定理 `one_lt_card_support_of_ne_one`

English:
theorem one_lt_card_support_of_ne_one
  given: {f : Perm α} (h : f != 1)
  statement: 1 < #f.support
  proof: by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h

中文:
定理 one_lt_card_support_of_ne_one
  条件: {f : 置换 α} (h : f != 1)
  结论: 1 < #f.support
  证明: by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h

Depends on / 依赖: TensorProduct, TensorProduct.leftModule, apply_eq_iff_eq, contrapose, leftModule, mem_support, not_or, one_lt_card_iff, or_self_iff, simp_rw, specialize
-/
theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f != 1) : 1 < #f.support := by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h

/--
theorem `card_support_ne_one` / 定理 `card_support_ne_one`

English:
theorem card_support_ne_one
  given: (f : Perm α)
  statement: #f.support != 1
  proof: by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)

@[simp]

中文:
定理 card_support_ne_one
  条件: (f : 置换 α)
  结论: #f.support != 1
  证明: by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)

@[simp]

Depends on / 依赖: card_support_eq_zero, card_support_eq_zero.mpr, ne_of_eq_of_ne, ne_of_gt, one_lt_card_support_of_ne_one, zero_ne_one
-/
theorem card_support_ne_one (f : Perm α) : #f.support != 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)

@[simp]
/--
theorem `card_support_le_one` / 定理 `card_support_le_one`

English:
theorem card_support_le_one
  given: {f : Perm α}
  statement: #f.support <= 1 ↔ f = 1
  proof: by
  rw [le_iff_lt_or_eq]; rw [Nat.lt_succ_iff]; rw [Nat.le_zero]; rw [card_support_eq_zero]; rw [or_iff_not_imp_right]; rw [imp_iff_right f.card_support_ne_one]

中文:
定理 card_support_le_one
  条件: {f : 置换 α}
  结论: #f.support <= 1 ↔ f = 1
  证明: by
  rw [le_iff_lt_or_eq]; rw [Nat.lt_succ_iff]; rw [Nat.le_zero]; rw [card_support_eq_zero]; rw [or_iff_not_imp_right]; rw [imp_iff_right f.card_support_ne_one]

Depends on / 依赖: Nat.le_zero, Nat.lt_succ_iff, card_support_eq_zero, card_support_ne_one, f.card_support_ne_one, imp_iff_right, le_iff_lt_or_eq, le_zero, lt_succ_iff, or_iff_not_imp_right
-/
theorem card_support_le_one {f : Perm α} : #f.support <= 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq]; rw [Nat.lt_succ_iff]; rw [Nat.le_zero]; rw [card_support_eq_zero]; rw [or_iff_not_imp_right]; rw [imp_iff_right f.card_support_ne_one]

/--
theorem `two_le_card_support_of_ne_one` / 定理 `two_le_card_support_of_ne_one`

English:
theorem two_le_card_support_of_ne_one
  given: {f : Perm α} (h : f != 1)
  statement: 2 <= #f.support
  proof: one_lt_card_support_of_ne_one h

中文:
定理 two_le_card_support_of_ne_one
  条件: {f : 置换 α} (h : f != 1)
  结论: 2 <= #f.support
  证明: one_lt_card_support_of_ne_one h

Depends on / 依赖: one_lt_card_support_of_ne_one
-/
theorem two_le_card_support_of_ne_one {f : Perm α} (h : f != 1) : 2 <= #f.support :=
  one_lt_card_support_of_ne_one h

/--
theorem `card_support_swap_mul` / 定理 `card_support_swap_mul`

English:
theorem card_support_swap_mul
  given: {f : Perm α} {x : α} (hx : f x != x)
  proof: Finset.card_lt_card
    ⟨fun _ hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

中文:
定理 card_support_swap_mul
  条件: {f : 置换 α} {x : α} (hx : f x != x)
  证明: Finset.card_lt_card
    ⟨fun _ hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

Depends on / 依赖: Finset, Finset.card_lt_card, absurd, card_lt_card, mem_support, mem_support_swap_mul_imp_mem_support_ne
-/
theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x != x) :
    #(swap x (f x) * f).support < #f.support :=
  Finset.card_lt_card
    ⟨fun _ hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_support_swap` / 定理 `card_support_swap`

English:
theorem card_support_swap
  given: {x y : α} (hxy : x != y)
  statement: #(swap x y).support = 2
  proof: show #(swap x y).support = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
congr_arg card by simp [support_swap hxy, *, Finset.ext_iff]

@[simp]

中文:
定理 card_support_swap
  条件: {x y : α} (hxy : x != y)
  结论: #(swap x y).support = 2
  证明: show #(swap x y).support = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
congr_arg card by simp [support_swap hxy, *, Finset.ext_iff]

@[simp]

Depends on / 依赖: Finset, Finset.ext_iff, congr_arg, ext_iff, support, support_swap
-/
theorem card_support_swap {x y : α} (hxy : x != y) : #(swap x y).support = 2 :=
  show #(swap x y).support = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
congr_arg card by simp [support_swap hxy, *, Finset.ext_iff]

@[simp]
/--
theorem `card_support_eq_two` / 定理 `card_support_eq_two`

English:
theorem card_support_eq_two
  given: {f : Perm α}
  statement: #f.support = 2 ↔ IsSwap f
  proof: by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : forall b, f b != b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha]; rw [swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy

中文:
定理 card_support_eq_two
  条件: {f : 置换 α}
  结论: #f.support = 2 ↔ IsSwap f
  证明: by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : forall b, f b != b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha]; rw [swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy

Depends on / 依赖: apply_eq_iff_eq, card_eq_one, card_eq_succ, f.apply_eq_iff_eq.mp, mem_insert, mem_singleton, mem_support, not_not, not_not.mpr, not_or, not_or.mp, swap_apply_of_ne_of_ne
-/
theorem card_support_eq_two {f : Perm α} : #f.support = 2 ↔ IsSwap f := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : forall b, f b != b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha]; rw [swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy

/--
theorem `Disjoint.card_support_mul` / 定理 `Disjoint.card_support_mul`

English:
theorem Disjoint.card_support_mul
  given: (h : Disjoint f g)
  proof: by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support

中文:
定理 Disjoint.card_support_mul
  条件: (h : Disjoint f g)
  证明: by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support

Depends on / 依赖: Finset, Finset.card_union_of_disjoint, card_union_of_disjoint, disjoint_support, h.disjoint_support, h.support_mul, support_mul
-/
theorem Disjoint.card_support_mul (h : Disjoint f g) :
    #(f * g).support = #f.support + #g.support := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support

/--
theorem `card_support_prod_list_of_pairwise_disjoint` / 定理 `card_support_prod_list_of_pairwise_disjoint`

English:
theorem card_support_prod_list_of_pairwise_disjoint
  given: {l : List (Perm α)} (h : l.Pairwise Disjoint)
  proof: by
  induction l with
  | nil => exact card_support_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.sum_cons]; rw [← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul

中文:
定理 card_support_prod_list_of_pairwise_disjoint
  条件: {l : 列表 (置换 α)} (h : l.两两 Disjoint)
  证明: by
  induction l with
  | nil => exact card_support_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.sum_cons]; rw [← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul

Depends on / 依赖: List.map_cons, List.pairwise_cons, List.prod_cons, List.sum_cons, card_support_eq_zero, card_support_eq_zero.mpr, card_support_mul, disjoint_prod_right, map_cons, pairwise_cons, prod_cons, sum_cons
-/
theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    #l.prod.support = (l.map (card ∘ support)).sum := by
  induction l with
  | nil => exact card_support_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.sum_cons]; rw [← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul

end Card

end support

@[simp]
/--
theorem `support_subtypePerm` / 定理 `support_subtypePerm`

English:
theorem support_subtypePerm
  given: [DecidableEq α] {s : Finset α} (f : Perm α) (h)
  proof: by
  ext; simp [Subtype.ext_iff]

中文:
定理 support_subtypePerm
  条件: [DecidableEq α] {s : 有限集 α} (f : 置换 α) (h)
  证明: by
  ext; simp [Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem support_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).support = ({x | f x != x} : Finset s) := by
  ext; simp [Subtype.ext_iff]

end Equiv.Perm

section FixedPoints

namespace Equiv.Perm
/-!
### Fixed points
-/

variable {α : Type*}

/--
theorem `fixed_point_card_lt_of_ne_one` / 定理 `fixed_point_card_lt_of_ne_one`

English:
theorem fixed_point_card_lt_of_ne_one
  given: [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ != 1)
  proof: by
  rw [Nat.lt_sub_iff_add_lt]; rw [← Nat.lt_sub_iff_add_lt']; rw [← Finset.card_compl]; rw [Finset.compl_filter]
  exact one_lt_card_support_of_ne_one h

中文:
定理 fixed_point_card_lt_of_ne_one
  条件: [DecidableEq α] [有限类型 α] {σ : 置换 α} (h : σ != 1)
  证明: by
  rw [Nat.lt_sub_iff_add_lt]; rw [← Nat.lt_sub_iff_add_lt']; rw [← Finset.card_compl]; rw [Finset.compl_filter]
  exact one_lt_card_support_of_ne_one h

Depends on / 依赖: Finset, Finset.card_compl, Finset.compl_filter, Nat.lt_sub_iff_add_lt, card_compl, compl_filter, lt_sub_iff_add_lt, one_lt_card_support_of_ne_one
-/
theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ != 1) :
    #{x | σ x = x} < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt]; rw [← Nat.lt_sub_iff_add_lt']; rw [← Finset.card_compl]; rw [Finset.compl_filter]
  exact one_lt_card_support_of_ne_one h

end Equiv.Perm

end FixedPoints

section Conjugation

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
/--
theorem `support_conj` / 定理 `support_conj`

English:
theorem support_conj
  statement: (σ * τ * σ⁻¹).support = τ.support.map σ.toEmbedding
  proof: by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_support,
    Equiv.eq_symm_apply, inv_def]

中文:
定理 support_conj
  结论: (σ * τ * σ⁻¹).support = τ.support.map σ.toEmbedding
  证明: by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_support,
    Equiv.eq_symm_apply, inv_def]

Depends on / 依赖: Equiv.eq_symm_apply, Function, Function.comp_apply, Perm.coe_mul, Perm.mem_support, coe_mul, comp_apply, eq_symm_apply, inv_def, mem_map_equiv, mem_support
-/
theorem support_conj : (σ * τ * σ⁻¹).support = τ.support.map σ.toEmbedding := by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_support,
    Equiv.eq_symm_apply, inv_def]

/--
theorem `card_support_conj` / 定理 `card_support_conj`

English:
theorem card_support_conj
  statement: #(σ * τ * σ⁻¹).support = #τ.support
  proof: by simp

中文:
定理 card_support_conj
  结论: #(σ * τ * σ⁻¹).support = #τ.support
  证明: by simp
-/
theorem card_support_conj : #(σ * τ * σ⁻¹).support = #τ.support := by simp

end Equiv.Perm

end Conjugation
