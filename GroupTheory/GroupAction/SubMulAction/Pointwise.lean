/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise monoid structures on SubMulAction

This file provides `SubMulAction.Monoid` and weaker typeclasses, which show that `SubMulAction`s
inherit the same pointwise multiplications as sets.

To match `Submodule.idemSemiring`, we do not put these in the `Pointwise` locale.

-/

public section


open scoped Pointwise

variable {R M : Type*}

namespace SubMulAction

section One

variable [Monoid R] [MulAction R M] [One M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (SubMulAction R M)
  body: { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r _ ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

中文:
实例 :
  签名: 幺 (SubMul作用 R M)
  定义体: { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r _ ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

Depends on / 依赖: Set.range, carrier, mul_smul, smul_mem
-/
instance : One (SubMulAction R M) where
  one :=
    { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r _ ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M)
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ↑(1 : SubMul作用 R M) = 集合.range fun r : R => r • (1 : M)
  证明: rfl

@[simp]
-/
theorem coe_one : ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M) :=
  rfl

@[simp]
/--
theorem `mem_one` / 定理 `mem_one`

English:
theorem mem_one
  given: {x : M}
  statement: x in (1 : SubMulAction R M) ↔ exists r : R, r • (1 : M) = x
  proof: Iff.rfl

中文:
定理 mem_one
  条件: {x : M}
  结论: x in (1 : SubMul作用 R M) ↔ 存在 r : R, r • (1 : M) = x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_one {x : M} : x in (1 : SubMulAction R M) ↔ exists r : R, r • (1 : M) = x :=
  Iff.rfl

/--
theorem `subset_coe_one` / 定理 `subset_coe_one`

English:
theorem subset_coe_one
  statement: (1 : Set M) subseteq (1 : SubMulAction R M)
  proof: fun _ hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩

中文:
定理 subset_coe_one
  结论: (1 : 集合 M) subseteq (1 : SubMul作用 R M)
  证明: fun _ hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩
-/
theorem subset_coe_one : (1 : Set M) subseteq (1 : SubMulAction R M) := fun _ hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩

end One

section Mul

variable [Monoid R] [MulAction R M] [Mul M] [IsScalarTower R M M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (SubMulAction R M)
  body: { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r _ ⟨m₁, hm₁, m₂, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]

中文:
实例 :
  签名: 乘法 (SubMul作用 R M)
  定义体: { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r _ ⟨m₁, hm₁, m₂, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]

Depends on / 依赖: Set.image2, Set.mul_mem_mul, carrier, image2, mul_mem_mul, p.smul_mem, smul_mem, smul_mul_assoc
-/
instance : Mul (SubMulAction R M) where
  mul p q :=
    { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r _ ⟨m₁, hm₁, m₂, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (p q : SubMulAction R M)
  statement: ↑(p * q) = (p * q : Set M)
  proof: rfl

中文:
定理 coe_mul
  条件: (p q : SubMul作用 R M)
  结论: ↑(p * q) = (p * q : 集合 M)
  证明: rfl
-/
theorem coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M) :=
  rfl

/--
theorem `mem_mul` / 定理 `mem_mul`

English:
theorem mem_mul
  given: {p q : SubMulAction R M} {x : M}
  statement: x in p * q ↔ exists y in p, exists z in q, y * z = x
  proof: Set.mem_mul

中文:
定理 mem_mul
  条件: {p q : SubMul作用 R M} {x : M}
  结论: x in p * q ↔ 存在 y in p, 存在 z in q, y * z = x
  证明: Set.mem_mul

Depends on / 依赖: Set.mem_mul, mem_mul
-/
theorem mem_mul {p q : SubMulAction R M} {x : M} : x in p * q ↔ exists y in p, exists z in q, y * z = x :=
  Set.mem_mul

end Mul

section MulOneClass

variable [Monoid R] [MulAction R M] [MulOneClass M] [IsScalarTower R M M] [SMulCommClass R M M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulOneClass (SubMulAction R M)
  body: by
    ext x
    simp only [mem_mul, mem_one, mul_smul_comm, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext x
    simp only [mem_mul, mem_one, smul_mul_assoc, exists

中文:
实例 :
  签名: MulOne类 (SubMul作用 R M)
  定义体: by
    ext x
    simp only [mem_mul, mem_one, mul_smul_comm, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext x
    simp only [mem_mul, mem_one, smul_mul_assoc, exists

Depends on / 依赖: exists_exists_eq_and, mem_mul, mem_one, mul_one, mul_smul_comm, one_mul, one_smul, smul_mem, smul_mul_assoc
-/
instance : MulOneClass (SubMulAction R M) where
  mul_one a := by
    ext x
    simp only [mem_mul, mem_one, mul_smul_comm, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext x
    simp only [mem_mul, mem_one, smul_mul_assoc, exists_exists_eq_and, one_mul]
    refine ⟨?_, fun hx => ⟨1, x, hx, one_smul _ _⟩⟩
    rintro ⟨r, y, hy, rfl⟩
    exact smul_mem _ _ hy

end MulOneClass

section Semigroup

variable [Monoid R] [MulAction R M] [Semigroup M] [IsScalarTower R M M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semigroup (SubMulAction R M)
  body: SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

中文:
实例 :
  签名: 半群 (SubMul作用 R M)
  定义体: SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, mul_assoc
-/
instance : Semigroup (SubMulAction R M) where
  mul_assoc _ _ _ := SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

end Semigroup

section Monoid

variable [Monoid R] [MulAction R M] [Monoid M] [IsScalarTower R M M] [SMulCommClass R M M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (SubMulAction R M)
  body: { }

中文:
实例 :
  签名: 幺半群 (SubMul作用 R M)
  定义体: { }
-/
instance : Monoid (SubMulAction R M) := { }

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (p : SubMulAction R M)
  statement: forall {n : Nat} (_ : n != 0), ↑(p ^ n) = (p : Set M) ^ n

中文:
定理 coe_pow
  条件: (p : SubMul作用 R M)
  结论: 对任意 {n : 自然数} (_ : n != 0), ↑(p ^ n) = (p : 集合 M) ^ n
-/
theorem coe_pow (p : SubMulAction R M) : forall {n : Nat} (_ : n != 0), ↑(p ^ n) = (p : Set M) ^ n
  | 0, hn => (hn rfl).elim
  | 1, _ => by rw [pow_one, pow_one]
  | n + 2, _ => by
    rw [pow_succ _ (n + 1)]; rw [pow_succ _ (n + 1)]; rw [coe_mul]; rw [coe_pow _ n.succ_ne_zero]

/--
theorem `subset_coe_pow` / 定理 `subset_coe_pow`

English:
theorem subset_coe_pow
  given: (p : SubMulAction R M)
  statement: forall {n : Nat}, (p : Set M) ^ n subseteq ↑(p ^ n)

中文:
定理 subset_coe_pow
  条件: (p : SubMul作用 R M)
  结论: 对任意 {n : 自然数}, (p : 集合 M) ^ n subseteq ↑(p ^ n)
-/
theorem subset_coe_pow (p : SubMulAction R M) : forall {n : Nat}, (p : Set M) ^ n subseteq ↑(p ^ n)
  | 0 => by
    rw [pow_zero]; rw [pow_zero]
    exact subset_coe_one
  | n + 1 => by rw [← Nat.succ_eq_add_one, coe_pow _ n.succ_ne_zero]

end Monoid

end SubMulAction
