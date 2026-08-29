/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Ring.Subring.Defs

/-! # Subrings invariant under an action

If a monoid acts on a ring via a `MulSemiringAction`, then `IsInvariantSubring` is
a predicate on subrings asserting that the subring is fixed elementwise by the
action.

-/

@[expose] public section

assert_not_exists RelIso

section Ring

variable (M R : Type*) [Monoid M] [Ring R] [MulSemiringAction M R]
variable (S : Subring R)

open MulAction

variable {R}

/--
Definition of `IsInvariantSubring` / `IsInvariantSubring` 的定义

English:
class IsInvariantSubring
  parameters: : Prop where
  axioms and operations (1):
    - smul_mem : forall (m : M) {x : R}, x in S -> m • x in S

中文:
类 是不变子环
  参数: : 命题 where
  公理与运算 (1 个):
    - smul_mem : 对任意 (m : M) {x : R}, x in S -> m • x in S
-/
class IsInvariantSubring : Prop where
  smul_mem : forall (m : M) {x : R}, x in S -> m • x in S

/--
Instance `IsInvariantSubring.toMulSemiringAction` / 实例 `IsInvariantSubring.toMulSemiringAction`

English:
instance IsInvariantSubring.toMulSemiringAction
  signature: [IsInvariantSubring M S]
  body: ⟨m • ↑x, IsInvariantSubring.smul_mem m x.2⟩
one_smul s := Subtype.ext one_smul M (s : R)
mul_smul m₁ m₂ s := Subtype.ext mul_smul m₁ m₂ (s : R)
smul_add m s₁ s₂ := Subtype.ext smul_add m (s₁ : R) (s₂ : R)
smul_zero m := Subtype.ext smul_zero m
smul_one m := Subtype.ext smul_one m
smul_mul m s₁ s₂ := Subtype.ext smul_mul' m (s₁ : R) (s₂ : R)

中文:
实例 是不变子环.toMulSemiringAction
  签名: [是不变子环 M S]
  定义体: ⟨m • ↑x, IsInvariantSubring.smul_mem m x.2⟩
one_smul s := Subtype.ext one_smul M (s : R)
mul_smul m₁ m₂ s := Subtype.ext mul_smul m₁ m₂ (s : R)
smul_add m s₁ s₂ := Subtype.ext smul_add m (s₁ : R) (s₂ : R)
smul_zero m := Subtype.ext smul_zero m
smul_one m := Subtype.ext smul_one m
smul_mul m s₁ s₂ := Subtype.ext smul_mul' m (s₁ : R) (s₂ : R)

Depends on / 依赖: IsInvariantSubring, IsInvariantSubring.smul_mem, smul_mem
-/
instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • ↑x, IsInvariantSubring.smul_mem m x.2⟩
one_smul s := Subtype.ext one_smul M (s : R)
mul_smul m₁ m₂ s := Subtype.ext mul_smul m₁ m₂ (s : R)
smul_add m s₁ s₂ := Subtype.ext smul_add m (s₁ : R) (s₂ : R)
smul_zero m := Subtype.ext smul_zero m
smul_one m := Subtype.ext smul_one m
smul_mul m s₁ s₂ := Subtype.ext smul_mul' m (s₁ : R) (s₂ : R)

end Ring

section

variable (M : Type*) [Monoid M]
variable {R' : Type*} [Ring R'] [MulSemiringAction M R']
variable (U : Subring R') [IsInvariantSubring M U]

/--
Definition of `IsInvariantSubring.subtypeHom` / `IsInvariantSubring.subtypeHom` 的定义

English:
definition IsInvariantSubring.subtypeHom
  signature: : U ->+*[M] R'
  body: { U.subtype with map_smul' := fun _ _ => rfl }

@[simp]

中文:
定义 是不变子环.subtypeHom
  签名: : U ->+*[M] R'
  定义体: { U.subtype with map_smul' := fun _ _ => rfl }

@[simp]

Depends on / 依赖: U.subtype, map_smul, subtype
-/
def IsInvariantSubring.subtypeHom : U ->+*[M] R' :=
  { U.subtype with map_smul' := fun _ _ => rfl }

@[simp]
/--
theorem `IsInvariantSubring.coe_subtypeHom` / 定理 `IsInvariantSubring.coe_subtypeHom`

English:
theorem IsInvariantSubring.coe_subtypeHom
  proof: rfl

@[simp]

中文:
定理 是不变子环.coe_subtypeHom
  证明: rfl

@[simp]
-/
theorem IsInvariantSubring.coe_subtypeHom :
    (IsInvariantSubring.subtypeHom M U : U -> R') = Subtype.val := rfl

@[simp]
/--
theorem `IsInvariantSubring.coe_subtypeHom'` / 定理 `IsInvariantSubring.coe_subtypeHom'`

English:
theorem IsInvariantSubring.coe_subtypeHom'
  proof: rfl

中文:
定理 是不变子环.coe_subtypeHom'
  证明: rfl
-/
theorem IsInvariantSubring.coe_subtypeHom' :
    ((IsInvariantSubring.subtypeHom M U) : U ->+* R') = U.subtype := rfl

end
