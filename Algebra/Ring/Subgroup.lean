/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Algebra.Module.Defs

/-!
# Additive subgroups of rings
-/

@[expose] public section

open scoped Pointwise

variable {R M : Type*}

namespace AddSubgroup
section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R]

/-- For additive subgroups `S` and `T` of a ring, the product of `S` and `T` as submonoids
is automatically a subgroup, which we define as the product of `S` and `T` as subgroups. -/
@[instance_reducible]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : Mul (AddSubgroup R) where
  body: { __ := M.toAddSubmonoid * N.toAddSubmonoid
    neg_mem' := fun h => AddSubmonoid.mul_induction_on h
      (fun m hm n hn => by rw [← neg_mul]; exact AddSubmonoid.mul_mem_mul (M.neg_mem hm) hn)
      fun r₁ r₂ h₁ h₂ => by rw [neg_add]; exact (M.1 * N.1).add_mem h₁ h₂ }

scoped[Pointwise] attribute [instance] AddSubgroup.mul

中文:
定义 mul
  签名: : 乘法 (加法子群 R) where
  定义体: { __ := M.toAddSubmonoid * N.toAddSubmonoid
    neg_mem' := fun h => AddSubmonoid.mul_induction_on h
      (fun m hm n hn => by rw [← neg_mul]; exact AddSubmonoid.mul_mem_mul (M.neg_mem hm) hn)
      fun r₁ r₂ h₁ h₂ => by rw [neg_add]; exact (M.1 * N.1).add_mem h₁ h₂ }

scoped[Pointwise] attribute [instance] AddSubgroup.mul
-/
protected def mul : Mul (AddSubgroup R) where
  mul M N :=
  { __ := M.toAddSubmonoid * N.toAddSubmonoid
    neg_mem' := fun h => AddSubmonoid.mul_induction_on h
      (fun m hm n hn => by rw [← neg_mul]; exact AddSubmonoid.mul_mem_mul (M.neg_mem hm) hn)
      fun r₁ r₂ h₁ h₂ => by rw [neg_add]; exact (M.1 * N.1).add_mem h₁ h₂ }

scoped[Pointwise] attribute [instance] AddSubgroup.mul

/--
lemma `mul_toAddSubmonoid` / 引理 `mul_toAddSubmonoid`

English:
lemma mul_toAddSubmonoid
  given: (M N : AddSubgroup R)
  proof: rfl

中文:
引理 mul_toAddSubmonoid
  条件: (M N : 加法子群 R)
  证明: rfl
-/
lemma mul_toAddSubmonoid (M N : AddSubgroup R) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

end NonUnitalNonAssocRing

section Semiring
variable [Semiring R] [AddCommGroup M] [Module R M]

/--
lemma `zero_smul` / 引理 `zero_smul`

English:
lemma zero_smul
  given: (s : AddSubgroup M)
  statement: (0 : R) • s = ⊥
  proof: by
  simp [eq_bot_iff_forall, pointwise_smul_def]

中文:
引理 zero_smul
  条件: (s : 加法子群 M)
  结论: (0 : R) • s = ⊥
  证明: by
  simp [eq_bot_iff_forall, pointwise_smul_def]
-/
@[simp] protected lemma zero_smul (s : AddSubgroup M) : (0 : R) • s = ⊥ := by
  simp [eq_bot_iff_forall, pointwise_smul_def]

end Semiring
end AddSubgroup
