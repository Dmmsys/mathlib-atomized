/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.Subring.Pointwise

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/

@[expose] public section


namespace Subalgebra

section Pointwise

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/--
theorem `mul_toSubmodule_le` / 定理 `mul_toSubmodule_le`

English:
theorem mul_toSubmodule_le
  given: (S T : Subalgebra R A)
  proof: by
  rw [Submodule.mul_le]
  intro y hy z hz
  simp only [mem_toSubmodule]
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

中文:
定理 mul_toSubmodule_le
  条件: (S T : Subalgebra R A)
  证明: by
  rw [Submodule.mul_le]
  intro y hy z hz
  simp only [mem_toSubmodule]
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

Depends on / 依赖: Algebra, Algebra.mem_sup_left, Algebra.mem_sup_right, Submodule, Submodule.mul_le, mem_sup_left, mem_sup_right, mem_toSubmodule, mul_le, mul_mem
-/
theorem mul_toSubmodule_le (S T : Subalgebra R A) :
    Subalgebra.toSubmodule S * Subalgebra.toSubmodule T <= Subalgebra.toSubmodule (S ⊔ T) := by
  rw [Submodule.mul_le]
  intro y hy z hz
  simp only [mem_toSubmodule]
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

/-- As submodules, subalgebras are idempotent. -/
@[simp]
/--
theorem `isIdempotentElem_toSubmodule` / 定理 `isIdempotentElem_toSubmodule`

English:
theorem isIdempotentElem_toSubmodule
  given: (S : Subalgebra R A)
  proof: by
  apply le_antisymm
  · refine (mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) in S from one_mem S)

中文:
定理 isIdempotentElem_toSubmodule
  条件: (S : Subalgebra R A)
  证明: by
  apply le_antisymm
  · refine (mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) in S from one_mem S)

Depends on / 依赖: Submodule, Submodule.mul_mem_mul, le_antisymm, mul_mem_mul, mul_one, mul_toSubmodule_le, one_mem, sup_idem, trans_eq
-/
theorem isIdempotentElem_toSubmodule (S : Subalgebra R A) :
    IsIdempotentElem S.toSubmodule := by
  apply le_antisymm
  · refine (mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) in S from one_mem S)

/--
theorem `mul_toSubmodule` / 定理 `mul_toSubmodule`

English:
theorem mul_toSubmodule
  statement: {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  proof: by
  refine le_antisymm (mul_toSubmodule_le _ _) ?_
  rintro x (hx : x in Algebra.adjoin R (S union T : Set A))
  refine
    Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun _ _ _ _ => Submodule.add_mem _)
      (fun x y _ _ hx hy => ?_) hx
  · rcases hx with hxS | hxT
    · rw [← mul_on

中文:
定理 mul_toSubmodule
  结论: {R : 类型} {A : 类型} [CommSemiring R] [CommSemiring A] [Algebra R A]
  证明: by
  refine le_antisymm (mul_toSubmodule_le _ _) ?_
  rintro x (hx : x in Algebra.adjoin R (S union T : Set A))
  refine
    Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun _ _ _ _ => Submodule.add_mem _)
      (fun x y _ _ hx hy => ?_) hx
  · rcases hx with hxS | hxT
    · rw [← mul_on

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_induction, Submodule, Submodule.add_mem, Submodule.mul_mem_mul, add_mem, adjoin, adjoin_induction, algebraMap, le_antisymm, mul_mem_mul, mul_one, mul_toSubmodule_le, one_mem, one_mul
-/
theorem mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T)
        = Subalgebra.toSubmodule (S ⊔ T) := by
  refine le_antisymm (mul_toSubmodule_le _ _) ?_
  rintro x (hx : x in Algebra.adjoin R (S union T : Set A))
  refine
    Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun _ _ _ _ => Submodule.add_mem _)
      (fun x y _ _ hx hy => ?_) hx
  · rcases hx with hxS | hxT
    · rw [← mul_one x]
      exact Submodule.mul_mem_mul hxS (show (1 : A) in T from one_mem T)
    · rw [← one_mul x]
      exact Submodule.mul_mem_mul (show (1 : A) in S from one_mem S) hxT
  · rw [← one_mul (algebraMap _ _ _)]
    exact Submodule.mul_mem_mul (show (1 : A) in S from one_mem S) (algebraMap_mem T _)
  have := Submodule.mul_mem_mul hx hy
  rwa [mul_assoc, mul_comm _ (Subalgebra.toSubmodule T), ← mul_assoc _ _ (Subalgebra.toSubmodule S),
    isIdempotentElem_toSubmodule, mul_comm T.toSubmodule, ← mul_assoc,
    isIdempotentElem_toSubmodule] at this

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction R' (Subalgebra R A) where
  body: S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subalgebra.poi

中文:
定义 pointwiseMulAction
  签名: : MulAction R' (Subalgebra R A) where
  定义体: S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subalgebra.poi
-/
protected def pointwiseMulAction : MulAction R' (Subalgebra R A) where
  smul a S := S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open scoped Pointwise

@[simp, norm_cast]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: (m : R') (S : Subalgebra R A)
  statement: ↑(m • S) = m • (S : Set A)
  proof: rfl

@[simp]

中文:
定理 coe_pointwise_smul
  条件: (m : R') (S : Subalgebra R A)
  结论: ↑(m • S) = m • (S : Set A)
  证明: rfl

@[simp]
-/
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toSubsemiring` / 定理 `pointwise_smul_toSubsemiring`

English:
theorem pointwise_smul_toSubsemiring
  given: (m : R') (S : Subalgebra R A)
  proof: rfl

@[simp]

中文:
定理 pointwise_smul_toSubsemiring
  条件: (m : R') (S : Subalgebra R A)
  证明: rfl

@[simp]
-/
theorem pointwise_smul_toSubsemiring (m : R') (S : Subalgebra R A) :
    (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toSubmodule` / 定理 `pointwise_smul_toSubmodule`

English:
theorem pointwise_smul_toSubmodule
  given: (m : R') (S : Subalgebra R A)
  proof: rfl

@[simp]

中文:
定理 pointwise_smul_toSubmodule
  条件: (m : R') (S : Subalgebra R A)
  证明: rfl

@[simp]
-/
theorem pointwise_smul_toSubmodule (m : R') (S : Subalgebra R A) :
    Subalgebra.toSubmodule (m • S) = m • Subalgebra.toSubmodule S :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toSubring` / 定理 `pointwise_smul_toSubring`

English:
theorem pointwise_smul_toSubring
  statement: {R' R A : Type*} [Semiring R'] [CommRing R] [Ring A]
  proof: rfl

中文:
定理 pointwise_smul_toSubring
  结论: {R' R A : 类型} [Semiring R'] [CommRing R] [Ring A]
  证明: rfl
-/
theorem pointwise_smul_toSubring {R' R A : Type*} [Semiring R'] [CommRing R] [Ring A]
    [MulSemiringAction R' A] [Algebra R A] [SMulCommClass R' R A] (m : R') (S : Subalgebra R A) :
    (m • S).toSubring = m • S.toSubring :=
  rfl

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (m : R') (r : A) (S : Subalgebra R A)
  statement: r in S -> m • r in m • S
  proof: (Set.smul_mem_smul_set : _ -> _ in m • (S : Set A))

中文:
定理 smul_mem_pointwise_smul
  条件: (m : R') (r : A) (S : Subalgebra R A)
  结论: r in S -> m • r in m • S
  证明: (Set.smul_mem_smul_set : _ -> _ in m • (S : Set A))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r in S -> m • r in m • S :=
  (Set.smul_mem_smul_set : _ -> _ in m • (S : Set A))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass R' (Subalgebra R A) HSMul.hSMul LE.le
  body: ⟨fun _ _ => map_mono⟩

中文:
实例 :
  签名: CovariantClass R' (Subalgebra R A) HSMul.hSMul LE.le
  定义体: ⟨fun _ _ => map_mono⟩

Depends on / 依赖: map_mono
-/
instance : CovariantClass R' (Subalgebra R A) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

end Pointwise

end Subalgebra
