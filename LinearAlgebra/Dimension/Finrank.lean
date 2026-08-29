/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
module

public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Finite dimension of vector spaces

Definition of the rank of a module, or dimension of a vector space, as a natural number.

## Main definitions

Defined is `Module.finrank`, the dimension of a finite-dimensional space, returning a
`Nat`, as opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite
dimension, its `finrank` is by convention set to `0`.

The definition of `finrank` does not assume a `FiniteDimensional` instance, but lemmas might.
Import `LinearAlgebra.FiniteDimensional` to get access to these additional lemmas.

Formulas for the dimension are given for linear equivs, in `LinearEquiv.finrank_eq`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `Dimension.lean`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.
-/

@[expose] public section


universe u v w

open Cardinal Submodule Module Function

variable {R : Type u} {M : Type v} {N : Type w}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Module

section Semiring

/--
Definition of `finrank` / `finrank` 的定义

English:
definition finrank
  signature: (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
  body: Cardinal.toNat (Module.rank R M)

中文:
定义 finrank
  签名: (R M : 类型) [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: Cardinal.toNat (Module.rank R M)

Depends on / 依赖: Cardinal, Cardinal.toNat, Module, Module.rank
-/
noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : Nat :=
  Cardinal.toNat (Module.rank R M)

/--
theorem `finrank_subsingleton` / 定理 `finrank_subsingleton`

English:
theorem finrank_subsingleton
  given: [Subsingleton R]
  statement: finrank R M = 1
  proof: by
  rw [finrank]; rw [rank_subsingleton]; rw [map_one]

中文:
定理 finrank_subsingleton
  条件: [子单例 R]
  结论: finrank R M = 1
  证明: by
  rw [finrank]; rw [rank_subsingleton]; rw [map_one]
-/
@[simp] theorem finrank_subsingleton [Subsingleton R] : finrank R M = 1 := by
  rw [finrank]; rw [rank_subsingleton]; rw [map_one]

/--
theorem `finrank_eq_of_rank_eq` / 定理 `finrank_eq_of_rank_eq`

English:
theorem finrank_eq_of_rank_eq
  given: {n : Nat} (h : Module.rank R M = ↑n)
  statement: finrank R M = n
  proof: by
  simp [finrank, h]

中文:
定理 finrank_eq_of_rank_eq
  条件: {n : 自然数} (h : 模.rank R M = ↑n)
  结论: finrank R M = n
  证明: by
  simp [finrank, h]

Depends on / 依赖: finrank
-/
theorem finrank_eq_of_rank_eq {n : Nat} (h : Module.rank R M = ↑n) : finrank R M = n := by
  simp [finrank, h]

/--
lemma `rank_eq_one_iff_finrank_eq_one` / 引理 `rank_eq_one_iff_finrank_eq_one`

English:
lemma rank_eq_one_iff_finrank_eq_one
  statement: Module.rank R M = 1 ↔ finrank R M = 1
  proof: Cardinal.toNat_eq_one.symm

中文:
引理 rank_eq_one_iff_finrank_eq_one
  结论: 模.rank R M = 1 ↔ finrank R M = 1
  证明: Cardinal.toNat_eq_one.symm

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_one.symm, toNat_eq_one
-/
lemma rank_eq_one_iff_finrank_eq_one : Module.rank R M = 1 ↔ finrank R M = 1 :=
  Cardinal.toNat_eq_one.symm

/--
lemma `rank_eq_ofNat_iff_finrank_eq_ofNat` / 引理 `rank_eq_ofNat_iff_finrank_eq_ofNat`

English:
lemma rank_eq_ofNat_iff_finrank_eq_ofNat
  given: (n : Nat) [Nat.AtLeastTwo n]
  proof: Cardinal.toNat_eq_ofNat.symm

中文:
引理 rank_eq_of自然数_iff_finrank_eq_of自然数
  条件: (n : 自然数) [自然数.AtLeastTwo n]
  证明: Cardinal.toNat_eq_ofNat.symm

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_ofNat.symm, toNat_eq_ofNat
-/
lemma rank_eq_ofNat_iff_finrank_eq_ofNat (n : Nat) [Nat.AtLeastTwo n] :
    Module.rank R M = OfNat.ofNat n ↔ finrank R M = OfNat.ofNat n :=
  Cardinal.toNat_eq_ofNat.symm

/--
theorem `finrank_le_of_rank_le` / 定理 `finrank_le_of_rank_le`

English:
theorem finrank_le_of_rank_le
  given: {n : Nat} (h : Module.rank R M <= ↑n)
  statement: finrank R M <= n
  proof: by
  rwa [← Cardinal.toNat_le_iff_le_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans_lt natCast_lt_aleph0
  · exact natCast_lt_aleph0

中文:
定理 finrank_le_of_rank_le
  条件: {n : 自然数} (h : 模.rank R M <= ↑n)
  结论: finrank R M <= n
  证明: by
  rwa [← Cardinal.toNat_le_iff_le_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans_lt natCast_lt_aleph0
  · exact natCast_lt_aleph0

Depends on / 依赖: Cardinal, Cardinal.toNat_le_iff_le_of_lt_aleph0, h.trans_lt, natCast_lt_aleph0, toNat_le_iff_le_of_lt_aleph0, toNat_natCast, trans_lt
-/
theorem finrank_le_of_rank_le {n : Nat} (h : Module.rank R M <= ↑n) : finrank R M <= n := by
  rwa [← Cardinal.toNat_le_iff_le_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans_lt natCast_lt_aleph0
  · exact natCast_lt_aleph0

/--
theorem `finrank_lt_of_rank_lt` / 定理 `finrank_lt_of_rank_lt`

English:
theorem finrank_lt_of_rank_lt
  given: {n : Nat} (h : Module.rank R M < ↑n)
  statement: finrank R M < n
  proof: by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans natCast_lt_aleph0
  · exact natCast_lt_aleph0

中文:
定理 finrank_lt_of_rank_lt
  条件: {n : 自然数} (h : 模.rank R M < ↑n)
  结论: finrank R M < n
  证明: by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans natCast_lt_aleph0
  · exact natCast_lt_aleph0

Depends on / 依赖: Cardinal, Cardinal.toNat_lt_iff_lt_of_lt_aleph0, h.trans, natCast_lt_aleph0, toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast
-/
theorem finrank_lt_of_rank_lt {n : Nat} (h : Module.rank R M < ↑n) : finrank R M < n := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans natCast_lt_aleph0
  · exact natCast_lt_aleph0

/--
theorem `lt_rank_of_lt_finrank` / 定理 `lt_rank_of_lt_finrank`

English:
theorem lt_rank_of_lt_finrank
  given: {n : Nat} (h : n < finrank R M)
  statement: ↑n < Module.rank R M
  proof: by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast]
  · exact natCast_lt_aleph0
  · contrapose! h
    rw [finrank]; rw [Cardinal.toNat_apply_of_aleph0_le h]
    exact n.zero_le

中文:
定理 lt_rank_of_lt_finrank
  条件: {n : 自然数} (h : n < finrank R M)
  结论: ↑n < 模.rank R M
  证明: by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast]
  · exact natCast_lt_aleph0
  · contrapose! h
    rw [finrank]; rw [Cardinal.toNat_apply_of_aleph0_le h]
    exact n.zero_le

Depends on / 依赖: Cardinal, Cardinal.toNat_apply_of_aleph0_le, Cardinal.toNat_lt_iff_lt_of_lt_aleph0, contrapose, finrank, n.zero_le, natCast_lt_aleph0, toNat_apply_of_aleph0_le, toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast, zero_le
-/
theorem lt_rank_of_lt_finrank {n : Nat} (h : n < finrank R M) : ↑n < Module.rank R M := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast]
  · exact natCast_lt_aleph0
  · contrapose! h
    rw [finrank]; rw [Cardinal.toNat_apply_of_aleph0_le h]
    exact n.zero_le

/--
theorem `one_lt_rank_of_one_lt_finrank` / 定理 `one_lt_rank_of_one_lt_finrank`

English:
theorem one_lt_rank_of_one_lt_finrank
  given: (h : 1 < finrank R M)
  statement: 1 < Module.rank R M
  proof: by
  simpa using lt_rank_of_lt_finrank h

中文:
定理 one_lt_rank_of_one_lt_finrank
  条件: (h : 1 < finrank R M)
  结论: 1 < 模.rank R M
  证明: by
  simpa using lt_rank_of_lt_finrank h

Depends on / 依赖: lt_rank_of_lt_finrank
-/
theorem one_lt_rank_of_one_lt_finrank (h : 1 < finrank R M) : 1 < Module.rank R M := by
  simpa using lt_rank_of_lt_finrank h

/--
theorem `finrank_le_finrank_of_rank_le_rank` / 定理 `finrank_le_finrank_of_rank_le_rank`

English:
theorem finrank_le_finrank_of_rank_le_rank
  proof: by
  simpa only [toNat_lift] using! toNat_le_toNat h (lift_lt_aleph0.mpr h')

中文:
定理 finrank_le_finrank_of_rank_le_rank
  证明: by
  simpa only [toNat_lift] using! toNat_le_toNat h (lift_lt_aleph0.mpr h')

Depends on / 依赖: lift_lt_aleph0, lift_lt_aleph0.mpr, toNat_le_toNat, toNat_lift
-/
theorem finrank_le_finrank_of_rank_le_rank
    (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N))
    (h' : Module.rank R N < ℵ₀) : finrank R M <= finrank R N := by
  simpa only [toNat_lift] using! toNat_le_toNat h (lift_lt_aleph0.mpr h')

end Semiring

end Module

/--
theorem `CommSemiring.finrank_self` / 定理 `CommSemiring.finrank_self`

English:
theorem CommSemiring.finrank_self
  given: (R) [CommSemiring R]
  statement: Module.finrank R R = 1
  proof: finrank_eq_of_rank_eq (rank_self R)

中文:
定理 交换半环.finrank_self
  条件: (R) [交换半环 R]
  结论: 模.finrank R R = 1
  证明: finrank_eq_of_rank_eq (rank_self R)

Depends on / 依赖: finrank_eq_of_rank_eq, rank_self
-/
theorem CommSemiring.finrank_self (R) [CommSemiring R] : Module.finrank R R = 1 :=
  finrank_eq_of_rank_eq (rank_self R)

open Module

namespace LinearEquiv

/--
theorem `finrank_eq` / 定理 `finrank_eq`

English:
theorem finrank_eq
  given: (f : M ≃ₗ[R] N)
  statement: finrank R M = finrank R N
  proof: by
  unfold finrank
  rw [← Cardinal.toNat_lift]; rw [f.lift_rank_eq]; rw [Cardinal.toNat_lift]

中文:
定理 finrank_eq
  条件: (f : M ≃ₗ[R] N)
  结论: finrank R M = finrank R N
  证明: by
  unfold finrank
  rw [← Cardinal.toNat_lift]; rw [f.lift_rank_eq]; rw [Cardinal.toNat_lift]

Depends on / 依赖: Cardinal, Cardinal.toNat_lift, f.lift_rank_eq, finrank, lift_rank_eq, toNat_lift
-/
theorem finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finrank R N := by
  unfold finrank
  rw [← Cardinal.toNat_lift]; rw [f.lift_rank_eq]; rw [Cardinal.toNat_lift]

/--
theorem `finrank_map_eq` / 定理 `finrank_map_eq`

English:
theorem finrank_map_eq
  given: (f : M ≃ₗ[R] N) (p : Submodule R M)
  proof: (f.submoduleMap p).finrank_eq.symm

中文:
定理 finrank_map_eq
  条件: (f : M ≃ₗ[R] N) (p : 子模 R M)
  证明: (f.submoduleMap p).finrank_eq.symm

Depends on / 依赖: f.submoduleMap, finrank_eq, finrank_eq.symm, submoduleMap
-/
theorem finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodule R M) :
    finrank R (p.map (f : M ->ₗ[R] N)) = finrank R p :=
  (f.submoduleMap p).finrank_eq.symm

end LinearEquiv

/--
theorem `LinearMap.finrank_range_of_inj` / 定理 `LinearMap.finrank_range_of_inj`

English:
theorem LinearMap.finrank_range_of_inj
  given: {f : M ->ₗ[R] N} (hf : Function.Injective f)
  proof: by rw [(LinearEquiv.ofInjective f hf).finrank_eq]

@[simp]

中文:
定理 线性映射.finrank_range_of_inj
  条件: {f : M ->ₗ[R] N} (hf : 函数.单射 f)
  证明: by rw [(LinearEquiv.ofInjective f hf).finrank_eq]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, finrank_eq, ofInjective
-/
theorem LinearMap.finrank_range_of_inj {f : M ->ₗ[R] N} (hf : Function.Injective f) :
    finrank R (LinearMap.range f) = finrank R M := by rw [(LinearEquiv.ofInjective f hf).finrank_eq]

@[simp]
/--
theorem `Submodule.finrank_map_subtype_eq` / 定理 `Submodule.finrank_map_subtype_eq`

English:
theorem Submodule.finrank_map_subtype_eq
  given: (p : Submodule R M) (q : Submodule R p)
  proof: (Submodule.equivSubtypeMap p q).symm.finrank_eq

中文:
定理 子模.finrank_map_subtype_eq
  条件: (p : 子模 R M) (q : 子模 R p)
  证明: (Submodule.equivSubtypeMap p q).symm.finrank_eq

Depends on / 依赖: Submodule, Submodule.equivSubtypeMap, equivSubtypeMap, finrank_eq, symm.finrank_eq
-/
theorem Submodule.finrank_map_subtype_eq (p : Submodule R M) (q : Submodule R p) :
    finrank R (q.map p.subtype) = finrank R q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq

variable (R M)

@[simp]
/--
theorem `finrank_top` / 定理 `finrank_top`

English:
theorem finrank_top
  statement: finrank R (⊤ : Submodule R M) = finrank R M
  proof: by
  unfold finrank
  simp

中文:
定理 finrank_top
  结论: finrank R (⊤ : 子模 R M) = finrank R M
  证明: by
  unfold finrank
  simp

Depends on / 依赖: finrank
-/
theorem finrank_top : finrank R (⊤ : Submodule R M) = finrank R M := by
  unfold finrank
  simp

namespace Algebra

/--
theorem `finrank_eq_of_equiv_equiv` / 定理 `finrank_eq_of_equiv_equiv`

English:
theorem finrank_eq_of_equiv_equiv
  statement: {R₀ S₀ : Type*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀]
  proof: by
  simpa using! (congr_arg Cardinal.toNat (lift_rank_eq_of_equiv_equiv i j hc))

中文:
定理 finrank_eq_of_equiv_equiv
  结论: {R₀ S₀ : 类型} [交换半环 R₀] [半环 S₀] [代数 R₀ S₀]
  证明: by
  simpa using! (congr_arg Cardinal.toNat (lift_rank_eq_of_equiv_equiv i j hc))

Depends on / 依赖: Cardinal, Cardinal.toNat, congr_arg, lift_rank_eq_of_equiv_equiv
-/
theorem finrank_eq_of_equiv_equiv {R₀ S₀ : Type*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀]
    {R₁ S₁ : Type*} [CommSemiring R₁] [Semiring S₁] [Algebra R₁ S₁] (i : R₀ ≃+* R₁) (j : S₀ ≃+* S₁)
    (hc : (algebraMap R₁ S₁).comp i.toRingHom = j.toRingHom.comp (algebraMap R₀ S₀)) :
    Module.finrank R₀ S₀ = Module.finrank R₁ S₁ := by
  simpa using! (congr_arg Cardinal.toNat (lift_rank_eq_of_equiv_equiv i j hc))

end Algebra
