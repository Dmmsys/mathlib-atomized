/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.Engel
public import Mathlib.Algebra.Lie.Normalizer
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Engel subalgebras

This file defines Engel subalgebras of a Lie algebra and provides basic related properties.

The Engel subalgebra `LieSubalgebra.Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

## Main results

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent (TODO), hence Cartan subalgebras.

* `LieSubalgebra.normalizer_eq_self_of_engel_le`:
  Lie subalgebras containing an Engel subalgebra are self-normalizing,
  provided the ambient Lie algebra is Artinian.
* `LieSubalgebra.isNilpotent_of_forall_le_engel`:
  A Lie subalgebra of a Noetherian Lie algebra is nilpotent
  if it is contained in the Engel subalgebra of all its elements.
-/

@[expose] public section

open LieAlgebra LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubalgebra

variable (R)

/-- The Engel subalgebra `Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent, hence Cartan subalgebras. -/
@[simps!]
/--
Definition of `engel` / `engel` 的定义

English:
definition engel
  signature: (x : L)
  body: { (ad R L x).maxGenEigenspace 0 with
    lie_mem' := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Module.End.mem_maxGenEigenspace, zero_smul,
        sub_zero, forall_exists_index]
      intro y z m hm n hn
      refine ⟨m + 

中文:
定义 engel
  签名: (x : L)
  定义体: { (ad R L x).maxGenEigenspace 0 with
    lie_mem' := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Module.End.mem_maxGenEigenspace, zero_smul,
        sub_zero, forall_exists_index]
      intro y z m hm n hn
      refine ⟨m + 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, Finset, Finset.mem_antidiagonal, Finset.sum_eq_zero, Module, Module.End.mem_maxGenEigenspace, Module.End.pow_map_zero_of_le, Module.toMulActionWithZero, Submodule, Submodule.mem_toAddSubmonoid, ad_pow_lie, all_goals, forall_exists_index, lie_mem, maxGenEigenspace, mem_antidiagonal, mem_carrier
-/
def engel (x : L) : LieSubalgebra R L :=
  { (ad R L x).maxGenEigenspace 0 with
    lie_mem' := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Module.End.mem_maxGenEigenspace, zero_smul,
        sub_zero, forall_exists_index]
      intro y z m hm n hn
      refine ⟨m + n, ?_⟩
      rw [ad_pow_lie]
      apply Finset.sum_eq_zero
      intro ij hij
      obtain (h | h) : m <= ij.1 ∨ n <= ij.2 := by rw [Finset.mem_antidiagonal] at hij; lia
      all_goals simp [Module.End.pow_map_zero_of_le h, hm, hn] }

/--
lemma `mem_engel_iff` / 引理 `mem_engel_iff`

English:
lemma mem_engel_iff
  given: (x y : L)
  proof: (Module.End.mem_maxGenEigenspace _ _ _).trans by simp only [zero_smul, sub_zero]

中文:
引理 mem_engel_iff
  条件: (x y : L)
  证明: (Module.End.mem_maxGenEigenspace _ _ _).trans by simp only [zero_smul, sub_zero]

Depends on / 依赖: Module, Module.End.mem_maxGenEigenspace, mem_maxGenEigenspace, sub_zero, zero_smul
-/
lemma mem_engel_iff (x y : L) :
    y in engel R x ↔ exists n : Nat, ((ad R L x) ^ n) y = 0 :=
(Module.End.mem_maxGenEigenspace _ _ _).trans by simp only [zero_smul, sub_zero]

/--
lemma `self_mem_engel` / 引理 `self_mem_engel`

English:
lemma self_mem_engel
  given: (x : L)
  statement: x in engel R x
  proof: by
  simp only [mem_engel_iff]
  exact ⟨1, by simp⟩

@[simp]

中文:
引理 self_mem_engel
  条件: (x : L)
  结论: x in engel R x
  证明: by
  simp only [mem_engel_iff]
  exact ⟨1, by simp⟩

@[simp]

Depends on / 依赖: mem_engel_iff
-/
lemma self_mem_engel (x : L) : x in engel R x := by
  simp only [mem_engel_iff]
  exact ⟨1, by simp⟩

@[simp]
/--
lemma `engel_zero` / 引理 `engel_zero`

English:
lemma engel_zero
  statement: engel R (0 : L) = ⊤
  proof: by
  rw [eq_top_iff]
  rintro x -
  rw [mem_engel_iff]; rw [map_zero]
  use 1
  simp only [pow_one, LinearMap.zero_apply]

中文:
引理 engel_zero
  结论: engel R (0 : L) = ⊤
  证明: by
  rw [eq_top_iff]
  rintro x -
  rw [mem_engel_iff]; rw [map_zero]
  use 1
  simp only [pow_one, LinearMap.zero_apply]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, eq_top_iff, map_zero, mem_engel_iff, pow_one, zero_apply
-/
lemma engel_zero : engel R (0 : L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [mem_engel_iff]; rw [map_zero]
  use 1
  simp only [pow_one, LinearMap.zero_apply]

/-- Engel subalgebras are self-normalizing.
See `LieSubalgebra.normalizer_eq_self_of_engel_le` for a proof that Lie-subalgebras
containing an Engel subalgebra are also self-normalizing,
provided that the ambient Lie algebra is Artinian. -/
@[simp]
/--
lemma `normalizer_engel` / 引理 `normalizer_engel`

English:
lemma normalizer_engel
  given: (x : L)
  statement: normalizer (engel R x) = engel R x
  proof: by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (self_mem_engel R x)
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]; rw [mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [mem_engel_iff]
  use n + 1
  rw [pow_succ]; rw [Module.End.mul_apply]
 

中文:
引理 normalizer_engel
  条件: (x : L)
  结论: normalizer (engel R x) = engel R x
  证明: by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (self_mem_engel R x)
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]; rw [mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [mem_engel_iff]
  use n + 1
  rw [pow_succ]; rw [Module.End.mul_apply]
 

Depends on / 依赖: Module, Module.End.mul_apply, le_antisymm, le_normalizer, lie_skew, mem_engel_iff, mem_normalizer_iff, mul_apply, neg_mem_iff, pow_succ, self_mem_engel, specialize
-/
lemma normalizer_engel (x : L) : normalizer (engel R x) = engel R x := by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (self_mem_engel R x)
  rw [← lie_skew]; rw [neg_mem_iff (G := L)]; rw [mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [mem_engel_iff]
  use n + 1
  rw [pow_succ]; rw [Module.End.mul_apply]
  exact hn

variable {R}

open Filter in
/--
lemma `normalizer_eq_self_of_engel_le` / 引理 `normalizer_eq_self_of_engel_le`

English:
lemma normalizer_eq_self_of_engel_le
  statement: [IsArtinian R L]
  proof: by
  set N := normalizer H
  apply le_antisymm _ (le_normalizer H)
  calc N.toSubmodule <= (engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : forall n in N, ⁅x, n⁆ in H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (self_

中文:
引理 normalizer_eq_self_of_engel_le
  结论: [IsArtinian R L]
  证明: by
  set N := normalizer H
  apply le_antisymm _ (le_normalizer H)
  calc N.toSubmodule <= (engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : forall n in N, ⁅x, n⁆ in H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (self_

Depends on / 依赖: H.toSubmodule, N.toSubmodule, le_antisymm, le_normalizer, lie_skew, mem_normalizer_iff, neg_mem_iff, normalizer, restrict, self_mem_engel, specialize, sup_eq_right, toSubmodule
-/
lemma normalizer_eq_self_of_engel_le [IsArtinian R L]
    (H : LieSubalgebra R L) (x : L) (h : engel R x <= H) :
    normalizer H = H := by
  set N := normalizer H
  apply le_antisymm _ (le_normalizer H)
  calc N.toSubmodule <= (engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : forall n in N, ⁅x, n⁆ in H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (self_mem_engel R x))
    rwa [← lie_skew, neg_mem_iff (G := L)]
  have aux₂ : forall n in N, ⁅x, n⁆ in N := fun n hn => le_normalizer H (aux₁ _ hn)
  let dx : N ->ₗ[R] N := (ad R L x).restrict aux₂
  obtain ⟨k, hk⟩ : exists a, forall b >= a, Codisjoint (LinearMap.ker (dx ^ b)) (LinearMap.range (dx ^ b)) :=
eventually_atTop.mp dx.eventually_codisjoint_ker_pow_range_pow
  specialize hk (k + 1) (Nat.le_add_right k 1)
  rw [← Submodule.map_subtype_top N.toSubmodule]; rw [Submodule.map_le_iff_le_comap]
  apply hk
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_left
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    simp only [Submodule.mem_comap, mem_engel_iff, mem_toSubmodule]
    use k + 1
    clear hk; revert hy
    generalize k + 1 = k
    induction k generalizing y with
    | zero =>
      cases y; intro hy; simp only [pow_zero, Module.End.one_apply]
      exact (AddSubmonoid.mk_eq_zero N.toAddSubmonoid).mp hy
    | succ k ih => solve_by_elim
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_right
    rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨y, rfl⟩
    simp only [pow_succ', Module.End.mul_apply, Submodule.mem_comap, mem_toSubmodule]
    apply aux₁
    simp only [Submodule.coe_subtype, SetLike.coe_mem]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isNilpotent_of_forall_le_engel` / 引理 `isNilpotent_of_forall_le_engel`

English:
lemma isNilpotent_of_forall_le_engel
  statement: [IsNoetherian R L]
  proof: by
  rw [LieAlgebra.isNilpotent_iff_forall (R := R)]
  intro x
  let K : Nat ->o Submodule R H :=
    ⟨fun n => LinearMap.ker ((ad R H x) ^ n), fun m n hmn => ?mono⟩
  case mono =>
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact Module.End.pow_map_zero_of_le hmn hy
  obtain ⟨n, hn⟩ := mo

中文:
引理 isNilpotent_of_forall_le_engel
  结论: [IsNoetherian R L]
  证明: by
  rw [LieAlgebra.isNilpotent_iff_forall (R := R)]
  intro x
  let K : Nat ->o Submodule R H :=
    ⟨fun n => LinearMap.ker ((ad R H x) ^ n), fun m n hmn => ?mono⟩
  case mono =>
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact Module.End.pow_map_zero_of_le hmn hy
  obtain ⟨n, hn⟩ := mo

Depends on / 依赖: LieAlgebra, LieAlgebra.isNilpotent_iff_forall, LinearMap, LinearMap.ker, LinearMap.mem_ker, Module, Module.End.pow_ma, Module.End.pow_map_zero_of_le, Submodule, coe_ad_pow, isNilpotent_iff_forall, le_total, mem_engel_iff, mem_ker, monotone_stabilizes_iff_noetherian, monotone_stabilizes_iff_noetherian.mpr, pow_ma, pow_map_zero_of_le, specialize
-/
lemma isNilpotent_of_forall_le_engel [IsNoetherian R L]
    (H : LieSubalgebra R L) (h : forall x in H, H <= engel R x) :
    LieRing.IsNilpotent H := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := R)]
  intro x
  let K : Nat ->o Submodule R H :=
    ⟨fun n => LinearMap.ker ((ad R H x) ^ n), fun m n hmn => ?mono⟩
  case mono =>
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact Module.End.pow_map_zero_of_le hmn hy
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  use n
  ext y
  rw [coe_ad_pow]
  specialize h x x.2 y.2
  rw [mem_engel_iff] at h
  obtain ⟨m, hm⟩ := h
  obtain (hmn | hmn) : m <= n ∨ n <= m := le_total m n
  · exact Module.End.pow_map_zero_of_le hmn hm
  · have : forall k : Nat, ((ad R L) x ^ k) y = 0 ↔ y in K k := by simp [K, Subtype.ext_iff, coe_ad_pow]
    rwa [this, ← hn m hmn, ← this] at hm

end LieSubalgebra
