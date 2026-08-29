/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.RootSystem.Basic
public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# The root system associated with a Lie algebra

We show that the roots of a finite-dimensional splitting semisimple Lie algebra over a field of
characteristic 0 form a root system. We achieve this by studying root chains.

## Main results

- `LieAlgebra.IsKilling.apply_coroot_eq_cast`:
  If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer.

- `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`:
  The `α`-chain through `β` (`β - qα ... β ... β + rα`) are the only roots of the form `β + kα`.

- `LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul`:
  `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots.

- `LieAlgebra.IsKilling.rootSystem`: The root system of a finite-dimensional Lie algebra with
  non-degenerate Killing form over a field of characteristic zero,
  relative to a splitting Cartan subalgebra.

-/

@[expose] public section

noncomputable section

namespace LieAlgebra.IsKilling

open LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable (α β : Weight K H L)

set_option backward.privateInPublic true in
/--
lemma `chainLength_aux` / 引理 `chainLength_aux`

English:
lemma chainLength_aux
  given: (hα : α.IsNonZero) {x} (hx : x in rootSpace H (chainTop α β))
  proof: by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩

中文:
引理 chainLength_aux
  条件: (hα : α.IsNonZero) {x} (hx : x in rootSpace H (chainTop α β))
  证明: by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩
-/
private lemma chainLength_aux (hα : α.IsNonZero) {x} (hx : x in rootSpace H (chainTop α β)) :
    exists n : Nat, n • x = ⁅coroot α, x⁆ := by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `chainLength` / `chainLength` 的定义

English:
definition chainLength
  signature: (α β : Weight K H L)
  body: letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose

中文:
定义 chainLength
  签名: (α β : Weight K H L)
  定义体: letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose

Depends on / 依赖: Classical, Classical.propDecidable, IsZero, chainLength_aux, chainTop, choose_spec, exists_ne_zero, exists_ne_zero.choose_spec, propDecidable
-/
def chainLength (α β : Weight K H L) : Nat :=
  letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose

/--
lemma `chainLength_of_isZero` / 引理 `chainLength_of_isZero`

English:
lemma chainLength_of_isZero
  given: (hα : α.IsZero)
  statement: chainLength α β = 0
  proof: dif_pos hα

中文:
引理 chainLength_of_isZero
  条件: (hα : α.是零)
  结论: chainLength α β = 0
  证明: dif_pos hα

Depends on / 依赖: dif_pos
-/
lemma chainLength_of_isZero (hα : α.IsZero) : chainLength α β = 0 := dif_pos hα

/--
lemma `chainLength_nsmul` / 引理 `chainLength_nsmul`

English:
lemma chainLength_nsmul
  given: {x} (hx : x in rootSpace H (chainTop α β))
  proof: by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' in rootSpace H (chainTop α β) ∧ x' != 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : exists k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul]; rw [smul_comm]; rw [chainLength]; rw [dif_neg hα]; rw [(chainLength_aux α β hα h.1).choose_spec]

中文:
引理 chainLength_nsmul
  条件: {x} (hx : x in rootSpace H (chainTop α β))
  证明: by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' in rootSpace H (chainTop α β) ∧ x' != 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : exists k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul]; rw [smul_comm]; rw [chainLength]; rw [dif_neg hα]; rw [(chainLength_aux α β hα h.1).choose_spec]

Depends on / 依赖: IsZero, chainLength, chainLength_of_isZero, chainTop, chainTop_isNonZero, choose_spec, coroot_eq_zero_iff, coroot_eq_zero_iff.mpr, exists_ne_zero, exists_ne_zero.choose, exists_ne_zero.choose_spec, finrank_eq_one_iff_of_nonzero, finrank_rootSpace_eq_one, lie_smul, rootSpace, smul_comm, zero_lie, zero_smul
-/
lemma chainLength_nsmul {x} (hx : x in rootSpace H (chainTop α β)) :
    chainLength α β • x = ⁅coroot α, x⁆ := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' in rootSpace H (chainTop α β) ∧ x' != 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : exists k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul]; rw [smul_comm]; rw [chainLength]; rw [dif_neg hα]; rw [(chainLength_aux α β hα h.1).choose_spec]

/--
lemma `chainLength_smul` / 引理 `chainLength_smul`

English:
lemma chainLength_smul
  given: {x} (hx : x in rootSpace H (chainTop α β))
  proof: by
  rw [Nat.cast_smul_eq_nsmul]; rw [chainLength_nsmul _ _ hx]

中文:
引理 chainLength_smul
  条件: {x} (hx : x in rootSpace H (chainTop α β))
  证明: by
  rw [Nat.cast_smul_eq_nsmul]; rw [chainLength_nsmul _ _ hx]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, chainLength_nsmul
-/
lemma chainLength_smul {x} (hx : x in rootSpace H (chainTop α β)) :
    (chainLength α β : K) • x = ⁅coroot α, x⁆ := by
  rw [Nat.cast_smul_eq_nsmul]; rw [chainLength_nsmul _ _ hx]

/--
lemma `apply_coroot_eq_cast'` / 引理 `apply_coroot_eq_cast'`

English:
lemma apply_coroot_eq_cast'
  proof: by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx]; rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero_iff_left x_ne0]; rw [sub_eq_zero]; rw [coe_chainTop']; rw [nsmul_eq_mul]; rw [Pi.natCast_def]; rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

中文:
引理 apply_coroot_eq_cast'
  证明: by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx]; rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero_iff_left x_ne0]; rw [sub_eq_zero]; rw [coe_chainTop']; rw [nsmul_eq_mul]; rw [Pi.natCast_def]; rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

Depends on / 依赖: CharP.cast_eq_zero, Int.cast_zero, IsZero, Pi.add_apply, Pi.mul_apply, Pi.natCast_def, add_apply, cast_eq_zero, cast_zero, chainLength, chainLength_smul, chainTop, chainTopCoeff_zero, coe_chainTop, coroot_eq_zero_iff, coroot_eq_zero_iff.mpr, dif_pos, exists_ne_zero, lie_eq_smul_of_mem_rootSpace, map_zero
-/
lemma apply_coroot_eq_cast' :
    β (coroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : Int) := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx]; rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero_iff_left x_ne0]; rw [sub_eq_zero]; rw [coe_chainTop']; rw [nsmul_eq_mul]; rw [Pi.natCast_def]; rw [Pi.add_apply]; rw [Pi.mul_apply]; rw [root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

/--
lemma `rootSpace_neg_nsmul_add_chainTop_of_le` / 引理 `rootSpace_neg_nsmul_add_chainTop_of_le`

English:
lemma rootSpace_neg_nsmul_add_chainTop_of_le
  given: {n : Nat} (hn : n <= chainLength α β)
  proof: by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using! β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩

中文:
引理 rootSpace_neg_nsmul_add_chainTop_of_le
  条件: {n : 自然数} (hn : n <= chainLength α β)
  证明: by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using! β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩

Depends on / 依赖: HasPrimitiveVectorWith, IsZero, chainLength, chainLength_smul, chainTop, chainTop_zero, exists_isSl2Triple_of_weight_isNonZero, exists_ne_zero, genWeightSpace_add_chainTop, h_eq_coroot, isSl2.HasPrimitiveVectorWith, isSl2.h_eq_coroot, lie_mem_genWeightSpace_of_mem_genWeightSpace, ne_eq, neg_zero, smul_zero, x_ne0, zero_add
-/
lemma rootSpace_neg_nsmul_add_chainTop_of_le {n : Nat} (hn : n <= chainLength α β) :
    rootSpace H (-(n • α) + chainTop α β) != ⊥ := by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using! β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩

/--
lemma `rootSpace_neg_nsmul_add_chainTop_of_lt` / 引理 `rootSpace_neg_nsmul_add_chainTop_of_lt`

English:
lemma rootSpace_neg_nsmul_add_chainTop_of_lt
  given: (hα : α.IsNonZero) {n : Nat} (hn : chainLength α β < n)
  proof: by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H -> K) = -(n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W <= chainLength (-α) W := by
    have := apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_comm (2 : K),
      add_sub_cancel, add_sub, Nat.cast_inj, eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add,
      sub_eq_iff_eq_add] at this
    lia
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H -> K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, ← Nat.cast_smul_eq_nsmul Int, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg]; rw [← smul_neg]; rw [neg_neg]; rw [← Weight.coe_neg]; rw [H₂] at this
  exact this (genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα)

中文:
引理 rootSpace_neg_nsmul_add_chainTop_of_lt
  条件: (hα : α.IsNonZero) {n : 自然数} (hn : chainLength α β < n)
  证明: by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H -> K) = -(n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W <= chainLength (-α) W := by
    have := apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_comm (2 : K),
      add_sub_cancel, add_sub, Nat.cast_inj, eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add,
      sub_eq_iff_eq_add] at this
    lia
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H -> K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, ← Nat.cast_smul_eq_nsmul Int, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg]; rw [← smul_neg]; rw [neg_neg]; rw [← Weight.coe_neg]; rw [H₂] at this
  exact this (genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα)

Depends on / 依赖: AddCommMonoid, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_sub, Pi.add_apply, Pi.mul_apply, Pi.natCast_def, Pi.neg_apply, Semiring, Weight, add_, add_apply, add_sub_cancel, apply_coroot_eq_cast, cast_mul, cast_natCast, cast_ofNat, cast_sub, chainLength
-/
lemma rootSpace_neg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : Nat} (hn : chainLength α β < n) :
    rootSpace H (-(n • α) + chainTop α β) = ⊥ := by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H -> K) = -(n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W <= chainLength (-α) W := by
    have := apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_comm (2 : K),
      add_sub_cancel, add_sub, Nat.cast_inj, eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add,
      sub_eq_iff_eq_add] at this
    lia
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H -> K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, ← Nat.cast_smul_eq_nsmul Int, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg]; rw [← smul_neg]; rw [neg_neg]; rw [← Weight.coe_neg]; rw [H₂] at this
  exact this (genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα)

/--
lemma `chainTopCoeff_le_chainLength` / 引理 `chainTopCoeff_le_chainLength`

English:
lemma chainTopCoeff_le_chainLength
  statement: chainTopCoeff α β <= chainLength α β
  proof: by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt]; rw [← Nat.succ_le_iff]
  intro e
  apply genWeightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_sub e]; rw [sub_smul]; rw [sub_eq_neg_add]; rw [add_assoc]; rw [← coe_chainTop]; rw [Nat.cast_smul_eq_nsmul]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)

中文:
引理 chainTopCoeff_le_chainLength
  结论: chainTopCoeff α β <= chainLength α β
  证明: by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt]; rw [← Nat.succ_le_iff]
  intro e
  apply genWeightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_sub e]; rw [sub_smul]; rw [sub_eq_neg_add]; rw [add_assoc]; rw [← coe_chainTop]; rw [Nat.cast_smul_eq_nsmul]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)

Depends on / 依赖: AddCommMonoid, IsZero, Module, Nat.cast_smul_eq_nsmul, Nat.cast_sub, Nat.lt_succ_self, Nat.sub_le, Nat.succ_le_iff, Semiring, SetLike, add_assoc, cast_smul_eq_nsmul, cast_sub, chainLength, chainTopCoeff, chainTopCoeff_zero, coe_chainTop, genWeightSpace_nsmul_add_ne_bot_of_le, lt_succ_self, module
-/
lemma chainTopCoeff_le_chainLength : chainTopCoeff α β <= chainLength α β := by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt]; rw [← Nat.succ_le_iff]
  intro e
  apply genWeightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_sub e]; rw [sub_smul]; rw [sub_eq_neg_add]; rw [add_assoc]; rw [← coe_chainTop]; rw [Nat.cast_smul_eq_nsmul]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)

/--
lemma `chainBotCoeff_add_chainTopCoeff` / 引理 `chainBotCoeff_add_chainTopCoeff`

English:
lemma chainBotCoeff_add_chainTopCoeff
  proof: by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le_iff, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply genWeightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_succ]; rw [Nat.cast_sub (chainTopCoeff_le_chainLength α β)]; rw [LieModule.Weight.coe_neg]; rw [smul_neg]; rw [← neg_smul]; rw [neg_add_rev]; rw [neg_sub]; rw [sub_eq_neg_add]; rw [← add_assoc]; rw [← neg_add_rev]; rw [add_smul]; rw [add_assoc]; rw [← coe_chainTop]; rw [neg_smul]; rw [← @Nat.cast_one Int]; rw [← Nat.cast_add]; rw [Nat.cast_smul_eq_nsmul]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add]; rw [← Nat.cast_smul_eq_nsmul Int]; rw [← neg_smul]; rw [coe_chainTop]; rw [← add_assoc]; rw [← add_smul]; rw [Nat.cast_add]; rw [neg_add]; rw [add_assoc]; rw [neg_add_cancel]; rw [add_zero]; rw [neg_smul]; rw [← smul_neg]; rw [Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)

中文:
引理 chainBotCoeff_add_chainTopCoeff
  证明: by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le_iff, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply genWeightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_succ]; rw [Nat.cast_sub (chainTopCoeff_le_chainLength α β)]; rw [LieModule.Weight.coe_neg]; rw [smul_neg]; rw [← neg_smul]; rw [neg_add_rev]; rw [neg_sub]; rw [sub_eq_neg_add]; rw [← add_assoc]; rw [← neg_add_rev]; rw [add_smul]; rw [add_assoc]; rw [← coe_chainTop]; rw [neg_smul]; rw [← @Nat.cast_one Int]; rw [← Nat.cast_add]; rw [Nat.cast_smul_eq_nsmul]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add]; rw [← Nat.cast_smul_eq_nsmul Int]; rw [← neg_smul]; rw [coe_chainTop]; rw [← add_assoc]; rw [← add_smul]; rw [Nat.cast_add]; rw [neg_add]; rw [add_assoc]; rw [neg_add_cancel]; rw [add_zero]; rw [neg_smul]; rw [← smul_neg]; rw [Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)

Depends on / 依赖: IsZero, LieModule, LieModule.Weight.coe_neg, Nat.cast_smul_eq_nsmul, Nat.cast_sub, Nat.cast_succ, Nat.le_sub_iff_add_le, Nat.succ_le_iff, Weight, Weight.coe_neg, cast_smul_eq_nsmul, cast_sub, cast_succ, chainBotCoeff, chainBotCoeff_zero, chainLength_of_isZero, chainTopCoeff_le_chainLength, chainTopCoeff_zero, coe_neg, genWeightSpace_nsmul_add_ne_bot_of_le
-/
lemma chainBotCoeff_add_chainTopCoeff :
    chainBotCoeff α β + chainTopCoeff α β = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le_iff, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply genWeightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [← Nat.cast_smul_eq_nsmul Int]; rw [Nat.cast_succ]; rw [Nat.cast_sub (chainTopCoeff_le_chainLength α β)]; rw [LieModule.Weight.coe_neg]; rw [smul_neg]; rw [← neg_smul]; rw [neg_add_rev]; rw [neg_sub]; rw [sub_eq_neg_add]; rw [← add_assoc]; rw [← neg_add_rev]; rw [add_smul]; rw [add_assoc]; rw [← coe_chainTop]; rw [neg_smul]; rw [← @Nat.cast_one Int]; rw [← Nat.cast_add]; rw [Nat.cast_smul_eq_nsmul]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add]; rw [← Nat.cast_smul_eq_nsmul Int]; rw [← neg_smul]; rw [coe_chainTop]; rw [← add_assoc]; rw [← add_smul]; rw [Nat.cast_add]; rw [neg_add]; rw [add_assoc]; rw [neg_add_cancel]; rw [add_zero]; rw [neg_smul]; rw [← smul_neg]; rw [Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)

/--
lemma `chainTopCoeff_add_chainBotCoeff` / 引理 `chainTopCoeff_add_chainBotCoeff`

English:
lemma chainTopCoeff_add_chainBotCoeff
  proof: by
  rw [add_comm]; rw [chainBotCoeff_add_chainTopCoeff]

中文:
引理 chainTopCoeff_add_chainBotCoeff
  证明: by
  rw [add_comm]; rw [chainBotCoeff_add_chainTopCoeff]

Depends on / 依赖: add_comm, chainBotCoeff_add_chainTopCoeff
-/
lemma chainTopCoeff_add_chainBotCoeff :
    chainTopCoeff α β + chainBotCoeff α β = chainLength α β := by
  rw [add_comm]; rw [chainBotCoeff_add_chainTopCoeff]

/--
lemma `chainBotCoeff_le_chainLength` / 引理 `chainBotCoeff_le_chainLength`

English:
lemma chainBotCoeff_le_chainLength
  statement: chainBotCoeff α β <= chainLength α β
  proof: (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)

@[simp]

中文:
引理 chainBotCoeff_le_chainLength
  结论: chainBotCoeff α β <= chainLength α β
  证明: (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)

@[simp]

Depends on / 依赖: Nat.le_add_left, chainTopCoeff_add_chainBotCoeff, le_add_left, trans_eq
-/
lemma chainBotCoeff_le_chainLength : chainBotCoeff α β <= chainLength α β :=
  (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)

@[simp]
/--
lemma `chainLength_neg` / 引理 `chainLength_neg`

English:
lemma chainLength_neg
  proof: by
  rw [← chainBotCoeff_add_chainTopCoeff]; rw [← chainBotCoeff_add_chainTopCoeff]; rw [add_comm]; rw [Weight.coe_neg]; rw [chainTopCoeff_neg]; rw [chainBotCoeff_neg]

@[simp]

中文:
引理 chainLength_neg
  证明: by
  rw [← chainBotCoeff_add_chainTopCoeff]; rw [← chainBotCoeff_add_chainTopCoeff]; rw [add_comm]; rw [Weight.coe_neg]; rw [chainTopCoeff_neg]; rw [chainBotCoeff_neg]

@[simp]

Depends on / 依赖: Weight, Weight.coe_neg, add_comm, chainBotCoeff_add_chainTopCoeff, chainBotCoeff_neg, chainTopCoeff_neg, coe_neg
-/
lemma chainLength_neg :
    chainLength (-α) β = chainLength α β := by
  rw [← chainBotCoeff_add_chainTopCoeff]; rw [← chainBotCoeff_add_chainTopCoeff]; rw [add_comm]; rw [Weight.coe_neg]; rw [chainTopCoeff_neg]; rw [chainBotCoeff_neg]

@[simp]
/--
lemma `chainLength_zero` / 引理 `chainLength_zero`

English:
lemma chainLength_zero
  given: [Nontrivial L]
  statement: chainLength 0 β = 0
  proof: by
  simp [← chainBotCoeff_add_chainTopCoeff]

中文:
引理 chainLength_zero
  条件: [非平凡 L]
  结论: chainLength 0 β = 0
  证明: by
  simp [← chainBotCoeff_add_chainTopCoeff]

Depends on / 依赖: chainBotCoeff_add_chainTopCoeff
-/
lemma chainLength_zero [Nontrivial L] : chainLength 0 β = 0 := by
  simp [← chainBotCoeff_add_chainTopCoeff]

/--
lemma `apply_coroot_eq_cast` / 引理 `apply_coroot_eq_cast`

English:
lemma apply_coroot_eq_cast
  proof: by
  rw [apply_coroot_eq_cast']; rw [← chainTopCoeff_add_chainBotCoeff]; congr 1; lia

中文:
引理 apply_coroot_eq_cast
  证明: by
  rw [apply_coroot_eq_cast']; rw [← chainTopCoeff_add_chainBotCoeff]; congr 1; lia

Depends on / 依赖: apply_coroot_eq_cast, chainTopCoeff_add_chainBotCoeff
-/
lemma apply_coroot_eq_cast :
    β (coroot α) = (chainBotCoeff α β - chainTopCoeff α β : Int) := by
  rw [apply_coroot_eq_cast']; rw [← chainTopCoeff_add_chainBotCoeff]; congr 1; lia

/--
lemma `le_chainBotCoeff_of_rootSpace_ne_top` / 引理 `le_chainBotCoeff_of_rootSpace_ne_top`

English:
lemma le_chainBotCoeff_of_rootSpace_ne_top
  proof: by
  contrapose! hn
  lift n to Nat using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt]; rw [← @Nat.add_lt_add_iff_right (chainTopCoeff α β)]; rw [chainBotCoeff_add_chainTopCoeff] at hn
  have := rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [← Nat.cast_smul_eq_nsmul Int, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero] at this

中文:
引理 le_chainBotCoeff_of_rootSpace_ne_top
  证明: by
  contrapose! hn
  lift n to Nat using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt]; rw [← @Nat.add_lt_add_iff_right (chainTopCoeff α β)]; rw [chainBotCoeff_add_chainTopCoeff] at hn
  have := rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [← Nat.cast_smul_eq_nsmul Int, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero] at this

Depends on / 依赖: Nat.add_lt_add_iff_right, Nat.cast_add, Nat.cast_lt, Nat.cast_nonneg, Nat.cast_smul_eq_nsmul, add_assoc, add_lt_add_iff_right, add_smul, add_zero, cast_add, cast_lt, cast_nonneg, cast_smul_eq_nsmul, chainBotCoeff_add_chainTopCoeff, chainTopCoeff, coe_chainTop, contrapose, hn.le, neg_add, neg_add_cancel
-/
lemma le_chainBotCoeff_of_rootSpace_ne_top
    (hα : α.IsNonZero) (n : Int) (hn : rootSpace H (-n • α + β) != ⊥) :
    n <= chainBotCoeff α β := by
  contrapose! hn
  lift n to Nat using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt]; rw [← @Nat.add_lt_add_iff_right (chainTopCoeff α β)]; rw [chainBotCoeff_add_chainTopCoeff] at hn
  have := rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [← Nat.cast_smul_eq_nsmul Int, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero] at this

/--
lemma `rootSpace_zsmul_add_ne_bot_iff` / 引理 `rootSpace_zsmul_add_ne_bot_iff`

English:
lemma rootSpace_zsmul_add_ne_bot_iff
  given: (hα : α.IsNonZero) (n : Int)
  proof: by
  constructor
  · refine (fun hn => ⟨?_, le_chainBotCoeff_of_rootSpace_ne_top α β hα _ (by rwa [neg_neg])⟩)
    rw [← chainBotCoeff_neg]; rw [← Weight.coe_neg]
    apply le_chainBotCoeff_of_rootSpace_ne_top _ _ hα.neg
    rwa [neg_smul, Weight.coe_neg, smul_neg, neg_neg]
  · rintro ⟨h₁, h₂⟩
    set k := chainTopCoeff α β - n with hk; clear_value k
    lift k to Nat using (by rw [hk, le_sub_iff_add_le, zero_add]; exact h₁)
    rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at hk
    subst hk
    simp only [neg_sub, tsub_le_iff_right, ← Nat.cast_add, Nat.cast_le,
      chainBotCoeff_add_chainTopCoeff] at h₂
    have := rootSpace_neg_nsmul_add_chainTop_of_le α β h₂
    rwa [coe_chainTop, ← Nat.cast_smul_eq_nsmul Int, ← neg_smul,
      ← add_assoc, ← add_smul, ← sub_eq_neg_add] at this

中文:
引理 rootSpace_zsmul_add_ne_bot_iff
  条件: (hα : α.IsNonZero) (n : 整数)
  证明: by
  constructor
  · refine (fun hn => ⟨?_, le_chainBotCoeff_of_rootSpace_ne_top α β hα _ (by rwa [neg_neg])⟩)
    rw [← chainBotCoeff_neg]; rw [← Weight.coe_neg]
    apply le_chainBotCoeff_of_rootSpace_ne_top _ _ hα.neg
    rwa [neg_smul, Weight.coe_neg, smul_neg, neg_neg]
  · rintro ⟨h₁, h₂⟩
    set k := chainTopCoeff α β - n with hk; clear_value k
    lift k to Nat using (by rw [hk, le_sub_iff_add_le, zero_add]; exact h₁)
    rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at hk
    subst hk
    simp only [neg_sub, tsub_le_iff_right, ← Nat.cast_add, Nat.cast_le,
      chainBotCoeff_add_chainTopCoeff] at h₂
    have := rootSpace_neg_nsmul_add_chainTop_of_le α β h₂
    rwa [coe_chainTop, ← Nat.cast_smul_eq_nsmul Int, ← neg_smul,
      ← add_assoc, ← add_smul, ← sub_eq_neg_add] at this

Depends on / 依赖: Weight, Weight.coe_neg, chainBotCoeff_neg, chainTopCoeff, clear_value, coe_neg, eq_sub_iff_add_eq, le_chainBotCoeff_of_rootSpace_ne_top, le_sub_iff_add_le, neg_neg, neg_smul, neg_sub, smul_neg, tsub_le_iff_, zero_add
-/
lemma rootSpace_zsmul_add_ne_bot_iff (hα : α.IsNonZero) (n : Int) :
    rootSpace H (n • α + β) != ⊥ ↔ n <= chainTopCoeff α β ∧ -n <= chainBotCoeff α β := by
  constructor
  · refine (fun hn => ⟨?_, le_chainBotCoeff_of_rootSpace_ne_top α β hα _ (by rwa [neg_neg])⟩)
    rw [← chainBotCoeff_neg]; rw [← Weight.coe_neg]
    apply le_chainBotCoeff_of_rootSpace_ne_top _ _ hα.neg
    rwa [neg_smul, Weight.coe_neg, smul_neg, neg_neg]
  · rintro ⟨h₁, h₂⟩
    set k := chainTopCoeff α β - n with hk; clear_value k
    lift k to Nat using (by rw [hk, le_sub_iff_add_le, zero_add]; exact h₁)
    rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at hk
    subst hk
    simp only [neg_sub, tsub_le_iff_right, ← Nat.cast_add, Nat.cast_le,
      chainBotCoeff_add_chainTopCoeff] at h₂
    have := rootSpace_neg_nsmul_add_chainTop_of_le α β h₂
    rwa [coe_chainTop, ← Nat.cast_smul_eq_nsmul Int, ← neg_smul,
      ← add_assoc, ← add_smul, ← sub_eq_neg_add] at this

/--
lemma `rootSpace_zsmul_add_ne_bot_iff_mem` / 引理 `rootSpace_zsmul_add_ne_bot_iff_mem`

English:
lemma rootSpace_zsmul_add_ne_bot_iff_mem
  given: (hα : α.IsNonZero) (n : Int)
  proof: by
  rw [rootSpace_zsmul_add_ne_bot_iff α β hα n]; rw [Finset.mem_Icc]; rw [and_comm]; rw [neg_le]

中文:
引理 rootSpace_zsmul_add_ne_bot_iff_mem
  条件: (hα : α.IsNonZero) (n : 整数)
  证明: by
  rw [rootSpace_zsmul_add_ne_bot_iff α β hα n]; rw [Finset.mem_Icc]; rw [and_comm]; rw [neg_le]

Depends on / 依赖: Finset, Finset.mem_Icc, and_comm, mem_Icc, neg_le, rootSpace_zsmul_add_ne_bot_iff
-/
lemma rootSpace_zsmul_add_ne_bot_iff_mem (hα : α.IsNonZero) (n : Int) :
    rootSpace H (n • α + β) != ⊥ ↔ n in Finset.Icc (-chainBotCoeff α β : Int) (chainTopCoeff α β) := by
  rw [rootSpace_zsmul_add_ne_bot_iff α β hα n]; rw [Finset.mem_Icc]; rw [and_comm]; rw [neg_le]

/--
lemma `chainTopCoeff_of_eq_zsmul_add` / 引理 `chainTopCoeff_of_eq_zsmul_add`

English:
lemma chainTopCoeff_of_eq_zsmul_add
  proof: by
  apply le_antisymm
  · refine le_sub_iff_add_le.mpr ((rootSpace_zsmul_add_ne_bot_iff α β hα _).mp ?_).1
    rw [add_smul]; rw [add_assoc]; rw [← hβ']; rw [← coe_chainTop]
    exact (chainTop α β').2
  · refine ((rootSpace_zsmul_add_ne_bot_iff α β' hα _).mp ?_).1
    rw [hβ']; rw [← add_assoc]; rw [← add_smul]; rw [sub_add_cancel]; rw [← coe_chainTop]
    exact (chainTop α β).2

中文:
引理 chainTopCoeff_of_eq_zsmul_add
  证明: by
  apply le_antisymm
  · refine le_sub_iff_add_le.mpr ((rootSpace_zsmul_add_ne_bot_iff α β hα _).mp ?_).1
    rw [add_smul]; rw [add_assoc]; rw [← hβ']; rw [← coe_chainTop]
    exact (chainTop α β').2
  · refine ((rootSpace_zsmul_add_ne_bot_iff α β' hα _).mp ?_).1
    rw [hβ']; rw [← add_assoc]; rw [← add_smul]; rw [sub_add_cancel]; rw [← coe_chainTop]
    exact (chainTop α β).2

Depends on / 依赖: add_assoc, add_smul, chainTop, coe_chainTop, le_antisymm, le_sub_iff_add_le, le_sub_iff_add_le.mpr, rootSpace_zsmul_add_ne_bot_iff, sub_add_cancel
-/
lemma chainTopCoeff_of_eq_zsmul_add
    (hα : α.IsNonZero) (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) = n • α + β) :
    chainTopCoeff α β' = chainTopCoeff α β - n := by
  apply le_antisymm
  · refine le_sub_iff_add_le.mpr ((rootSpace_zsmul_add_ne_bot_iff α β hα _).mp ?_).1
    rw [add_smul]; rw [add_assoc]; rw [← hβ']; rw [← coe_chainTop]
    exact (chainTop α β').2
  · refine ((rootSpace_zsmul_add_ne_bot_iff α β' hα _).mp ?_).1
    rw [hβ']; rw [← add_assoc]; rw [← add_smul]; rw [sub_add_cancel]; rw [← coe_chainTop]
    exact (chainTop α β).2

/--
lemma `chainBotCoeff_of_eq_zsmul_add` / 引理 `chainBotCoeff_of_eq_zsmul_add`

English:
lemma chainBotCoeff_of_eq_zsmul_add
  proof: by
  have : (β' : H -> K) = -n • (-α) + β := by rwa [neg_smul, smul_neg, neg_neg]
  rw [chainBotCoeff]; rw [chainBotCoeff]; rw [← Weight.coe_neg]; rw [chainTopCoeff_of_eq_zsmul_add (-α) β hα.neg β' (-n) this]; rw [sub_neg_eq_add]

中文:
引理 chainBotCoeff_of_eq_zsmul_add
  证明: by
  have : (β' : H -> K) = -n • (-α) + β := by rwa [neg_smul, smul_neg, neg_neg]
  rw [chainBotCoeff]; rw [chainBotCoeff]; rw [← Weight.coe_neg]; rw [chainTopCoeff_of_eq_zsmul_add (-α) β hα.neg β' (-n) this]; rw [sub_neg_eq_add]

Depends on / 依赖: Weight, Weight.coe_neg, chainBotCoeff, chainTopCoeff_of_eq_zsmul_add, coe_neg, neg_neg, neg_smul, smul_neg, sub_neg_eq_add
-/
lemma chainBotCoeff_of_eq_zsmul_add
    (hα : α.IsNonZero) (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) = n • α + β) :
    chainBotCoeff α β' = chainBotCoeff α β + n := by
  have : (β' : H -> K) = -n • (-α) + β := by rwa [neg_smul, smul_neg, neg_neg]
  rw [chainBotCoeff]; rw [chainBotCoeff]; rw [← Weight.coe_neg]; rw [chainTopCoeff_of_eq_zsmul_add (-α) β hα.neg β' (-n) this]; rw [sub_neg_eq_add]

/--
lemma `chainLength_of_eq_zsmul_add` / 引理 `chainLength_of_eq_zsmul_add`

English:
lemma chainLength_of_eq_zsmul_add
  given: (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) = n • α + β)
  proof: by
  by_cases hα : α.IsZero
  · rw [chainLength_of_isZero _ _ hα, chainLength_of_isZero _ _ hα]
  · apply Nat.cast_injective (R := Int)
    rw [← chainTopCoeff_add_chainBotCoeff]; rw [← chainTopCoeff_add_chainBotCoeff]; rw [Nat.cast_add]; rw [Nat.cast_add]; rw [chainTopCoeff_of_eq_zsmul_add α β hα β' n hβ']; rw [chainBotCoeff_of_eq_zsmul_add α β hα β' n hβ']; rw [sub_eq_add_neg]; rw [add_add_add_comm]; rw [neg_add_cancel]; rw [add_zero]

中文:
引理 chainLength_of_eq_zsmul_add
  条件: (β' : Weight K H L) (n : 整数) (hβ' : (β' : H -> K) = n • α + β)
  证明: by
  by_cases hα : α.IsZero
  · rw [chainLength_of_isZero _ _ hα, chainLength_of_isZero _ _ hα]
  · apply Nat.cast_injective (R := Int)
    rw [← chainTopCoeff_add_chainBotCoeff]; rw [← chainTopCoeff_add_chainBotCoeff]; rw [Nat.cast_add]; rw [Nat.cast_add]; rw [chainTopCoeff_of_eq_zsmul_add α β hα β' n hβ']; rw [chainBotCoeff_of_eq_zsmul_add α β hα β' n hβ']; rw [sub_eq_add_neg]; rw [add_add_add_comm]; rw [neg_add_cancel]; rw [add_zero]

Depends on / 依赖: IsZero, Nat.cast_add, Nat.cast_injective, add_add_add_comm, add_zero, cast_add, cast_injective, chainBotCoeff_of_eq_zsmul_add, chainLength_of_isZero, chainTopCoeff_add_chainBotCoeff, chainTopCoeff_of_eq_zsmul_add, neg_add_cancel, sub_eq_add_neg
-/
lemma chainLength_of_eq_zsmul_add (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) = n • α + β) :
    chainLength α β' = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [chainLength_of_isZero _ _ hα, chainLength_of_isZero _ _ hα]
  · apply Nat.cast_injective (R := Int)
    rw [← chainTopCoeff_add_chainBotCoeff]; rw [← chainTopCoeff_add_chainBotCoeff]; rw [Nat.cast_add]; rw [Nat.cast_add]; rw [chainTopCoeff_of_eq_zsmul_add α β hα β' n hβ']; rw [chainBotCoeff_of_eq_zsmul_add α β hα β' n hβ']; rw [sub_eq_add_neg]; rw [add_add_add_comm]; rw [neg_add_cancel]; rw [add_zero]

/--
lemma `chainTopCoeff_zero_right` / 引理 `chainTopCoeff_zero_right`

English:
lemma chainTopCoeff_zero_right
  given: [Nontrivial L] (hα : α.IsNonZero)
  proof: by
  symm
  apply eq_of_le_of_not_lt
  · rw [Nat.one_le_iff_ne_zero]
    intro e
    exact α.2 (by simpa [e] using!
      genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα)
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α (0 : Weight K H L)).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α (0 : Weight K H L) : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  obtain ⟨k, hk⟩ : exists k : K, k • f =
      (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x := by
    have : (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x in rootSpace H (-α) := by
      convert toEnd_pow_apply_mem hf hx (chainTopCoeff α (0 : Weight K H L) + 1)
      rw [coe_chainTop']; rw [FunLike.coe_zero]; rw [add_zero]; rw [succ_nsmul']; rw [add_assoc]; rw [smul_neg]; rw [neg_add_cancel]; rw [add_zero]
    simpa using! (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using! isSl2.f_ne_zero)).mp
      (finrank_rootSpace_eq_one _ hα.neg) ⟨_, this⟩
  apply_fun (⁅f, ·⁆) at hk
  simp only [lie_smul, lie_self, smul_zero, prim.lie_f_pow_toEnd_f] at hk
  intro e
  refine prim.pow_toEnd_f_ne_zero_of_eq_nat rfl ?_ hk.symm
  have := (apply_coroot_eq_cast' α 0).symm
  simp only [← @Nat.cast_two Int, ← Nat.cast_mul, zero_apply, Int.cast_eq_zero, sub_eq_zero,
    Nat.cast_inj] at this
  rwa [this, Nat.succ_le_iff, two_mul, add_lt_add_iff_left]

中文:
引理 chainTopCoeff_zero_right
  条件: [非平凡 L] (hα : α.IsNonZero)
  证明: by
  symm
  apply eq_of_le_of_not_lt
  · rw [Nat.one_le_iff_ne_zero]
    intro e
    exact α.2 (by simpa [e] using!
      genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα)
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α (0 : Weight K H L)).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α (0 : Weight K H L) : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  obtain ⟨k, hk⟩ : exists k : K, k • f =
      (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x := by
    have : (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x in rootSpace H (-α) := by
      convert toEnd_pow_apply_mem hf hx (chainTopCoeff α (0 : Weight K H L) + 1)
      rw [coe_chainTop']; rw [FunLike.coe_zero]; rw [add_zero]; rw [succ_nsmul']; rw [add_assoc]; rw [smul_neg]; rw [neg_add_cancel]; rw [add_zero]
    simpa using! (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using! isSl2.f_ne_zero)).mp
      (finrank_rootSpace_eq_one _ hα.neg) ⟨_, this⟩
  apply_fun (⁅f, ·⁆) at hk
  simp only [lie_smul, lie_self, smul_zero, prim.lie_f_pow_toEnd_f] at hk
  intro e
  refine prim.pow_toEnd_f_ne_zero_of_eq_nat rfl ?_ hk.symm
  have := (apply_coroot_eq_cast' α 0).symm
  simp only [← @Nat.cast_two Int, ← Nat.cast_mul, zero_apply, Int.cast_eq_zero, sub_eq_zero,
    Nat.cast_inj] at this
  rwa [this, Nat.succ_le_iff, two_mul, add_lt_add_iff_left]

Depends on / 依赖: HasPrimitiveVectorWith, Nat.one_le_iff_ne_zero, Weight, chainLength, chainTop, eq_of_le_of_not_lt, exists_isSl2Triple_of_weight_isNonZero, exists_ne_zero, genWeightSpace_chainTopCoeff_add_one_nsmul_add, h_eq_coroot, isSl2.HasPrimitiveVectorWith, isSl2.h_eq_coroot, lie_mem_genWeightSpace_of_mem_genWeightSpac, one_le_iff_ne_zero, x_ne0
-/
lemma chainTopCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) :
    chainTopCoeff α (0 : Weight K H L) = 1 := by
  symm
  apply eq_of_le_of_not_lt
  · rw [Nat.one_le_iff_ne_zero]
    intro e
    exact α.2 (by simpa [e] using!
      genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα)
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α (0 : Weight K H L)).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α (0 : Weight K H L) : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  obtain ⟨k, hk⟩ : exists k : K, k • f =
      (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x := by
    have : (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x in rootSpace H (-α) := by
      convert toEnd_pow_apply_mem hf hx (chainTopCoeff α (0 : Weight K H L) + 1)
      rw [coe_chainTop']; rw [FunLike.coe_zero]; rw [add_zero]; rw [succ_nsmul']; rw [add_assoc]; rw [smul_neg]; rw [neg_add_cancel]; rw [add_zero]
    simpa using! (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using! isSl2.f_ne_zero)).mp
      (finrank_rootSpace_eq_one _ hα.neg) ⟨_, this⟩
  apply_fun (⁅f, ·⁆) at hk
  simp only [lie_smul, lie_self, smul_zero, prim.lie_f_pow_toEnd_f] at hk
  intro e
  refine prim.pow_toEnd_f_ne_zero_of_eq_nat rfl ?_ hk.symm
  have := (apply_coroot_eq_cast' α 0).symm
  simp only [← @Nat.cast_two Int, ← Nat.cast_mul, zero_apply, Int.cast_eq_zero, sub_eq_zero,
    Nat.cast_inj] at this
  rwa [this, Nat.succ_le_iff, two_mul, add_lt_add_iff_left]

/--
lemma `chainBotCoeff_zero_right` / 引理 `chainBotCoeff_zero_right`

English:
lemma chainBotCoeff_zero_right
  given: [Nontrivial L] (hα : α.IsNonZero)
  proof: chainTopCoeff_zero_right (-α) hα.neg

中文:
引理 chainBotCoeff_zero_right
  条件: [非平凡 L] (hα : α.IsNonZero)
  证明: chainTopCoeff_zero_right (-α) hα.neg

Depends on / 依赖: chainTopCoeff_zero_right
-/
lemma chainBotCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) :
    chainBotCoeff α (0 : Weight K H L) = 1 :=
  chainTopCoeff_zero_right (-α) hα.neg

/--
lemma `chainLength_zero_right` / 引理 `chainLength_zero_right`

English:
lemma chainLength_zero_right
  given: [Nontrivial L] (hα : α.IsNonZero)
  statement: chainLength α 0 = 2
  proof: by
  rw [← chainBotCoeff_add_chainTopCoeff]; rw [chainTopCoeff_zero_right α hα]; rw [chainBotCoeff_zero_right α hα]

中文:
引理 chainLength_zero_right
  条件: [非平凡 L] (hα : α.IsNonZero)
  结论: chainLength α 0 = 2
  证明: by
  rw [← chainBotCoeff_add_chainTopCoeff]; rw [chainTopCoeff_zero_right α hα]; rw [chainBotCoeff_zero_right α hα]

Depends on / 依赖: chainBotCoeff_add_chainTopCoeff, chainBotCoeff_zero_right, chainTopCoeff_zero_right
-/
lemma chainLength_zero_right [Nontrivial L] (hα : α.IsNonZero) : chainLength α 0 = 2 := by
  rw [← chainBotCoeff_add_chainTopCoeff]; rw [chainTopCoeff_zero_right α hα]; rw [chainBotCoeff_zero_right α hα]

/--
lemma `rootSpace_two_smul` / 引理 `rootSpace_two_smul`

English:
lemma rootSpace_two_smul
  given: (hα : α.IsNonZero)
  statement: rootSpace H (2 • α) = ⊥
  proof: by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  simpa [chainTopCoeff_zero_right α hα] using
    genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα

中文:
引理 rootSpace_two_smul
  条件: (hα : α.IsNonZero)
  结论: rootSpace H (2 • α) = ⊥
  证明: by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  simpa [chainTopCoeff_zero_right α hα] using
    genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα

Depends on / 依赖: IsEmpty, IsEmpty.elim, Weight, chainTopCoeff_zero_right, genWeightSpace_chainTopCoeff_add_one_nsmul_add, subsingleton_or_nontrivial
-/
lemma rootSpace_two_smul (hα : α.IsNonZero) : rootSpace H (2 • α) = ⊥ := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  simpa [chainTopCoeff_zero_right α hα] using
    genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα

/--
lemma `rootSpace_one_div_two_smul` / 引理 `rootSpace_one_div_two_smul`

English:
lemma rootSpace_one_div_two_smul
  given: (hα : α.IsNonZero)
  statement: rootSpace H ((2⁻¹ : K) • α) = ⊥
  proof: by
  by_contra h
  let W : Weight K H L := ⟨_, h⟩
  have hW : 2 • (W : H -> K) = α := by
    change 2 • (2⁻¹ : K) • (α : H -> K) = α
    rw [← Nat.cast_smul_eq_nsmul K]; rw [smul_smul]; simp
  apply α.genWeightSpace_ne_bot
  have := rootSpace_two_smul W (fun (e : (W : H -> K) = 0) => hα <| by
    apply_fun (2 • ·) at e; simpa [hW] using e)
  rwa [hW] at this

中文:
引理 rootSpace_one_div_two_smul
  条件: (hα : α.IsNonZero)
  结论: rootSpace H ((2⁻¹ : K) • α) = ⊥
  证明: by
  by_contra h
  let W : Weight K H L := ⟨_, h⟩
  have hW : 2 • (W : H -> K) = α := by
    change 2 • (2⁻¹ : K) • (α : H -> K) = α
    rw [← Nat.cast_smul_eq_nsmul K]; rw [smul_smul]; simp
  apply α.genWeightSpace_ne_bot
  have := rootSpace_two_smul W (fun (e : (W : H -> K) = 0) => hα <| by
    apply_fun (2 • ·) at e; simpa [hW] using e)
  rwa [hW] at this

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Weight, apply_fun, cast_smul_eq_nsmul, genWeightSpace_ne_bot, rootSpace_two_smul, smul_smul
-/
lemma rootSpace_one_div_two_smul (hα : α.IsNonZero) : rootSpace H ((2⁻¹ : K) • α) = ⊥ := by
  by_contra h
  let W : Weight K H L := ⟨_, h⟩
  have hW : 2 • (W : H -> K) = α := by
    change 2 • (2⁻¹ : K) • (α : H -> K) = α
    rw [← Nat.cast_smul_eq_nsmul K]; rw [smul_smul]; simp
  apply α.genWeightSpace_ne_bot
  have := rootSpace_two_smul W (fun (e : (W : H -> K) = 0) => hα <| by
    apply_fun (2 • ·) at e; simpa [hW] using e)
  rwa [hW] at this

/--
lemma `eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul` / 引理 `eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul`

English:
lemma eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul
  proof: by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (chainLength α β).even_or_odd with (⟨n, hn⟩ | ⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast]; rw [← Int.cast_natCast (chainTopCoeff α β)]; rw [← Int.cast_sub] at H
    have := (rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [← Int.cast_smul_eq_zsmul K, ← H, ← h, FunLike.coe_zero, add_zero]; exact β.2)
    rw [chainTopCoeff_zero_right α hα]; rw [chainBotCoeff_zero_right α hα]; rw [Nat.cast_one] at this
    set k' : Int := n - chainTopCoeff α β
    subst H
    have : k' in ({-1, 0, 1} : Finset Int) := by
      change k' in Finset.Icc (-1 : Int) (1 : Int)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn]; rw [smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add]; rw [chainBotCoeff_add_chainTopCoeff]; rw [hn]
      lia
    rw [h]; rw [hk]; rw [← Int.cast_smul_eq_zsmul K]; rw [← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (rootSpace_one_div_two_smul α hα)

中文:
引理 eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul
  证明: by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (chainLength α β).even_or_odd with (⟨n, hn⟩ | ⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast]; rw [← Int.cast_natCast (chainTopCoeff α β)]; rw [← Int.cast_sub] at H
    have := (rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [← Int.cast_smul_eq_zsmul K, ← H, ← h, FunLike.coe_zero, add_zero]; exact β.2)
    rw [chainTopCoeff_zero_right α hα]; rw [chainBotCoeff_zero_right α hα]; rw [Nat.cast_one] at this
    set k' : Int := n - chainTopCoeff α β
    subst H
    have : k' in ({-1, 0, 1} : Finset Int) := by
      change k' in Finset.Icc (-1 : Int) (1 : Int)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn]; rw [smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add]; rw [chainBotCoeff_add_chainTopCoeff]; rw [hn]
      lia
    rw [h]; rw [hk]; rw [← Int.cast_smul_eq_zsmul K]; rw [← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (rootSpace_one_div_two_smul α hα)

Depends on / 依赖: Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_sub, IsEmpty, IsEmpty.elim, Nat.cast_mul, Nat.cast_ofNat, OfNat.ofNat_ne_zero, Pi.smul_apply, apply_coroot_eq_cast, cast_mul, cast_natCast, cast_ofNat, cast_sub, chainLength, even_or_odd, mul_comm, mul_eq_mul_left_iff, mul_sub
-/
lemma eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul
    (hα : α.IsNonZero) (k : K) (h : (β : H -> K) = k • α) :
    k = -1 ∨ k = 0 ∨ k = 1 := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (chainLength α β).even_or_odd with (⟨n, hn⟩ | ⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast]; rw [← Int.cast_natCast (chainTopCoeff α β)]; rw [← Int.cast_sub] at H
    have := (rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [← Int.cast_smul_eq_zsmul K, ← H, ← h, FunLike.coe_zero, add_zero]; exact β.2)
    rw [chainTopCoeff_zero_right α hα]; rw [chainBotCoeff_zero_right α hα]; rw [Nat.cast_one] at this
    set k' : Int := n - chainTopCoeff α β
    subst H
    have : k' in ({-1, 0, 1} : Finset Int) := by
      change k' in Finset.Icc (-1 : Int) (1 : Int)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn]; rw [smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add]; rw [chainBotCoeff_add_chainTopCoeff]; rw [hn]
      lia
    rw [h]; rw [hk]; rw [← Int.cast_smul_eq_zsmul K]; rw [← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (rootSpace_one_div_two_smul α hα)

/--
lemma `eq_neg_or_eq_of_eq_smul` / 引理 `eq_neg_or_eq_of_eq_smul`

English:
lemma eq_neg_or_eq_of_eq_smul
  given: (hβ : β.IsNonZero) (k : K) (h : (β : H -> K) = k • α)
  proof: by
  by_cases hα : α.IsZero
  · rw [hα, smul_zero] at h; cases hβ h
  rcases eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul α β hα k h with (rfl | rfl | rfl)
  · exact .inl (by ext; rw [h, neg_one_smul]; rfl)
  · cases hβ (by rwa [zero_smul] at h)
  · exact .inr (by ext; rw [h, one_smul])

中文:
引理 eq_neg_or_eq_of_eq_smul
  条件: (hβ : β.IsNonZero) (k : K) (h : (β : H -> K) = k • α)
  证明: by
  by_cases hα : α.IsZero
  · rw [hα, smul_zero] at h; cases hβ h
  rcases eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul α β hα k h with (rfl | rfl | rfl)
  · exact .inl (by ext; rw [h, neg_one_smul]; rfl)
  · cases hβ (by rwa [zero_smul] at h)
  · exact .inr (by ext; rw [h, one_smul])

Depends on / 依赖: IsZero, eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul, neg_one_smul, one_smul, smul_zero, zero_smul
-/
lemma eq_neg_or_eq_of_eq_smul (hβ : β.IsNonZero) (k : K) (h : (β : H -> K) = k • α) :
    β = -α ∨ β = α := by
  by_cases hα : α.IsZero
  · rw [hα, smul_zero] at h; cases hβ h
  rcases eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul α β hα k h with (rfl | rfl | rfl)
  · exact .inl (by ext; rw [h, neg_one_smul]; rfl)
  · cases hβ (by rwa [zero_smul] at h)
  · exact .inr (by ext; rw [h, one_smul])

/--
Definition of `reflectRoot` / `reflectRoot` 的定义

English:
definition reflectRoot
  signature: (α β : Weight K H L)
  body: β - β (coroot α) • α
  genWeightSpace_ne_bot' := by
    by_cases hα : α.IsZero
    · simpa [hα.eq] using β.genWeightSpace_ne_bot
    rw [sub_eq_neg_add]; rw [apply_coroot_eq_cast α β]; rw [← neg_smul]; rw [← Int.cast_neg]; rw [Int.cast_smul_eq_zsmul]; rw [rootSpace_zsmul_add_ne_bot_iff α β hα]
    lia

中文:
定义 reflectRoot
  签名: (α β : Weight K H L)
  定义体: β - β (coroot α) • α
  genWeightSpace_ne_bot' := by
    by_cases hα : α.IsZero
    · simpa [hα.eq] using β.genWeightSpace_ne_bot
    rw [sub_eq_neg_add]; rw [apply_coroot_eq_cast α β]; rw [← neg_smul]; rw [← Int.cast_neg]; rw [Int.cast_smul_eq_zsmul]; rw [rootSpace_zsmul_add_ne_bot_iff α β hα]
    lia

Depends on / 依赖: coroot
-/
def reflectRoot (α β : Weight K H L) : Weight K H L where
  toFun := β - β (coroot α) • α
  genWeightSpace_ne_bot' := by
    by_cases hα : α.IsZero
    · simpa [hα.eq] using β.genWeightSpace_ne_bot
    rw [sub_eq_neg_add]; rw [apply_coroot_eq_cast α β]; rw [← neg_smul]; rw [← Int.cast_neg]; rw [Int.cast_smul_eq_zsmul]; rw [rootSpace_zsmul_add_ne_bot_iff α β hα]
    lia

/--
lemma `reflectRoot_isNonZero` / 引理 `reflectRoot_isNonZero`

English:
lemma reflectRoot_isNonZero
  given: (α β : Weight K H L) (hβ : β.IsNonZero)
  proof: by
  intro e
  have : β (coroot α) = 0 := by
    by_cases hα : α.IsZero
    · simp [coroot_eq_zero_iff.mpr hα]
    simpa [root_apply_coroot hα, mul_two] using congr_fun (sub_eq_zero.mp e) (coroot α)
  have : reflectRoot α β = β := by ext; simp [reflectRoot, this]
  exact hβ (this ▸ e)

中文:
引理 reflectRoot_isNonZero
  条件: (α β : Weight K H L) (hβ : β.IsNonZero)
  证明: by
  intro e
  have : β (coroot α) = 0 := by
    by_cases hα : α.IsZero
    · simp [coroot_eq_zero_iff.mpr hα]
    simpa [root_apply_coroot hα, mul_two] using congr_fun (sub_eq_zero.mp e) (coroot α)
  have : reflectRoot α β = β := by ext; simp [reflectRoot, this]
  exact hβ (this ▸ e)

Depends on / 依赖: IsZero, congr_fun, coroot, coroot_eq_zero_iff, coroot_eq_zero_iff.mpr, mul_two, reflectRoot, root_apply_coroot, sub_eq_zero, sub_eq_zero.mp
-/
lemma reflectRoot_isNonZero (α β : Weight K H L) (hβ : β.IsNonZero) :
    (reflectRoot α β).IsNonZero := by
  intro e
  have : β (coroot α) = 0 := by
    by_cases hα : α.IsZero
    · simp [coroot_eq_zero_iff.mpr hα]
    simpa [root_apply_coroot hα, mul_two] using congr_fun (sub_eq_zero.mp e) (coroot α)
  have : reflectRoot α β = β := by ext; simp [reflectRoot, this]
  exact hβ (this ▸ e)

variable (H)

/--
Definition of `rootSystem` / `rootSystem` 的定义

English:
definition rootSystem
  signature: :
  body: RootPairing.mk''
    .id
    { toFun := (↑)
      inj' := by
        intro α β h; ext x; simpa using LinearMap.congr_fun h x }
    { toFun := coroot ∘ (↑)
      inj' := by rintro ⟨α, hα⟩ ⟨β, hβ⟩ h; simpa using h }
    (fun ⟨α, hα⟩ => by simpa using root_apply_coroot <| by simpa using hα)
    (by
      rintro ⟨α, hα⟩ - ⟨⟨β, hβ⟩, rfl⟩
      simpa using
⟨reflectRoot α β, by simpa using reflectRoot_isNonZero α β by simpa using hβ, rfl⟩)
    (by convert! span_weight_isNonZero_eq_top K L H; ext; simp)

中文:
定义 rootSystem
  签名: :
  定义体: RootPairing.mk''
    .id
    { toFun := (↑)
      inj' := by
        intro α β h; ext x; simpa using LinearMap.congr_fun h x }
    { toFun := coroot ∘ (↑)
      inj' := by rintro ⟨α, hα⟩ ⟨β, hβ⟩ h; simpa using h }
    (fun ⟨α, hα⟩ => by simpa using root_apply_coroot <| by simpa using hα)
    (by
      rintro ⟨α, hα⟩ - ⟨⟨β, hβ⟩, rfl⟩
      simpa using
⟨reflectRoot α β, by simpa using reflectRoot_isNonZero α β by simpa using hβ, rfl⟩)
    (by convert! span_weight_isNonZero_eq_top K L H; ext; simp)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, RootPairing, RootPairing.mk, congr_fun, convert, coroot, reflectRoot, reflectRoot_isNonZero, root_apply_coroot, span_weight_isNonZero_eq_top
-/
def rootSystem :
    RootPairing H.root K (Dual K H) H :=
  RootPairing.mk''
    .id
    { toFun := (↑)
      inj' := by
        intro α β h; ext x; simpa using LinearMap.congr_fun h x }
    { toFun := coroot ∘ (↑)
      inj' := by rintro ⟨α, hα⟩ ⟨β, hβ⟩ h; simpa using h }
    (fun ⟨α, hα⟩ => by simpa using root_apply_coroot <| by simpa using hα)
    (by
      rintro ⟨α, hα⟩ - ⟨⟨β, hβ⟩, rfl⟩
      simpa using
⟨reflectRoot α β, by simpa using reflectRoot_isNonZero α β by simpa using hβ, rfl⟩)
    (by convert! span_weight_isNonZero_eq_top K L H; ext; simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (rootSystem H).IsRootSystem
  body: RootPairing.isRootSystem_mk'' fun α β =>
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

@[simp]

中文:
实例 :
  签名: (rootSystem H).是RootSystem
  定义体: RootPairing.isRootSystem_mk'' fun α β =>
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

@[simp]

Depends on / 依赖: RootPairing, RootPairing.isRootSystem_mk, apply_coroot_eq_cast, chainBotCoeff, chainTopCoeff, isRootSystem_mk
-/
instance : (rootSystem H).IsRootSystem :=
  RootPairing.isRootSystem_mk'' fun α β =>
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

@[simp]
/--
lemma `corootForm_rootSystem_eq_killing` / 引理 `corootForm_rootSystem_eq_killing`

English:
lemma corootForm_rootSystem_eq_killing
  proof: by
  rw [restrict_killingForm_eq_sum]; rw [RootPairing.CorootForm]; rw [← Finset.sum_coe_sort (s := H.root)]
  rfl

中文:
引理 corootForm_rootSystem_eq_killing
  证明: by
  rw [restrict_killingForm_eq_sum]; rw [RootPairing.CorootForm]; rw [← Finset.sum_coe_sort (s := H.root)]
  rfl

Depends on / 依赖: CorootForm, Finset, Finset.sum_coe_sort, H.root, RootPairing, RootPairing.CorootForm, restrict_killingForm_eq_sum, sum_coe_sort
-/
lemma corootForm_rootSystem_eq_killing :
    (rootSystem H).CorootForm = (killingForm K L).restrict H := by
  rw [restrict_killingForm_eq_sum]; rw [RootPairing.CorootForm]; rw [← Finset.sum_coe_sort (s := H.root)]
  rfl

/--
lemma `rootSystem_toLinearMap_apply` / 引理 `rootSystem_toLinearMap_apply`

English:
lemma rootSystem_toLinearMap_apply
  given: (f x)
  statement: (rootSystem H).toLinearMap f x = f x
  proof: rfl

中文:
引理 rootSystem_toLinearMap_apply
  条件: (f x)
  结论: (rootSystem H).toLinearMap f x = f x
  证明: rfl
-/
@[simp] lemma rootSystem_toLinearMap_apply (f x) : (rootSystem H).toLinearMap f x = f x := rfl
/--
lemma `rootSystem_pairing_apply` / 引理 `rootSystem_pairing_apply`

English:
lemma rootSystem_pairing_apply
  given: (α β)
  statement: (rootSystem H).pairing β α = β.1 (coroot α.1)
  proof: rfl

中文:
引理 rootSystem_pairing_apply
  条件: (α β)
  结论: (rootSystem H).pairing β α = β.1 (coroot α.1)
  证明: rfl
-/
@[simp] lemma rootSystem_pairing_apply (α β) : (rootSystem H).pairing β α = β.1 (coroot α.1) := rfl
/--
lemma `rootSystem_root_apply` / 引理 `rootSystem_root_apply`

English:
lemma rootSystem_root_apply
  given: (α)
  statement: (rootSystem H).root α = α
  proof: rfl

中文:
引理 rootSystem_root_apply
  条件: (α)
  结论: (rootSystem H).root α = α
  证明: rfl
-/
@[simp] lemma rootSystem_root_apply (α) : (rootSystem H).root α = α := rfl
/--
lemma `rootSystem_coroot_apply` / 引理 `rootSystem_coroot_apply`

English:
lemma rootSystem_coroot_apply
  given: (α)
  statement: (rootSystem H).coroot α = coroot α
  proof: rfl

中文:
引理 rootSystem_coroot_apply
  条件: (α)
  结论: (rootSystem H).coroot α = coroot α
  证明: rfl
-/
@[simp] lemma rootSystem_coroot_apply (α) : (rootSystem H).coroot α = coroot α := rfl

open LieSubmodule in
@[simp]
/--
lemma `biSup_corootSpace_eq_top` / 引理 `biSup_corootSpace_eq_top`

English:
lemma biSup_corootSpace_eq_top
  proof: by
  simp only [← toSubmodule_inj, top_toSubmodule, iSup_toSubmodule,
    ← RootPairing.IsRootSystem.span_coroot_eq_top (P := rootSystem H),
    coe_corootSpace_eq_span_singleton, Submodule.iSup_span]
  congr
  ext α
  simp [eq_comm]

中文:
引理 biSup_corootSpace_eq_top
  证明: by
  simp only [← toSubmodule_inj, top_toSubmodule, iSup_toSubmodule,
    ← RootPairing.IsRootSystem.span_coroot_eq_top (P := rootSystem H),
    coe_corootSpace_eq_span_singleton, Submodule.iSup_span]
  congr
  ext α
  simp [eq_comm]

Depends on / 依赖: IsRootSystem, RootPairing, RootPairing.IsRootSystem.span_coroot_eq_top, Submodule, Submodule.iSup_span, coe_corootSpace_eq_span_singleton, eq_comm, iSup_span, iSup_toSubmodule, rootSystem, span_coroot_eq_top, toSubmodule_inj, top_toSubmodule
-/
lemma biSup_corootSpace_eq_top :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤ := by
  simp only [← toSubmodule_inj, top_toSubmodule, iSup_toSubmodule,
    ← RootPairing.IsRootSystem.span_coroot_eq_top (P := rootSystem H),
    coe_corootSpace_eq_span_singleton, Submodule.iSup_span]
  congr
  ext α
  simp [eq_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `biSup_corootSubmodule_eq_cartan` / 引理 `biSup_corootSubmodule_eq_cartan`

English:
lemma biSup_corootSubmodule_eq_cartan
  proof: by
  suffices ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤ from
    le_antisymm (by simp) (by simp [← LieSubmodule.map_iSup, this])
  simp

中文:
引理 biSup_corootSubmodule_eq_cartan
  证明: by
  suffices ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤ from
    le_antisymm (by simp) (by simp [← LieSubmodule.map_iSup, this])
  simp

Depends on / 依赖: IsNonZero, LieSubmodule, LieSubmodule.map_iSup, Weight, corootSpace, le_antisymm, map_iSup
-/
lemma biSup_corootSubmodule_eq_cartan :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSubmodule α = H.toLieSubmodule := by
  suffices ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤ from
    le_antisymm (by simp) (by simp [← LieSubmodule.map_iSup, this])
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (rootSystem H).IsCrystallographic
  body: ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

中文:
实例 :
  签名: (rootSystem H).IsCrystallographic
  定义体: ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

Depends on / 依赖: apply_coroot_eq_cast, chainBotCoeff, chainTopCoeff
-/
instance : (rootSystem H).IsCrystallographic where
  exists_value α β :=
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (rootSystem H).IsReduced
  body: by
    intro ⟨α, hα⟩ ⟨β, hβ⟩ e
    rw [LinearIndependent.pair_iff' ((rootSystem H).ne_zero _)]; rw [not_forall] at e
    simp only [rootSystem_root_apply, ne_eq, not_not] at e
    obtain ⟨u, hu⟩ := e
    obtain (h | h) := eq_neg_or_eq_of_eq_smul α β (by simpa using hβ) u
      (by ext x; exact DFunLike.congr_fun hu.symm x)
    · right; ext x; simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun h.symm x
    · left; ext x; simpa using DFunLike.congr_fun h.symm x

中文:
实例 :
  签名: (rootSystem H).是既约
  定义体: by
    intro ⟨α, hα⟩ ⟨β, hβ⟩ e
    rw [LinearIndependent.pair_iff' ((rootSystem H).ne_zero _)]; rw [not_forall] at e
    simp only [rootSystem_root_apply, ne_eq, not_not] at e
    obtain ⟨u, hu⟩ := e
    obtain (h | h) := eq_neg_or_eq_of_eq_smul α β (by simpa using hβ) u
      (by ext x; exact DFunLike.congr_fun hu.symm x)
    · right; ext x; simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun h.symm x
    · left; ext x; simpa using DFunLike.congr_fun h.symm x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, LinearIndependent, LinearIndependent.pair_iff, congr_fun, eq_neg_or_eq_of_eq_smul, h.symm, hu.symm, ne_eq, ne_zero, neg_eq_iff_eq_neg, not_forall, not_not, pair_iff, rootSystem, rootSystem_root_apply
-/
instance : (rootSystem H).IsReduced where
  eq_or_eq_neg := by
    intro ⟨α, hα⟩ ⟨β, hβ⟩ e
    rw [LinearIndependent.pair_iff' ((rootSystem H).ne_zero _)]; rw [not_forall] at e
    simp only [rootSystem_root_apply, ne_eq, not_not] at e
    obtain ⟨u, hu⟩ := e
    obtain (h | h) := eq_neg_or_eq_of_eq_smul α β (by simpa using hβ) u
      (by ext x; exact DFunLike.congr_fun hu.symm x)
    · right; ext x; simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun h.symm x
    · left; ext x; simpa using DFunLike.congr_fun h.symm x

end LieAlgebra.IsKilling
