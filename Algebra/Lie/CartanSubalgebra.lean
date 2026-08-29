/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Normalizer

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `LieSubmodule.IsUcsLimit`
  * `LieSubalgebra.IsCartanSubalgebra`
  * `LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/

@[expose] public section


universe u v w w₁ w₂

variable {R : Type u} {L : Type v}
variable [CommRing R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

/--
Definition of `LieSubmodule.IsUcsLimit` / `LieSubmodule.IsUcsLimit` 的定义

English:
definition LieSubmodule.IsUcsLimit
  signature: {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]
  body: exists k, forall l, k <= l -> (⊥ : LieSubmodule R L M).ucs l = N

中文:
定义 Lie子模.IsUcsLimit
  签名: {M : 类型} [加法交换群 M] [模 R M] [Lie环模 L M]
  定义体: exists k, forall l, k <= l -> (⊥ : LieSubmodule R L M).ucs l = N

Depends on / 依赖: LieSubmodule
-/
def LieSubmodule.IsUcsLimit {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] (N : LieSubmodule R L M) : Prop :=
  exists k, forall l, k <= l -> (⊥ : LieSubmodule R L M).ucs l = N

namespace LieSubalgebra

/--
Definition of `IsCartanSubalgebra` / `IsCartanSubalgebra` 的定义

English:
class IsCartanSubalgebra
  parameters: : Prop where
  axioms and operations (2):
    - nilpotent : LieRing.IsNilpotent H
    - self_normalizing : H.normalizer = H

中文:
类 是Cartan子代数
  参数: : 命题 where
  公理与运算 (2 个):
    - nilpotent : Lie环.是幂零 H
    - self_normalizing : H.normalizer = H
-/
class IsCartanSubalgebra : Prop where
  nilpotent : LieRing.IsNilpotent H
  self_normalizing : H.normalizer = H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [H.IsCartanSubalgebra]
  signature: : LieRing.IsNilpotent H
  body: IsCartanSubalgebra.nilpotent

@[simp]

中文:
实例 [H.是Cartan子代数]
  签名: : Lie环.是幂零 H
  定义体: IsCartanSubalgebra.nilpotent

@[simp]

Depends on / 依赖: IsCartanSubalgebra, IsCartanSubalgebra.nilpotent, nilpotent
-/
instance [H.IsCartanSubalgebra] : LieRing.IsNilpotent H :=
  IsCartanSubalgebra.nilpotent

@[simp]
/--
theorem `normalizer_eq_self_of_isCartanSubalgebra` / 定理 `normalizer_eq_self_of_isCartanSubalgebra`

English:
theorem normalizer_eq_self_of_isCartanSubalgebra
  given: (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [coe_normalizer_eq_normalizer]; rw [IsCartanSubalgebra.self_normalizing]; rw [coe_toLieSubmodule]

@[simp]

中文:
定理 normalizer_eq_self_of_isCartanSubalgebra
  条件: (H : Lie子代数 R L) [H.是Cartan子代数]
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [coe_normalizer_eq_normalizer]; rw [IsCartanSubalgebra.self_normalizing]; rw [coe_toLieSubmodule]

@[simp]

Depends on / 依赖: IsCartanSubalgebra, IsCartanSubalgebra.self_normalizing, LieSubmodule, LieSubmodule.toSubmodule_inj, coe_normalizer_eq_normalizer, coe_toLieSubmodule, self_normalizing, toSubmodule_inj
-/
theorem normalizer_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H.toLieSubmodule.normalizer = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [coe_normalizer_eq_normalizer]; rw [IsCartanSubalgebra.self_normalizing]; rw [coe_toLieSubmodule]

@[simp]
/--
theorem `ucs_eq_self_of_isCartanSubalgebra` / 定理 `ucs_eq_self_of_isCartanSubalgebra`

English:
theorem ucs_eq_self_of_isCartanSubalgebra
  given: (H : LieSubalgebra R L) [H.IsCartanSubalgebra] (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]

中文:
定理 ucs_eq_self_of_isCartanSubalgebra
  条件: (H : Lie子代数 R L) [H.是Cartan子代数] (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]
-/
theorem ucs_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] (k : Nat) :
    H.toLieSubmodule.ucs k = H.toLieSubmodule := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]

/--
theorem `isCartanSubalgebra_iff_isUcsLimit` / 定理 `isCartanSubalgebra_iff_isUcsLimit`

English:
theorem isCartanSubalgebra_iff_isUcsLimit
  statement: H.IsCartanSubalgebra ↔ H.toLieSubmodule.IsUcsLimit
  proof: by
  constructor
  · intro h
    have h₁ : LieRing.IsNilpotent H := by infer_instance
    obtain ⟨k, hk⟩ := H.toLieSubmodule.isNilpotent_iff_exists_self_le_ucs.mp h₁
    replace hk : H.toLieSubmodule = LieSubmodule.ucs k ⊥ :=
      le_antisymm hk
        (LieSubmodule.ucs_le_of_normalizer_eq_self H.

中文:
定理 isCartanSubalgebra_iff_isUcsLimit
  结论: H.是Cartan子代数 ↔ H.toLieSubmodule.IsUcsLimit
  证明: by
  constructor
  · intro h
    have h₁ : LieRing.IsNilpotent H := by infer_instance
    obtain ⟨k, hk⟩ := H.toLieSubmodule.isNilpotent_iff_exists_self_le_ucs.mp h₁
    replace hk : H.toLieSubmodule = LieSubmodule.ucs k ⊥ :=
      le_antisymm hk
        (LieSubmodule.ucs_le_of_normalizer_eq_self H.

Depends on / 依赖: H.normalizer_eq_self_of_isCartanSubalgebra, H.toLieSubmodule, H.toLieSubmodule.isNilpotent_iff_exists_self_le_ucs.mp, IsNilpotent, LieRing, LieRing.IsNilpotent, LieSubalgebra, LieSubalgebra.ucs_eq_self_of_isCartanSubalgebra, LieSubmodule, LieSubmodule.ucs, LieSubmodule.ucs_add, LieSubmodule.ucs_le_of_normalizer_eq_self, Nat.sub_add_cancel, infer_instance, isNilpotent_iff_exists_self_le_ucs, le_antisymm, nilpotent, normalizer_eq_self_of_isCartanSubalgebra, replace, sub_add_cancel
-/
theorem isCartanSubalgebra_iff_isUcsLimit : H.IsCartanSubalgebra ↔ H.toLieSubmodule.IsUcsLimit := by
  constructor
  · intro h
    have h₁ : LieRing.IsNilpotent H := by infer_instance
    obtain ⟨k, hk⟩ := H.toLieSubmodule.isNilpotent_iff_exists_self_le_ucs.mp h₁
    replace hk : H.toLieSubmodule = LieSubmodule.ucs k ⊥ :=
      le_antisymm hk
        (LieSubmodule.ucs_le_of_normalizer_eq_self H.normalizer_eq_self_of_isCartanSubalgebra k)
    refine ⟨k, fun l hl => ?_⟩
    rw [← Nat.sub_add_cancel hl]; rw [LieSubmodule.ucs_add]; rw [← hk]; rw [LieSubalgebra.ucs_eq_self_of_isCartanSubalgebra]
  · rintro ⟨k, hk⟩
    exact
      { nilpotent := by
          dsimp only [LieRing.IsNilpotent]
          -- The instance for the second `H` in the goal is `lieRingSelfModule`
          -- but `rw` expects it to be `H.toLieSubmodule.instLieRingModuleSubtypeMem`,
          -- and these are not reducibly defeq.
          erw [H.toLieSubmodule.isNilpotent_iff_exists_lcs_eq_bot]
          use k
          rw [_root_.eq_bot_iff]; rw [LieSubmodule.lcs_le_iff]; rw [hk k (le_refl k)]
        self_normalizing := by
          have hk' := hk (k + 1) k.le_succ
          rw [LieSubmodule.ucs_succ]; rw [hk k (le_refl k)] at hk'
          rw [← LieSubalgebra.toSubmodule_inj]; rw [← LieSubalgebra.coe_normalizer_eq_normalizer]; rw [hk']; rw [LieSubalgebra.coe_toLieSubmodule] }

/--
lemma `ne_bot_of_isCartanSubalgebra` / 引理 `ne_bot_of_isCartanSubalgebra`

English:
lemma ne_bot_of_isCartanSubalgebra
  given: [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
  proof: by
  intro e
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have : x in H.normalizer := by simp [LieSubalgebra.mem_normalizer_iff, e]
  exact hx (by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing, e] at this)

中文:
引理 ne_bot_of_isCartanSubalgebra
  条件: [非平凡 L] (H : Lie子代数 R L) [H.是Cartan子代数]
  证明: by
  intro e
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have : x in H.normalizer := by simp [LieSubalgebra.mem_normalizer_iff, e]
  exact hx (by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing, e] at this)

Depends on / 依赖: H.normalizer, IsCartanSubalgebra, LieSubalgebra, LieSubalgebra.IsCartanSubalgebra.self_normalizing, LieSubalgebra.mem_normalizer_iff, exists_ne, mem_normalizer_iff, normalizer, self_normalizing
-/
lemma ne_bot_of_isCartanSubalgebra [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H != ⊥ := by
  intro e
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have : x in H.normalizer := by simp [LieSubalgebra.mem_normalizer_iff, e]
  exact hx (by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing, e] at this)

instance (priority := 500) [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    Nontrivial H := by
  refine (subsingleton_or_nontrivial H).elim (fun inst => False.elim ?_) id
  apply ne_bot_of_isCartanSubalgebra H
  rw [eq_bot_iff]
  exact fun x hx => congr_arg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : H) 0)

end LieSubalgebra

@[simp]
/--
theorem `LieIdeal.normalizer_eq_top` / 定理 `LieIdeal.normalizer_eq_top`

English:
theorem LieIdeal.normalizer_eq_top
  statement: {R : Type u} {L : Type v} [CommRing R] [LieRing L]
  proof: by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true] using!
    fun y hy => I.lie_mem hy

中文:
定理 LieIdeal.normalizer_eq_top
  结论: {R : 类型u} {L : 类型v} [交换环 R] [Lie环 L]
  证明: by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true] using!
    fun y hy => I.lie_mem hy

Depends on / 依赖: I.lie_mem, LieSubalgebra, LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true, lie_mem, mem_normalizer_iff, mem_top
-/
theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true] using!
    fun y hy => I.lie_mem hy

open LieIdeal

/--
Instance `LieAlgebra.top_isCartanSubalgebra_of_nilpotent` / 实例 `LieAlgebra.top_isCartanSubalgebra_of_nilpotent`

English:
instance LieAlgebra.top_isCartanSubalgebra_of_nilpotent
  signature: [LieRing.IsNilpotent L]
  body: inferInstance
  self_normalizing := by rw [← top_toLieSubalgebra, normalizer_eq_top, top_toLieSubalgebra]

中文:
实例 Lie代数.top_isCartanSubalgebra_of_nilpotent
  签名: [Lie环.是幂零 L]
  定义体: inferInstance
  self_normalizing := by rw [← top_toLieSubalgebra, normalizer_eq_top, top_toLieSubalgebra]
-/
instance LieAlgebra.top_isCartanSubalgebra_of_nilpotent [LieRing.IsNilpotent L] :
    LieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where
  nilpotent := inferInstance
  self_normalizing := by rw [← top_toLieSubalgebra, normalizer_eq_top, top_toLieSubalgebra]
