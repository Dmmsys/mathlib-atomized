/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!

# Main definitions and results

In a field extension `K/k`

* `FiniteGaloisIntermediateField` : The type of intermediate fields of `K/k`
  that are finite and Galois over `k`

* `adjoin` : The finite Galois intermediate field obtained from the normal closure of adjoining a
  finite `s : Set K` to `k`.

## TODO

* `FiniteGaloisIntermediateField` should be a `ConditionallyCompleteLattice` but isn't proved yet.

-/

@[expose] public section

open IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/--
Definition of `FiniteGaloisIntermediateField` / `FiniteGaloisIntermediateField` 的定义

English:
structure FiniteGaloisIntermediateField
  parameters: extends IntermediateField k K
  extends: IntermediateField k K
  axioms and operations (2):
    - [finiteDimensional : FiniteDimensional k toIntermediateField]
    - [isGalois : IsGalois k toIntermediateField]

中文:
结构 有限Galois中间域
  参数: extends 中间域 k K
  继承: 中间域 k K
  公理与运算 (2 个):
    - [finiteDimensional : 有限维 k to整数ermediateField]
    - [isGalois : 是Galois k to整数ermediateField]
-/
structure FiniteGaloisIntermediateField extends IntermediateField k K where
  [finiteDimensional : FiniteDimensional k toIntermediateField]
  [isGalois : IsGalois k toIntermediateField]

namespace FiniteGaloisIntermediateField

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K)
  body: toIntermediateField

中文:
实例 :
  签名: Coe (有限Galois中间域 k K) (中间域 k K)
  定义体: toIntermediateField

Depends on / 依赖: toIntermediateField
-/
instance : Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K) where
  coe := toIntermediateField

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (FiniteGaloisIntermediateField k K) (Type _)
  body: L.toIntermediateField

中文:
实例 :
  签名: CoeSort (有限Galois中间域 k K) (类型 _)
  定义体: L.toIntermediateField

Depends on / 依赖: L.toIntermediateField, toIntermediateField
-/
instance : CoeSort (FiniteGaloisIntermediateField k K) (Type _) where
  coe L := L.toIntermediateField

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L :=
  L.finiteDimensional

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L := L.isGalois

variable {k K}

/--
lemma `val_injective` / 引理 `val_injective`

English:
lemma val_injective
  statement: Function.Injective (toIntermediateField (k := k) (K := K))
  proof: by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

中文:
引理 val_injective
  结论: 函数.单射 (to整数ermediateField (k := k) (K := K))
  证明: by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

Depends on / 依赖: mk.injEq
-/
lemma val_injective : Function.Injective (toIntermediateField (k := k) (K := K)) := by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

/-- Turns the collection of finite Galois IntermediateFields of `K/k` into a lattice. -/
instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊔ L₂) where

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₁] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₁) inf_le_left).toLinearMap
    (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₁) inf_le_left).toRingHom.injective

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₂] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₂) inf_le_right).toLinearMap
    (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₂) inf_le_right).injective

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₁] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_left)

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₂] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_right)

instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊓ L₂) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (FiniteGaloisIntermediateField k K)
  body: .mk L₁ ⊔ L₂

中文:
实例 :
  签名: 最大值 (有限Galois中间域 k K)
  定义体: .mk L₁ ⊔ L₂
-/
instance : Max (FiniteGaloisIntermediateField k K) where
max L₁ L₂ := .mk L₁ ⊔ L₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (FiniteGaloisIntermediateField k K)
  body: .mk L₁ ⊓ L₂

中文:
实例 :
  签名: 最小值 (有限Galois中间域 k K)
  定义体: .mk L₁ ⊓ L₂
-/
instance : Min (FiniteGaloisIntermediateField k K) where
min L₁ L₂ := .mk L₁ ⊓ L₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (FiniteGaloisIntermediateField k K)
  body: PartialOrder.lift _ val_injective

中文:
实例 :
  签名: 偏序 (有限Galois中间域 k K)
  定义体: PartialOrder.lift _ val_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, val_injective
-/
instance : PartialOrder (FiniteGaloisIntermediateField k K) :=
  PartialOrder.lift _ val_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (FiniteGaloisIntermediateField k K)
  body: val_injective.lattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 :
  签名: 格 (有限Galois中间域 k K)
  定义体: val_injective.lattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: lattice, val_injective, val_injective.lattice
-/
instance : Lattice (FiniteGaloisIntermediateField k K) :=
  val_injective.lattice _ .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (FiniteGaloisIntermediateField k K)
  body: .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

@[simp]

中文:
实例 :
  签名: 有底序 (有限Galois中间域 k K)
  定义体: .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

@[simp]
-/
instance : OrderBot (FiniteGaloisIntermediateField k K) where
  bot := .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

@[simp]
/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: (L₁ L₂ : FiniteGaloisIntermediateField k K)
  proof: Iff.rfl

中文:
引理 le_iff
  条件: (L₁ L₂ : 有限Galois中间域 k K)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_iff (L₁ L₂ : FiniteGaloisIntermediateField k K) :
    L₁ <= L₂ ↔ L₁.toIntermediateField <= L₂.toIntermediateField :=
  Iff.rfl

variable (k) in
/--
Definition of `adjoin` / `adjoin` 的定义

English:
definition adjoin
  signature: [IsGalois k K] (s : Set K) [Finite s]
  body: {
  normalClosure k (IntermediateField.adjoin k (s : Set K)) K with
  finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) :=
IntermediateField.finiteDimensional_adjoin fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    normalClo

中文:
定义 adjoin
  签名: [是Galois k K] (s : 集合 K) [有限 s]
  定义体: {
  normalClosure k (IntermediateField.adjoin k (s : Set K)) K with
  finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) :=
IntermediateField.finiteDimensional_adjoin fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    normalClo
-/
noncomputable def adjoin [IsGalois k K] (s : Set K) [Finite s] :
    FiniteGaloisIntermediateField k K := {
  normalClosure k (IntermediateField.adjoin k (s : Set K)) K with
  finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) :=
IntermediateField.finiteDimensional_adjoin fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    normalClosure.is_finiteDimensional k (IntermediateField.adjoin k (s : Set K)) K
  isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k (s : Set K)) K }

@[simp]
/--
lemma `adjoin_val` / 引理 `adjoin_val`

English:
lemma adjoin_val
  given: [IsGalois k K] (s : Set K) [Finite s]
  proof: rfl

中文:
引理 adjoin_val
  条件: [是Galois k K] (s : 集合 K) [有限 s]
  证明: rfl
-/
lemma adjoin_val [IsGalois k K] (s : Set K) [Finite s] :
    (FiniteGaloisIntermediateField.adjoin k s) =
    normalClosure k (IntermediateField.adjoin k s) K :=
  rfl

variable (k) in
/--
lemma `subset_adjoin` / 引理 `subset_adjoin`

English:
lemma subset_adjoin
  given: [IsGalois k K] (s : Set K) [Finite s]
  proof: (IntermediateField.subset_adjoin k s).trans (IntermediateField.le_normalClosure _)

中文:
引理 subset_adjoin
  条件: [是Galois k K] (s : 集合 K) [有限 s]
  证明: (IntermediateField.subset_adjoin k s).trans (IntermediateField.le_normalClosure _)

Depends on / 依赖: IntermediateField, IntermediateField.le_normalClosure, IntermediateField.subset_adjoin, le_normalClosure, subset_adjoin
-/
lemma subset_adjoin [IsGalois k K] (s : Set K) [Finite s] :
    s subseteq (adjoin k s).toIntermediateField :=
  (IntermediateField.subset_adjoin k s).trans (IntermediateField.le_normalClosure _)

/--
theorem `adjoin_simple_le_iff` / 定理 `adjoin_simple_le_iff`

English:
theorem adjoin_simple_le_iff
  given: [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K}
  proof: by
  simp only [le_iff, adjoin_val, IntermediateField.normalClosure_le_iff_of_normal,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]

@[simp]

中文:
定理 adjoin_simple_le_iff
  条件: [是Galois k K] {x : K} {L : 有限Galois中间域 k K}
  证明: by
  simp only [le_iff, adjoin_val, IntermediateField.normalClosure_le_iff_of_normal,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.adjoin_le_iff, IntermediateField.normalClosure_le_iff_of_normal, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, adjoin_le_iff, adjoin_val, le_iff, mem_coe, normalClosure_le_iff_of_normal, singleton_subset_iff
-/
theorem adjoin_simple_le_iff [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} :
    adjoin k {x} <= L ↔ x in L.toIntermediateField := by
  simp only [le_iff, adjoin_val, IntermediateField.normalClosure_le_iff_of_normal,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]

@[simp]
/--
theorem `adjoin_map` / 定理 `adjoin_map`

English:
theorem adjoin_map
  given: [IsGalois k K] (f : K ->ₐ[k] K) (s : Set K) [Finite s]
  proof: by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map]; rw [IntermediateField.normalClosure_map_eq]

@[simp]

中文:
定理 adjoin_map
  条件: [是Galois k K] (f : K ->ₐ[k] K) (s : 集合 K) [有限 s]
  证明: by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map]; rw [IntermediateField.normalClosure_map_eq]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.adjoin_map, IntermediateField.normalClosure_map_eq, adjoin_map, adjoin_val, normalClosure_map_eq, val_injective
-/
theorem adjoin_map [IsGalois k K] (f : K ->ₐ[k] K) (s : Set K) [Finite s] :
    adjoin k (f '' s) = adjoin k s := by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map]; rw [IntermediateField.normalClosure_map_eq]

@[simp]
/--
theorem `adjoin_simple_map_algHom` / 定理 `adjoin_simple_map_algHom`

English:
theorem adjoin_simple_map_algHom
  given: [IsGalois k K] (f : K ->ₐ[k] K) (x : K)
  proof: by
  simpa only [Set.image_singleton] using adjoin_map f { x }

@[simp]

中文:
定理 adjoin_simple_map_algHom
  条件: [是Galois k K] (f : K ->ₐ[k] K) (x : K)
  证明: by
  simpa only [Set.image_singleton] using adjoin_map f { x }

@[simp]

Depends on / 依赖: Set.image_singleton, adjoin_map, image_singleton
-/
theorem adjoin_simple_map_algHom [IsGalois k K] (f : K ->ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} := by
  simpa only [Set.image_singleton] using adjoin_map f { x }

@[simp]
/--
theorem `adjoin_simple_map_algEquiv` / 定理 `adjoin_simple_map_algEquiv`

English:
theorem adjoin_simple_map_algEquiv
  given: [IsGalois k K] (f : Gal(K/k)) (x : K)
  proof: adjoin_simple_map_algHom (f : K ->ₐ[k] K) x

nonrec lemma mem_fixingSubgroup_iff (α : Gal(K/k)) (L : FiniteGaloisIntermediateField k K) :
    α in L.fixingSubgroup ↔ α.restrictNormalHom L = 1 := by
  simp [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff, AlgEquiv.ext_iff, Subtype.ext_iff,
 

中文:
定理 adjoin_simple_map_algEquiv
  条件: [是Galois k K] (f : Gal(K/k)) (x : K)
  证明: adjoin_simple_map_algHom (f : K ->ₐ[k] K) x

nonrec lemma mem_fixingSubgroup_iff (α : Gal(K/k)) (L : FiniteGaloisIntermediateField k K) :
    α in L.fixingSubgroup ↔ α.restrictNormalHom L = 1 := by
  simp [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff, AlgEquiv.ext_iff, Subtype.ext_iff,
 

Depends on / 依赖: adjoin_simple_map_algHom
-/
theorem adjoin_simple_map_algEquiv [IsGalois k K] (f : Gal(K/k)) (x : K) :
    adjoin k {f x} = adjoin k {x} :=
  adjoin_simple_map_algHom (f : K ->ₐ[k] K) x

nonrec lemma mem_fixingSubgroup_iff (α : Gal(K/k)) (L : FiniteGaloisIntermediateField k K) :
    α in L.fixingSubgroup ↔ α.restrictNormalHom L = 1 := by
  simp [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff, AlgEquiv.ext_iff, Subtype.ext_iff,
    AlgEquiv.restrictNormalHom_apply]

end FiniteGaloisIntermediateField
