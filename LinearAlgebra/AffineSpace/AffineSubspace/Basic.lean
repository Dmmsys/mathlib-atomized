/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Affine spaces

This file gives further properties of affine subspaces (over modules)
and the affine span of a set of points.

## Main definitions

* `AffineSubspace.Parallel`, notation `∥`, gives the property of two affine subspaces being
  parallel (one being a translate of the other).

-/

@[expose] public section

noncomputable section

open Affine

open Set
open scoped Pointwise

section

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

/--
lemma `vectorSpan_vadd` / 引理 `vectorSpan_vadd`

English:
lemma vectorSpan_vadd
  given: (s : Set P) (v : V)
  statement: vectorSpan k (v +ᵥ s) = vectorSpan k s
  proof: by
  simp [vectorSpan]

中文:
引理 vectorSpan_vadd
  条件: (s : Set P) (v : V)
  结论: vectorSpan k (v +ᵥ s) = vectorSpan k s
  证明: by
  simp [vectorSpan]
-/
@[simp] lemma vectorSpan_vadd (s : Set P) (v : V) : vectorSpan k (v +ᵥ s) = vectorSpan k s := by
  simp [vectorSpan]

end


namespace AffineSubspace

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {k P}


/--
theorem `vsub_right_mem_direction_iff_mem` / 定理 `vsub_right_mem_direction_iff_mem`

English:
theorem vsub_right_mem_direction_iff_mem
  given: {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P)
  proof: by
  rw [mem_direction_iff_eq_vsub_right hp]
  simp

中文:
定理 vsub_right_mem_direction_iff_mem
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P)
  证明: by
  rw [mem_direction_iff_eq_vsub_right hp]
  simp

Depends on / 依赖: mem_direction_iff_eq_vsub_right
-/
theorem vsub_right_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) :
    p₂ -ᵥ p in s.direction ↔ p₂ in s := by
  rw [mem_direction_iff_eq_vsub_right hp]
  simp

/--
theorem `vsub_left_mem_direction_iff_mem` / 定理 `vsub_left_mem_direction_iff_mem`

English:
theorem vsub_left_mem_direction_iff_mem
  given: {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P)
  proof: by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp

中文:
定理 vsub_left_mem_direction_iff_mem
  条件: {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P)
  证明: by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp

Depends on / 依赖: mem_direction_iff_eq_vsub_left
-/
theorem vsub_left_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) :
    p -ᵥ p₂ in s.direction ↔ p₂ in s := by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp

/--
Instance `toAddTorsor` / 实例 `toAddTorsor`

English:
instance toAddTorsor
  signature: (s : AffineSubspace k P) [Nonempty s]
  body: ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := fun a => by
    ext
    exact zero_vadd _ _
  add_vadd a b c := by
    ext
    apply add_vadd
  vsub a b := ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  vsub_vadd' a b := by
    ext
    apply AddTorsor.

中文:
实例 toAddTorsor
  签名: (s : AffineSubspace k P) [Nonempty s]
  定义体: ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := fun a => by
    ext
    exact zero_vadd _ _
  add_vadd a b c := by
    ext
    apply add_vadd
  vsub a b := ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  vsub_vadd' a b := by
    ext
    apply AddTorsor.

Depends on / 依赖: vadd_mem_of_mem_direction
-/
instance toAddTorsor (s : AffineSubspace k P) [Nonempty s] : AddTorsor s.direction s where
  vadd a b := ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := fun a => by
    ext
    exact zero_vadd _ _
  add_vadd a b c := by
    ext
    apply add_vadd
  vsub a b := ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  vsub_vadd' a b := by
    ext
    apply AddTorsor.vsub_vadd'
  vadd_vsub' a b := by
    ext
    apply AddTorsor.vadd_vsub'

@[simp, norm_cast]
/--
theorem `coe_vsub` / 定理 `coe_vsub`

English:
theorem coe_vsub
  given: (s : AffineSubspace k P) [Nonempty s] (a b : s)
  statement: ↑(a -ᵥ b) = (a : P) -ᵥ (b : P)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_vsub
  条件: (s : AffineSubspace k P) [Nonempty s] (a b : s)
  结论: ↑(a -ᵥ b) = (a : P) -ᵥ (b : P)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_vsub (s : AffineSubspace k P) [Nonempty s] (a b : s) : ↑(a -ᵥ b) = (a : P) -ᵥ (b : P) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_vadd` / 定理 `coe_vadd`

English:
theorem coe_vadd
  given: (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s)
  proof: rfl

中文:
定理 coe_vadd
  条件: (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s)
  证明: rfl
-/
theorem coe_vadd (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s) :
    ↑(a +ᵥ b) = (a : V) +ᵥ (b : P) :=
  rfl

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : AffineSubspace k P) [Nonempty s]
  body: (↑)
  linear := s.direction.subtype
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 subtype
  签名: (s : AffineSubspace k P) [Nonempty s]
  定义体: (↑)
  linear := s.direction.subtype
  map_vadd' _ _ := rfl

@[simp]
-/
protected def subtype (s : AffineSubspace k P) [Nonempty s] : s ->ᵃ[k] P where
  toFun := (↑)
  linear := s.direction.subtype
  map_vadd' _ _ := rfl

@[simp]
/--
theorem `subtype_linear` / 定理 `subtype_linear`

English:
theorem subtype_linear
  given: (s : AffineSubspace k P) [Nonempty s]
  proof: rfl

@[simp]

中文:
定理 subtype_linear
  条件: (s : AffineSubspace k P) [Nonempty s]
  证明: rfl

@[simp]
-/
theorem subtype_linear (s : AffineSubspace k P) [Nonempty s] :
    s.subtype.linear = s.direction.subtype := rfl

@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: {s : AffineSubspace k P} [Nonempty s] (p : s)
  statement: s.subtype p = p
  proof: rfl

中文:
定理 subtype_apply
  条件: {s : AffineSubspace k P} [Nonempty s] (p : s)
  结论: s.subtype p = p
  证明: rfl
-/
theorem subtype_apply {s : AffineSubspace k P} [Nonempty s] (p : s) : s.subtype p = p :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  given: (s : AffineSubspace k P) [Nonempty s]
  statement: Function.Injective s.subtype
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  条件: (s : AffineSubspace k P) [Nonempty s]
  结论: Function.Injective s.subtype
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective (s : AffineSubspace k P) [Nonempty s] : Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  given: (s : AffineSubspace k P) [Nonempty s]
  statement: (s.subtype : s -> P) = ((↑) : s -> P)
  proof: rfl

中文:
定理 coe_subtype
  条件: (s : AffineSubspace k P) [Nonempty s]
  结论: (s.subtype : s -> P) = ((↑) : s -> P)
  证明: rfl
-/
theorem coe_subtype (s : AffineSubspace k P) [Nonempty s] : (s.subtype : s -> P) = ((↑) : s -> P) :=
  rfl

end AffineSubspace

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineMap.lineMap_mem` / 定理 `AffineMap.lineMap_mem`

English:
theorem AffineMap.lineMap_mem
  statement: {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  proof: by
  rw [AffineMap.lineMap_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀

中文:
定理 AffineMap.lineMap_mem
  结论: {k V P : 类型} [Ring k] [AddCommGroup V] [Module k V]
  证明: by
  rw [AffineMap.lineMap_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, Q.smul_vsub_vadd_mem, lineMap_apply, smul_vsub_vadd_mem
-/
theorem AffineMap.lineMap_mem {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ in Q) (h₁ : p₁ in Q) :
    AffineMap.lineMap p₀ p₁ c in Q := by
  rw [AffineMap.lineMap_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀

/--
theorem `AffineMap.homothety_mem` / 定理 `AffineMap.homothety_mem`

English:
theorem AffineMap.homothety_mem
  statement: {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  proof: by
  rw [AffineMap.homothety_eq_lineMap]
  exact lineMap_mem r hc hp

中文:
定理 AffineMap.homothety_mem
  结论: {k V P : 类型} [CommRing k] [AddCommGroup V] [Module k V]
  证明: by
  rw [AffineMap.homothety_eq_lineMap]
  exact lineMap_mem r hc hp

Depends on / 依赖: AffineMap, AffineMap.homothety_eq_lineMap, homothety_eq_lineMap, lineMap_mem
-/
theorem AffineMap.homothety_mem {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {s : AffineSubspace k P} {c : P} (hc : c in s) (r : k) {p : P} (hp : p in s) :
    AffineMap.homothety c r p in s := by
  rw [AffineMap.homothety_eq_lineMap]
  exact lineMap_mem r hc hp

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P]

variable (k V) {p₁ p₂ : P}

/-- The affine span of a single point, coerced to a set, contains just that point. -/
@[simp]
/--
theorem `coe_affineSpan_singleton` / 定理 `coe_affineSpan_singleton`

English:
theorem coe_affineSpan_singleton
  given: (p : P)
  statement: (affineSpan k ({p} : Set P) : Set P) = {p}
  proof: by
  ext x
  rw [mem_coe]; rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_singleton p)) _]; rw [direction_affineSpan]
  simp

中文:
定理 coe_affineSpan_singleton
  条件: (p : P)
  结论: (affineSpan k ({p} : Set P) : Set P) = {p}
  证明: by
  ext x
  rw [mem_coe]; rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_singleton p)) _]; rw [direction_affineSpan]
  simp

Depends on / 依赖: Set.mem_singleton, direction_affineSpan, mem_affineSpan, mem_coe, mem_singleton, vsub_right_mem_direction_iff_mem
-/
theorem coe_affineSpan_singleton (p : P) : (affineSpan k ({p} : Set P) : Set P) = {p} := by
  ext x
  rw [mem_coe]; rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_singleton p)) _]; rw [direction_affineSpan]
  simp

/-- A point is in the affine span of a single point if and only if they are equal. -/
@[simp]
/--
theorem `mem_affineSpan_singleton` / 定理 `mem_affineSpan_singleton`

English:
theorem mem_affineSpan_singleton
  statement: p₁ in affineSpan k ({p₂} : Set P) ↔ p₁ = p₂
  proof: by
  simp [← mem_coe]

中文:
定理 mem_affineSpan_singleton
  结论: p₁ in affineSpan k ({p₂} : Set P) ↔ p₁ = p₂
  证明: by
  simp [← mem_coe]

Depends on / 依赖: mem_coe
-/
theorem mem_affineSpan_singleton : p₁ in affineSpan k ({p₂} : Set P) ↔ p₁ = p₂ := by
  simp [← mem_coe]

/--
Instance `unique_affineSpan_singleton` / 实例 `unique_affineSpan_singleton`

English:
instance unique_affineSpan_singleton
  signature: (p : P)
  body: ⟨p, mem_affineSpan _ (Set.mem_singleton _)⟩
  uniq := fun x => Subtype.ext ((mem_affineSpan_singleton _ _).1 x.property)

@[simp]

中文:
实例 unique_affineSpan_singleton
  签名: (p : P)
  定义体: ⟨p, mem_affineSpan _ (Set.mem_singleton _)⟩
  uniq := fun x => Subtype.ext ((mem_affineSpan_singleton _ _).1 x.property)

@[simp]

Depends on / 依赖: Set.mem_singleton, mem_affineSpan, mem_singleton
-/
instance unique_affineSpan_singleton (p : P) : Unique (affineSpan k {p}) where
  default := ⟨p, mem_affineSpan _ (Set.mem_singleton _)⟩
  uniq := fun x => Subtype.ext ((mem_affineSpan_singleton _ _).1 x.property)

@[simp]
/--
theorem `preimage_coe_affineSpan_singleton` / 定理 `preimage_coe_affineSpan_singleton`

English:
theorem preimage_coe_affineSpan_singleton
  given: (x : P)
  proof: eq_univ_of_forall fun y => (AffineSubspace.mem_affineSpan_singleton _ _).1 y.2

中文:
定理 preimage_coe_affineSpan_singleton
  条件: (x : P)
  证明: eq_univ_of_forall fun y => (AffineSubspace.mem_affineSpan_singleton _ _).1 y.2

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_affineSpan_singleton, eq_univ_of_forall, mem_affineSpan_singleton
-/
theorem preimage_coe_affineSpan_singleton (x : P) :
    ((↑) : affineSpan k ({x} : Set P) -> P) ⁻¹' {x} = univ :=
  eq_univ_of_forall fun y => (AffineSubspace.mem_affineSpan_singleton _ _).1 y.2

variable (P)

/-- The top affine subspace is linearly equivalent to the affine space.
This is the affine version of `Submodule.topEquiv`. -/
@[simps! linear apply symm_apply_coe]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where
  body: Equiv.Set.univ P
  linear := .ofEq _ _ (direction_top _ _ _) ≪≫ₗ Submodule.topEquiv
  map_vadd' _ _ := rfl

中文:
定义 topEquiv
  签名: : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where
  定义体: Equiv.Set.univ P
  linear := .ofEq _ _ (direction_top _ _ _) ≪≫ₗ Submodule.topEquiv
  map_vadd' _ _ := rfl

Depends on / 依赖: Equiv.Set.univ
-/
def topEquiv : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where
  toEquiv := Equiv.Set.univ P
  linear := .ofEq _ _ (direction_top _ _ _) ≪≫ₗ Submodule.topEquiv
  map_vadd' _ _ := rfl

variable {k V P}

/--
theorem `subsingleton_of_subsingleton_span_eq_top` / 定理 `subsingleton_of_subsingleton_span_eq_top`

English:
theorem subsingleton_of_subsingleton_span_eq_top
  statement: {s : Set P} (h₁ : s.Subsingleton)
  proof: by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this]; rw [AffineSubspace.ext_iff]; rw [AffineSubspace.coe_affineSpan_singleton]; rw [AffineSubspace.top_coe]; rw [eq_comm]; rw [← subsingleton

中文:
定理 subsingleton_of_subsingleton_span_eq_top
  结论: {s : Set P} (h₁ : s.Subsingleton)
  证明: by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this]; rw [AffineSubspace.ext_iff]; rw [AffineSubspace.coe_affineSpan_singleton]; rw [AffineSubspace.top_coe]; rw [eq_comm]; rw [← subsingleton

Depends on / 依赖: AffineSubspace, AffineSubspace.coe_affineSpan_singleton, AffineSubspace.ext_iff, AffineSubspace.nonempty_of_affineSpan_eq_top, AffineSubspace.top_coe, Subset, Subset.antisymm, antisymm, coe_affineSpan_singleton, eq_comm, ext_iff, mem_univ, nonempty_of_affineSpan_eq_top, subsingleton_iff_singleton, subsingleton_of_univ_subsingleton, top_coe
-/
theorem subsingleton_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : Subsingleton P := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this]; rw [AffineSubspace.ext_iff]; rw [AffineSubspace.coe_affineSpan_singleton]; rw [AffineSubspace.top_coe]; rw [eq_comm]; rw [← subsingleton_iff_singleton (mem_univ _)] at h₂
  exact subsingleton_of_univ_subsingleton h₂

/--
theorem `eq_univ_of_subsingleton_span_eq_top` / 定理 `eq_univ_of_subsingleton_span_eq_top`

English:
theorem eq_univ_of_subsingleton_span_eq_top
  statement: {s : Set P} (h₁ : s.Subsingleton)
  proof: by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this]; rw [eq_comm]; rw [← subsingleton_iff_singleton (mem_univ p)]; rw [subsingleton_univ_iff]
  exact subsingleton_of_subsingleton_span_eq_to

中文:
定理 eq_univ_of_subsingleton_span_eq_top
  结论: {s : Set P} (h₁ : s.Subsingleton)
  证明: by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this]; rw [eq_comm]; rw [← subsingleton_iff_singleton (mem_univ p)]; rw [subsingleton_univ_iff]
  exact subsingleton_of_subsingleton_span_eq_to

Depends on / 依赖: AffineSubspace, AffineSubspace.nonempty_of_affineSpan_eq_top, Subset, Subset.antisymm, antisymm, eq_comm, mem_univ, nonempty_of_affineSpan_eq_top, subsingleton_iff_singleton, subsingleton_of_subsingleton_span_eq_top, subsingleton_univ_iff
-/
theorem eq_univ_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : s = (univ : Set P) := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this]; rw [eq_comm]; rw [← subsingleton_iff_singleton (mem_univ p)]; rw [subsingleton_univ_iff]
  exact subsingleton_of_subsingleton_span_eq_top h₁ h₂

/--
theorem `direction_lt_of_nonempty` / 定理 `direction_lt_of_nonempty`

English:
theorem direction_lt_of_nonempty
  statement: {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
  proof: by
  obtain ⟨p, hp⟩ := hn
  rw [lt_iff_le_and_exists] at h
  rcases h with ⟨hle, p₂, hp₂, hp₂s₁⟩
  rw [SetLike.lt_iff_le_and_exists]
  use direction_le hle, p₂ -ᵥ p, vsub_mem_direction hp₂ (hle hp)
  intro hm
  rw [vsub_right_mem_direction_iff_mem hp p₂] at hm
  exact hp₂s₁ hm

中文:
定理 direction_lt_of_nonempty
  结论: {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
  证明: by
  obtain ⟨p, hp⟩ := hn
  rw [lt_iff_le_and_exists] at h
  rcases h with ⟨hle, p₂, hp₂, hp₂s₁⟩
  rw [SetLike.lt_iff_le_and_exists]
  use direction_le hle, p₂ -ᵥ p, vsub_mem_direction hp₂ (hle hp)
  intro hm
  rw [vsub_right_mem_direction_iff_mem hp p₂] at hm
  exact hp₂s₁ hm

Depends on / 依赖: SetLike, SetLike.lt_iff_le_and_exists, direction_le, lt_iff_le_and_exists, vsub_mem_direction, vsub_right_mem_direction_iff_mem
-/
theorem direction_lt_of_nonempty {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
    (hn : (s₁ : Set P).Nonempty) : s₁.direction < s₂.direction := by
  obtain ⟨p, hp⟩ := hn
  rw [lt_iff_le_and_exists] at h
  rcases h with ⟨hle, p₂, hp₂, hp₂s₁⟩
  rw [SetLike.lt_iff_le_and_exists]
  use direction_le hle, p₂ -ᵥ p, vsub_mem_direction hp₂ (hle hp)
  intro hm
  rw [vsub_right_mem_direction_iff_mem hp p₂] at hm
  exact hp₂s₁ hm

end AffineSubspace

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {ι : Type*}

open AffineSubspace Set

/--
theorem `vectorSpan_eq_span_vsub_set_left` / 定理 `vectorSpan_eq_span_vsub_set_left`

English:
theorem vectorSpan_eq_span_vsub_set_left
  given: {s : Set P} {p : P} (hp : p in s)
  proof: by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_left p₁ p₂ p] at hv
    rw [← hv]; rw [SetLike.mem_coe]; rw [Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm 

中文:
定理 vectorSpan_eq_span_vsub_set_left
  条件: {s : Set P} {p : P} (hp : p in s)
  证明: by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_left p₁ p₂ p] at hv
    rw [← hv]; rw [SetLike.mem_coe]; rw [Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm 

Depends on / 依赖: SetLike, SetLike.mem_coe, Submodule, Submodule.mem_span, Submodule.span_le, Submodule.span_mono, Submodule.sub_mem, le_antisymm, mem_coe, mem_span, simp_rw, span_le, span_mono, sub_mem, vectorSpan_def, vsub_sub_vsub_cancel_left
-/
theorem vectorSpan_eq_span_vsub_set_left {s : Set P} {p : P} (hp : p in s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_left p₁ p₂ p] at hv
    rw [← hv]; rw [SetLike.mem_coe]; rw [Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₂, hp₂, rfl⟩) (hm ⟨p₁, hp₁, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p, hp, p₂, hp₂, hv⟩

/--
theorem `vectorSpan_eq_span_vsub_set_right` / 定理 `vectorSpan_eq_span_vsub_set_right`

English:
theorem vectorSpan_eq_span_vsub_set_right
  given: {s : Set P} {p : P} (hp : p in s)
  proof: by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_right p₁ p₂ p] at hv
    rw [← hv]; rw [SetLike.mem_coe]; rw [Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm

中文:
定理 vectorSpan_eq_span_vsub_set_right
  条件: {s : Set P} {p : P} (hp : p in s)
  证明: by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_right p₁ p₂ p] at hv
    rw [← hv]; rw [SetLike.mem_coe]; rw [Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm

Depends on / 依赖: SetLike, SetLike.mem_coe, Submodule, Submodule.mem_span, Submodule.span_le, Submodule.span_mono, Submodule.sub_mem, le_antisymm, mem_coe, mem_span, simp_rw, span_le, span_mono, sub_mem, vectorSpan_def, vsub_sub_vsub_cancel_right
-/
theorem vectorSpan_eq_span_vsub_set_right {s : Set P} {p : P} (hp : p in s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_right p₁ p₂ p] at hv
    rw [← hv]; rw [SetLike.mem_coe]; rw [Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₁, hp₁, rfl⟩) (hm ⟨p₂, hp₂, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p₂, hp₂, p, hp, hv⟩

/--
theorem `vectorSpan_eq_span_vsub_set_left_ne` / 定理 `vectorSpan_eq_span_vsub_set_left_ne`

English:
theorem vectorSpan_eq_span_vsub_set_left_ne
  given: {s : Set P} {p : P} (hp : p in s)
  proof: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k hp]; rw [← Set.insert_eq_of_mem hp]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

中文:
定理 vectorSpan_eq_span_vsub_set_left_ne
  条件: {s : Set P} {p : P} (hp : p in s)
  证明: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k hp]; rw [← Set.insert_eq_of_mem hp]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

Depends on / 依赖: Set.image_insert_eq, Set.insert_eq_of_mem, Set.insert_sdiff_singleton, Submodule, Submodule.span_insert_eq_span, conv_lhs, image_insert_eq, insert_eq_of_mem, insert_sdiff_singleton, span_insert_eq_span, vectorSpan_eq_span_vsub_set_left
-/
theorem vectorSpan_eq_span_vsub_set_left_ne {s : Set P} {p : P} (hp : p in s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' (s \ {p})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k hp]; rw [← Set.insert_eq_of_mem hp]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/--
theorem `vectorSpan_eq_span_vsub_set_right_ne` / 定理 `vectorSpan_eq_span_vsub_set_right_ne`

English:
theorem vectorSpan_eq_span_vsub_set_right_ne
  given: {s : Set P} {p : P} (hp : p in s)
  proof: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k hp]; rw [← Set.insert_eq_of_mem hp]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

中文:
定理 vectorSpan_eq_span_vsub_set_right_ne
  条件: {s : Set P} {p : P} (hp : p in s)
  证明: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k hp]; rw [← Set.insert_eq_of_mem hp]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

Depends on / 依赖: Set.image_insert_eq, Set.insert_eq_of_mem, Set.insert_sdiff_singleton, Submodule, Submodule.span_insert_eq_span, conv_lhs, image_insert_eq, insert_eq_of_mem, insert_sdiff_singleton, span_insert_eq_span, vectorSpan_eq_span_vsub_set_right
-/
theorem vectorSpan_eq_span_vsub_set_right_ne {s : Set P} {p : P} (hp : p in s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' (s \ {p})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k hp]; rw [← Set.insert_eq_of_mem hp]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/--
theorem `vectorSpan_eq_span_vsub_finset_right_ne` / 定理 `vectorSpan_eq_span_vsub_finset_right_ne`

English:
theorem vectorSpan_eq_span_vsub_finset_right_ne
  statement: [DecidableEq P] [DecidableEq V] {s : Finset P}
  proof: by
  simp [vectorSpan_eq_span_vsub_set_right_ne _ (Finset.mem_coe.mpr hp)]

中文:
定理 vectorSpan_eq_span_vsub_finset_right_ne
  结论: [DecidableEq P] [DecidableEq V] {s : Finset P}
  证明: by
  simp [vectorSpan_eq_span_vsub_set_right_ne _ (Finset.mem_coe.mpr hp)]

Depends on / 依赖: Finset, Finset.mem_coe.mpr, mem_coe, vectorSpan_eq_span_vsub_set_right_ne
-/
theorem vectorSpan_eq_span_vsub_finset_right_ne [DecidableEq P] [DecidableEq V] {s : Finset P}
    {p : P} (hp : p in s) :
    vectorSpan k (s : Set P) = Submodule.span k ((s.erase p).image (· -ᵥ p)) := by
  simp [vectorSpan_eq_span_vsub_set_right_ne _ (Finset.mem_coe.mpr hp)]

/--
theorem `vectorSpan_image_eq_span_vsub_set_left_ne` / 定理 `vectorSpan_image_eq_span_vsub_set_left_ne`

English:
theorem vectorSpan_image_eq_span_vsub_set_left_ne
  given: (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s)
  proof: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_image_of_mem p hi)]; rw [← Set.insert_eq_of_mem hi]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

中文:
定理 vectorSpan_image_eq_span_vsub_set_left_ne
  条件: (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s)
  证明: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_image_of_mem p hi)]; rw [← Set.insert_eq_of_mem hi]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

Depends on / 依赖: Set.image_insert_eq, Set.insert_eq_of_mem, Set.insert_sdiff_singleton, Set.mem_image_of_mem, Submodule, Submodule.span_insert_eq_span, conv_lhs, image_insert_eq, insert_eq_of_mem, insert_sdiff_singleton, mem_image_of_mem, span_insert_eq_span, vectorSpan_eq_span_vsub_set_left
-/
theorem vectorSpan_image_eq_span_vsub_set_left_ne (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s) :
    vectorSpan k (p '' s) = Submodule.span k ((p i -ᵥ ·) '' p '' (s \ {i})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_image_of_mem p hi)]; rw [← Set.insert_eq_of_mem hi]; rw [←
      Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/--
theorem `vectorSpan_image_eq_span_vsub_set_right_ne` / 定理 `vectorSpan_image_eq_span_vsub_set_right_ne`

English:
theorem vectorSpan_image_eq_span_vsub_set_right_ne
  given: (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s)
  proof: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi)]; rw [← Set.insert_eq_of_mem hi]; rw [← Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

中文:
定理 vectorSpan_image_eq_span_vsub_set_right_ne
  条件: (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s)
  证明: by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi)]; rw [← Set.insert_eq_of_mem hi]; rw [← Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

Depends on / 依赖: Set.image_insert_eq, Set.insert_eq_of_mem, Set.insert_sdiff_singleton, Set.mem_image_of_mem, Submodule, Submodule.span_insert_eq_span, conv_lhs, image_insert_eq, insert_eq_of_mem, insert_sdiff_singleton, mem_image_of_mem, span_insert_eq_span, vectorSpan_eq_span_vsub_set_right
-/
theorem vectorSpan_image_eq_span_vsub_set_right_ne (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s) :
    vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ p i) '' p '' (s \ {i})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi)]; rw [← Set.insert_eq_of_mem hi]; rw [← Set.insert_sdiff_singleton]; rw [Set.image_insert_eq]; rw [Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/--
theorem `vectorSpan_range_eq_span_range_vsub_left` / 定理 `vectorSpan_range_eq_span_range_vsub_left`

English:
theorem vectorSpan_range_eq_span_range_vsub_left
  given: (p : ι -> P) (i0 : ι)
  proof: by
  rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_range_self i0)]; rw [← Set.range_comp]
  congr

中文:
定理 vectorSpan_range_eq_span_range_vsub_left
  条件: (p : ι -> P) (i0 : ι)
  证明: by
  rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_range_self i0)]; rw [← Set.range_comp]
  congr

Depends on / 依赖: Set.mem_range_self, Set.range_comp, mem_range_self, range_comp, vectorSpan_eq_span_vsub_set_left
-/
theorem vectorSpan_range_eq_span_range_vsub_left (p : ι -> P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i0 -ᵥ p i) := by
  rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_range_self i0)]; rw [← Set.range_comp]
  congr

/--
theorem `vectorSpan_range_eq_span_range_vsub_right` / 定理 `vectorSpan_range_eq_span_range_vsub_right`

English:
theorem vectorSpan_range_eq_span_range_vsub_right
  given: (p : ι -> P) (i0 : ι)
  proof: by
  rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_range_self i0)]; rw [← Set.range_comp]
  congr

中文:
定理 vectorSpan_range_eq_span_range_vsub_right
  条件: (p : ι -> P) (i0 : ι)
  证明: by
  rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_range_self i0)]; rw [← Set.range_comp]
  congr

Depends on / 依赖: Set.mem_range_self, Set.range_comp, mem_range_self, range_comp, vectorSpan_eq_span_vsub_set_right
-/
theorem vectorSpan_range_eq_span_range_vsub_right (p : ι -> P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i -ᵥ p i0) := by
  rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_range_self i0)]; rw [← Set.range_comp]
  congr

/--
theorem `vectorSpan_range_eq_span_range_vsub_left_ne` / 定理 `vectorSpan_range_eq_span_range_vsub_left_ne`

English:
theorem vectorSpan_range_eq_span_range_vsub_left_ne
  given: (p : ι -> P) (i₀ : ι)
  proof: by
  rw [← Set.image_univ]; rw [vectorSpan_image_eq_span_vsub_set_left_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact f

中文:
定理 vectorSpan_range_eq_span_range_vsub_left_ne
  条件: (p : ι -> P) (i₀ : ι)
  证明: by
  rw [← Set.image_univ]; rw [vectorSpan_image_eq_span_vsub_set_left_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact f

Depends on / 依赖: Set.image_univ, Set.mem_image, Set.mem_range, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_univ, Subtype, Subtype.exists, image_univ, mem_image, mem_range, mem_sdiff, mem_singleton_iff, mem_univ, vectorSpan_image_eq_span_vsub_set_left_ne
-/
theorem vectorSpan_range_eq_span_range_vsub_left_ne (p : ι -> P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x != i₀ } => p i₀ -ᵥ p i) := by
  rw [← Set.image_univ]; rw [vectorSpan_image_eq_span_vsub_set_left_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

/--
theorem `vectorSpan_range_eq_span_range_vsub_right_ne` / 定理 `vectorSpan_range_eq_span_range_vsub_right_ne`

English:
theorem vectorSpan_range_eq_span_range_vsub_right_ne
  given: (p : ι -> P) (i₀ : ι)
  proof: by
  rw [← Set.image_univ]; rw [vectorSpan_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact 

中文:
定理 vectorSpan_range_eq_span_range_vsub_right_ne
  条件: (p : ι -> P) (i₀ : ι)
  证明: by
  rw [← Set.image_univ]; rw [vectorSpan_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact 

Depends on / 依赖: Set.image_univ, Set.mem_image, Set.mem_range, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_univ, Subtype, Subtype.exists, image_univ, mem_image, mem_range, mem_sdiff, mem_singleton_iff, mem_univ, vectorSpan_image_eq_span_vsub_set_right_ne
-/
theorem vectorSpan_range_eq_span_range_vsub_right_ne (p : ι -> P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x != i₀ } => p i -ᵥ p i₀) := by
  rw [← Set.image_univ]; rw [vectorSpan_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

variable {k}

/-- A set, considered as a subset of its spanned affine subspace, spans the whole subspace. -/
@[simp]
/--
theorem `affineSpan_coe_preimage_eq_top` / 定理 `affineSpan_coe_preimage_eq_top`

English:
theorem affineSpan_coe_preimage_eq_top
  given: (A : Set P) [Nonempty A]
  proof: by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  refine affineSpan_induction' (fun y hy => ?_) (fun c u hu v hv w hw => ?_) hx
  · exact subset_affineSpan _ _ hy
  · exact AffineSubspace.smul_vsub_vadd_mem _ _

中文:
定理 affineSpan_coe_preimage_eq_top
  条件: (A : Set P) [Nonempty A]
  证明: by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  refine affineSpan_induction' (fun y hy => ?_) (fun c u hu v hv w hw => ?_) hx
  · exact subset_affineSpan _ _ hy
  · exact AffineSubspace.smul_vsub_vadd_mem _ _

Depends on / 依赖: AffineSubspace, AffineSubspace.smul_vsub_vadd_mem, affineSpan_induction, eq_top_iff, smul_vsub_vadd_mem, subset_affineSpan
-/
theorem affineSpan_coe_preimage_eq_top (A : Set P) [Nonempty A] :
    affineSpan k (((↑) : affineSpan k A -> P) ⁻¹' A) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  refine affineSpan_induction' (fun y hy => ?_) (fun c u hu v hv w hw => ?_) hx
  · exact subset_affineSpan _ _ hy
  · exact AffineSubspace.smul_vsub_vadd_mem _ _

/--
theorem `affineSpan_singleton_union_vadd_eq_top_of_span_eq_top` / 定理 `affineSpan_singleton_union_vadd_eq_top_of_span_eq_top`

English:
theorem affineSpan_singleton_union_vadd_eq_top_of_span_eq_top
  statement: {s : Set V} (p : P)
  proof: by
  convert!
    ext_of_direction_eq _
      ⟨p, mem_affineSpan k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affineSpan]; rw [direction_top]; rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p in _)]; rw [eq_top_iff]; rw [← h]
 

中文:
定理 affineSpan_singleton_union_vadd_eq_top_of_span_eq_top
  结论: {s : Set V} (p : P)
  证明: by
  convert!
    ext_of_direction_eq _
      ⟨p, mem_affineSpan k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affineSpan]; rw [direction_top]; rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p in _)]; rw [eq_top_iff]; rw [← h]
 

Depends on / 依赖: Set.mem_singleton, Set.mem_union_left, Submodule, Submodule.span_mono, convert, direction_affineSpan, direction_top, eq_top_iff, ext_of_direction_eq, mem_affineSpan, mem_singleton, mem_top, mem_union_left, span_mono, vectorSpan_eq_span_vsub_set_right
-/
theorem affineSpan_singleton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P)
    (h : Submodule.span k (Set.range ((↑) : s -> V)) = ⊤) :
    affineSpan k ({p} union (fun v => v +ᵥ p) '' s) = ⊤ := by
  convert!
    ext_of_direction_eq _
      ⟨p, mem_affineSpan k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affineSpan]; rw [direction_top]; rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p in _)]; rw [eq_top_iff]; rw [← h]
  apply Submodule.span_mono
  rintro v ⟨v', rfl⟩
  use (v' : V) +ᵥ p
  simp

variable (k)

/--
theorem `vectorSpan_pair` / 定理 `vectorSpan_pair`

English:
theorem vectorSpan_pair
  given: (p₁ p₂ : P)
  statement: vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₁ -ᵥ p₂)
  proof: by
  simp_rw [vectorSpan_eq_span_vsub_set_left k (mem_insert p₁ _), image_pair, vsub_self,
    Submodule.span_insert_zero]

中文:
定理 vectorSpan_pair
  条件: (p₁ p₂ : P)
  结论: vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₁ -ᵥ p₂)
  证明: by
  simp_rw [vectorSpan_eq_span_vsub_set_left k (mem_insert p₁ _), image_pair, vsub_self,
    Submodule.span_insert_zero]

Depends on / 依赖: Submodule, Submodule.span_insert_zero, image_pair, mem_insert, simp_rw, span_insert_zero, vectorSpan_eq_span_vsub_set_left, vsub_self
-/
theorem vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₁ -ᵥ p₂) := by
  simp_rw [vectorSpan_eq_span_vsub_set_left k (mem_insert p₁ _), image_pair, vsub_self,
    Submodule.span_insert_zero]

/--
theorem `vectorSpan_pair_rev` / 定理 `vectorSpan_pair_rev`

English:
theorem vectorSpan_pair_rev
  given: (p₁ p₂ : P)
  statement: vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
  proof: by
  rw [pair_comm]; rw [vectorSpan_pair]

中文:
定理 vectorSpan_pair_rev
  条件: (p₁ p₂ : P)
  结论: vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
  证明: by
  rw [pair_comm]; rw [vectorSpan_pair]

Depends on / 依赖: pair_comm, vectorSpan_pair
-/
theorem vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁) := by
  rw [pair_comm]; rw [vectorSpan_pair]

variable {k}

/--
theorem `mem_vectorSpan_pair` / 定理 `mem_vectorSpan_pair`

English:
theorem mem_vectorSpan_pair
  given: {p₁ p₂ : P} {v : V}
  proof: by
  rw [vectorSpan_pair]; rw [Submodule.mem_span_singleton]

中文:
定理 mem_vectorSpan_pair
  条件: {p₁ p₂ : P} {v : V}
  证明: by
  rw [vectorSpan_pair]; rw [Submodule.mem_span_singleton]

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, mem_span_singleton, vectorSpan_pair
-/
theorem mem_vectorSpan_pair {p₁ p₂ : P} {v : V} :
    v in vectorSpan k ({p₁, p₂} : Set P) ↔ exists r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vectorSpan_pair]; rw [Submodule.mem_span_singleton]

/--
theorem `mem_vectorSpan_pair_rev` / 定理 `mem_vectorSpan_pair_rev`

English:
theorem mem_vectorSpan_pair_rev
  given: {p₁ p₂ : P} {v : V}
  proof: by
  rw [vectorSpan_pair_rev]; rw [Submodule.mem_span_singleton]

中文:
定理 mem_vectorSpan_pair_rev
  条件: {p₁ p₂ : P} {v : V}
  证明: by
  rw [vectorSpan_pair_rev]; rw [Submodule.mem_span_singleton]

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, mem_span_singleton, vectorSpan_pair_rev
-/
theorem mem_vectorSpan_pair_rev {p₁ p₂ : P} {v : V} :
    v in vectorSpan k ({p₁, p₂} : Set P) ↔ exists r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vectorSpan_pair_rev]; rw [Submodule.mem_span_singleton]


set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineMap.lineMap_mem_affineSpan_pair` / 定理 `AffineMap.lineMap_mem_affineSpan_pair`

English:
theorem AffineMap.lineMap_mem_affineSpan_pair
  given: (r : k) (p₁ p₂ : P)
  proof: AffineMap.lineMap_mem _ (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

中文:
定理 AffineMap.lineMap_mem_affineSpan_pair
  条件: (r : k) (p₁ p₂ : P)
  证明: AffineMap.lineMap_mem _ (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

Depends on / 依赖: AffineMap, AffineMap.lineMap_mem, left_mem_affineSpan_pair, lineMap_mem, right_mem_affineSpan_pair
-/
theorem AffineMap.lineMap_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₁ p₂ r in line[k, p₁, p₂] :=
  AffineMap.lineMap_mem _ (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineMap.lineMap_rev_mem_affineSpan_pair` / 定理 `AffineMap.lineMap_rev_mem_affineSpan_pair`

English:
theorem AffineMap.lineMap_rev_mem_affineSpan_pair
  given: (r : k) (p₁ p₂ : P)
  proof: AffineMap.lineMap_mem _ (right_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _)

中文:
定理 AffineMap.lineMap_rev_mem_affineSpan_pair
  条件: (r : k) (p₁ p₂ : P)
  证明: AffineMap.lineMap_mem _ (right_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _)

Depends on / 依赖: AffineMap, AffineMap.lineMap_mem, left_mem_affineSpan_pair, lineMap_mem, right_mem_affineSpan_pair
-/
theorem AffineMap.lineMap_rev_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₂ p₁ r in line[k, p₁, p₂] :=
  AffineMap.lineMap_mem _ (right_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _)

/--
theorem `smul_vsub_vadd_mem_affineSpan_pair` / 定理 `smul_vsub_vadd_mem_affineSpan_pair`

English:
theorem smul_vsub_vadd_mem_affineSpan_pair
  given: (r : k) (p₁ p₂ : P)
  proof: AffineMap.lineMap_mem_affineSpan_pair _ _ _

中文:
定理 smul_vsub_vadd_mem_affineSpan_pair
  条件: (r : k) (p₁ p₂ : P)
  证明: AffineMap.lineMap_mem_affineSpan_pair _ _ _

Depends on / 依赖: AffineMap, AffineMap.lineMap_mem_affineSpan_pair, lineMap_mem_affineSpan_pair
-/
theorem smul_vsub_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) +ᵥ p₁ in line[k, p₁, p₂] :=
  AffineMap.lineMap_mem_affineSpan_pair _ _ _

/--
theorem `smul_vsub_rev_vadd_mem_affineSpan_pair` / 定理 `smul_vsub_rev_vadd_mem_affineSpan_pair`

English:
theorem smul_vsub_rev_vadd_mem_affineSpan_pair
  given: (r : k) (p₁ p₂ : P)
  proof: AffineMap.lineMap_rev_mem_affineSpan_pair _ _ _

中文:
定理 smul_vsub_rev_vadd_mem_affineSpan_pair
  条件: (r : k) (p₁ p₂ : P)
  证明: AffineMap.lineMap_rev_mem_affineSpan_pair _ _ _

Depends on / 依赖: AffineMap, AffineMap.lineMap_rev_mem_affineSpan_pair, lineMap_rev_mem_affineSpan_pair
-/
theorem smul_vsub_rev_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₁ -ᵥ p₂) +ᵥ p₂ in line[k, p₁, p₂] :=
  AffineMap.lineMap_rev_mem_affineSpan_pair _ _ _

/--
theorem `vadd_left_mem_affineSpan_pair` / 定理 `vadd_left_mem_affineSpan_pair`

English:
theorem vadd_left_mem_affineSpan_pair
  given: {p₁ p₂ : P} {v : V}
  proof: by
  rw [vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [mem_vectorSpan_pair_rev]

中文:
定理 vadd_left_mem_affineSpan_pair
  条件: {p₁ p₂ : P} {v : V}
  证明: by
  rw [vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [mem_vectorSpan_pair_rev]

Depends on / 依赖: Decidable, direction_affineSpan, left_mem_affineSpan_pair, mem_vectorSpan_pair_rev, vadd_mem_iff_mem_direction
-/
theorem vadd_left_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₁ in line[k, p₁, p₂] ↔ exists r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [mem_vectorSpan_pair_rev]

/--
theorem `vadd_right_mem_affineSpan_pair` / 定理 `vadd_right_mem_affineSpan_pair`

English:
theorem vadd_right_mem_affineSpan_pair
  given: {p₁ p₂ : P} {v : V}
  proof: by
  rw [vadd_mem_iff_mem_direction _ (right_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [mem_vectorSpan_pair]

中文:
定理 vadd_right_mem_affineSpan_pair
  条件: {p₁ p₂ : P} {v : V}
  证明: by
  rw [vadd_mem_iff_mem_direction _ (right_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [mem_vectorSpan_pair]

Depends on / 依赖: Decidable, direction_affineSpan, mem_vectorSpan_pair, right_mem_affineSpan_pair, vadd_mem_iff_mem_direction
-/
theorem vadd_right_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₂ in line[k, p₁, p₂] ↔ exists r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vadd_mem_iff_mem_direction _ (right_mem_affineSpan_pair _ _ _)]; rw [direction_affineSpan]; rw [mem_vectorSpan_pair]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_affineSpan_pair_iff_exists_lineMap_eq` / 引理 `mem_affineSpan_pair_iff_exists_lineMap_eq`

English:
lemma mem_affineSpan_pair_iff_exists_lineMap_eq
  given: {p p₁ p₂ : P}
  proof: by
  constructor
  · intro h
    rw [← vsub_vadd p p₁]; rw [vadd_left_mem_affineSpan_pair] at h
    obtain ⟨r, hr⟩ := h
    refine ⟨r, ?_⟩
    rw [← vsub_vadd p p₁]; rw [← hr]; rw [AffineMap.lineMap_apply]
  · rintro ⟨r, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

中文:
引理 mem_affineSpan_pair_iff_exists_lineMap_eq
  条件: {p p₁ p₂ : P}
  证明: by
  constructor
  · intro h
    rw [← vsub_vadd p p₁]; rw [vadd_left_mem_affineSpan_pair] at h
    obtain ⟨r, hr⟩ := h
    refine ⟨r, ?_⟩
    rw [← vsub_vadd p p₁]; rw [← hr]; rw [AffineMap.lineMap_apply]
  · rintro ⟨r, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, AffineMap.lineMap_mem_affineSpan_pair, lineMap_apply, lineMap_mem_affineSpan_pair, vadd_left_mem_affineSpan_pair, vsub_vadd
-/
lemma mem_affineSpan_pair_iff_exists_lineMap_eq {p p₁ p₂ : P} :
    p in line[k, p₁, p₂] ↔ exists r : k, AffineMap.lineMap p₁ p₂ r = p := by
  constructor
  · intro h
    rw [← vsub_vadd p p₁]; rw [vadd_left_mem_affineSpan_pair] at h
    obtain ⟨r, hr⟩ := h
    refine ⟨r, ?_⟩
    rw [← vsub_vadd p p₁]; rw [← hr]; rw [AffineMap.lineMap_apply]
  · rintro ⟨r, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_affineSpan_pair_iff_exists_lineMap_rev_eq` / 引理 `mem_affineSpan_pair_iff_exists_lineMap_rev_eq`

English:
lemma mem_affineSpan_pair_iff_exists_lineMap_rev_eq
  given: {p p₁ p₂ : P}
  proof: by
  rw [Set.pair_comm]; rw [mem_affineSpan_pair_iff_exists_lineMap_eq]

中文:
引理 mem_affineSpan_pair_iff_exists_lineMap_rev_eq
  条件: {p p₁ p₂ : P}
  证明: by
  rw [Set.pair_comm]; rw [mem_affineSpan_pair_iff_exists_lineMap_eq]

Depends on / 依赖: Set.pair_comm, mem_affineSpan_pair_iff_exists_lineMap_eq, pair_comm
-/
lemma mem_affineSpan_pair_iff_exists_lineMap_rev_eq {p p₁ p₂ : P} :
    p in line[k, p₁, p₂] ↔ exists r : k, AffineMap.lineMap p₂ p₁ r = p := by
  rw [Set.pair_comm]; rw [mem_affineSpan_pair_iff_exists_lineMap_eq]

end AffineSpace'

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/--
theorem `direction_sup` / 定理 `direction_sup`

English:
theorem direction_sup
  given: {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s₁) (hp₂ : p₂ in s₂)
  proof: by
  refine le_antisymm ?_ ?_
  · change (affineSpan k ((s₁ : Set P) union s₂)).direction <= _
    rw [← mem_coe] at hp₁
    rw [direction_affineSpan]; rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ hp₁)]; rw [Submodule.span_le]
    rintro v ⟨p₃, hp₃, rfl⟩
    rcases hp₃ with hp₃ | hp

中文:
定理 direction_sup
  条件: {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s₁) (hp₂ : p₂ in s₂)
  证明: by
  refine le_antisymm ?_ ?_
  · change (affineSpan k ((s₁ : Set P) union s₂)).direction <= _
    rw [← mem_coe] at hp₁
    rw [direction_affineSpan]; rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ hp₁)]; rw [Submodule.span_le]
    rintro v ⟨p₃, hp₃, rfl⟩
    rcases hp₃ with hp₃ | hp

Depends on / 依赖: Set.mem_union_left, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_sup, Submodule.span_le, Submodule.zero_, Submodule.zero_mem, affineSpan, direction, direction_affineSpan, le_antisymm, mem_coe, mem_sup, mem_union_left, span_le, sup_assoc, sup_comm, vectorSpan_eq_span_vsub_set_right, vsub_mem_direction
-/
theorem direction_sup {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s₁) (hp₂ : p₂ in s₂) :
    (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction ⊔ k ∙ (p₂ -ᵥ p₁) := by
  refine le_antisymm ?_ ?_
  · change (affineSpan k ((s₁ : Set P) union s₂)).direction <= _
    rw [← mem_coe] at hp₁
    rw [direction_affineSpan]; rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ hp₁)]; rw [Submodule.span_le]
    rintro v ⟨p₃, hp₃, rfl⟩
    rcases hp₃ with hp₃ | hp₃
    · rw [sup_assoc, sup_comm, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁, vsub_mem_direction hp₃ hp₁
      rw [zero_add]
    · rw [sup_assoc, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁
      rw [and_comm]; rw [zero_add]
      use rfl
      rw [← vsub_add_vsub_cancel p₃ p₂ p₁]; rw [Submodule.mem_sup]
      use p₃ -ᵥ p₂, vsub_mem_direction hp₃ hp₂, p₂ -ᵥ p₁, Submodule.mem_span_singleton_self _
  · refine sup_le (sup_direction_le _ _) ?_
    rw [direction_eq_vectorSpan]; rw [vectorSpan_def]
    exact
      sInf_le_sInf fun p hp =>
        Set.Subset.trans
          (Set.singleton_subset_iff.2
            (vsub_mem_vsub (mem_affineSpan k (Set.mem_union_right _ hp₂))
              (mem_affineSpan k (Set.mem_union_left _ hp₁))))
          hp

/--
lemma `direction_sup_eq_sup_direction` / 引理 `direction_sup_eq_sup_direction`

English:
lemma direction_sup_eq_sup_direction
  statement: {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p in s₁)
  proof: by
  rw [direction_sup hp₁ hp₂]
  simp

中文:
引理 direction_sup_eq_sup_direction
  结论: {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p in s₁)
  证明: by
  rw [direction_sup hp₁ hp₂]
  simp

Depends on / 依赖: direction_sup
-/
lemma direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p in s₁)
    (hp₂ : p in s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction := by
  rw [direction_sup hp₁ hp₂]
  simp

/--
theorem `direction_affineSpan_insert` / 定理 `direction_affineSpan_insert`

English:
theorem direction_affineSpan_insert
  given: {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  rw [sup_comm]; rw [← Set.union_singleton]; rw [← coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _))]; rw [direction_affineSpan]
  simp

中文:
定理 direction_affineSpan_insert
  条件: {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  rw [sup_comm]; rw [← Set.union_singleton]; rw [← coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _))]; rw [direction_affineSpan]
  simp

Depends on / 依赖: Set.mem_singleton, Set.union_singleton, affineSpan, coe_affineSpan_singleton, direction, direction_affineSpan, direction_sup, mem_affineSpan, mem_singleton, sup_comm, union_singleton
-/
theorem direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) :
    (affineSpan k (insert p₂ (s : Set P))).direction =
    Submodule.span k {p₂ -ᵥ p₁} ⊔ s.direction := by
  rw [sup_comm]; rw [← Set.union_singleton]; rw [← coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _))]; rw [direction_affineSpan]
  simp

/--
theorem `mem_affineSpan_insert_iff` / 定理 `mem_affineSpan_insert_iff`

English:
theorem mem_affineSpan_insert_iff
  given: {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ in s) (p₂ p : P)
  proof: by
  rw [← mem_coe] at hp₁
  rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_insert_of_mem _ hp₁))]; rw [direction_affineSpan_insert hp₁]; rw [Submodule.mem_sup]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hp⟩
    rw [Submodule.mem_span_singleton] at hv₁
    rcases hv₁ with ⟨r, rfl

中文:
定理 mem_affineSpan_insert_iff
  条件: {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ in s) (p₂ p : P)
  证明: by
  rw [← mem_coe] at hp₁
  rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_insert_of_mem _ hp₁))]; rw [direction_affineSpan_insert hp₁]; rw [Submodule.mem_sup]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hp⟩
    rw [Submodule.mem_span_singleton] at hv₁
    rcases hv₁ with ⟨r, rfl

Depends on / 依赖: Set.mem_insert_of_mem, Submodule, Submodule.mem_span_singleton, Submodule.mem_sup, direction_affineSpan_insert, mem_affineSpan, mem_coe, mem_insert_of_mem, mem_span_singleton, mem_sup, sub_eq_zero, vadd_mem_of_mem_direction, vadd_vadd, vsub_eq_zero_iff_eq, vsub_right_mem_direction_iff_mem, vsub_vadd_eq_vsub_sub
-/
theorem mem_affineSpan_insert_iff {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ in s) (p₂ p : P) :
    p in affineSpan k (insert p₂ (s : Set P)) ↔
      exists r : k, exists p0 in s, p = r • (p₂ -ᵥ p₁ : V) +ᵥ p0 := by
  rw [← mem_coe] at hp₁
  rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_insert_of_mem _ hp₁))]; rw [direction_affineSpan_insert hp₁]; rw [Submodule.mem_sup]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hp⟩
    rw [Submodule.mem_span_singleton] at hv₁
    rcases hv₁ with ⟨r, rfl⟩
    use r, v₂ +ᵥ p₁, vadd_mem_of_mem_direction hv₂ hp₁
    symm at hp
    rw [← sub_eq_zero]; rw [← vsub_vadd_eq_vsub_sub]; rw [vsub_eq_zero_iff_eq] at hp
    rw [hp]; rw [vadd_vadd]
  · rintro ⟨r, p₃, hp₃, rfl⟩
    use r • (p₂ -ᵥ p₁), Submodule.mem_span_singleton.2 ⟨r, rfl⟩, p₃ -ᵥ p₁,
      vsub_mem_direction hp₃ hp₁
    rw [vadd_vsub_assoc]

variable (k) in
/--
lemma `vectorSpan_union_of_mem_of_mem` / 引理 `vectorSpan_union_of_mem_of_mem`

English:
lemma vectorSpan_union_of_mem_of_mem
  given: {s₁ s₂ : Set P} {p : P} (hp₁ : p in s₁) (hp₂ : p in s₂)
  proof: by
  simp_rw [← direction_affineSpan, span_union,
    direction_sup_eq_sup_direction (mem_affineSpan k hp₁) (mem_affineSpan k hp₂)]

中文:
引理 vectorSpan_union_of_mem_of_mem
  条件: {s₁ s₂ : Set P} {p : P} (hp₁ : p in s₁) (hp₂ : p in s₂)
  证明: by
  simp_rw [← direction_affineSpan, span_union,
    direction_sup_eq_sup_direction (mem_affineSpan k hp₁) (mem_affineSpan k hp₂)]

Depends on / 依赖: direction_affineSpan, direction_sup_eq_sup_direction, mem_affineSpan, simp_rw, span_union
-/
lemma vectorSpan_union_of_mem_of_mem {s₁ s₂ : Set P} {p : P} (hp₁ : p in s₁) (hp₂ : p in s₂) :
    vectorSpan k (s₁ union s₂) = vectorSpan k s₁ ⊔ vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan, span_union,
    direction_sup_eq_sup_direction (mem_affineSpan k hp₁) (mem_affineSpan k hp₂)]

end AffineSubspace

section MapComap

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

section

variable (f : P₁ ->ᵃ[k] P₂)

/-- The affine version of `LinearMap.map_span`. -/
@[simp]
/--
theorem `AffineMap.map_vectorSpan` / 定理 `AffineMap.map_vectorSpan`

English:
theorem AffineMap.map_vectorSpan
  given: {s : Set P₁}
  proof: by
  simp [vectorSpan_def, f.image_vsub_image]

中文:
定理 AffineMap.map_vectorSpan
  条件: {s : Set P₁}
  证明: by
  simp [vectorSpan_def, f.image_vsub_image]

Depends on / 依赖: f.image_vsub_image, image_vsub_image, vectorSpan_def
-/
theorem AffineMap.map_vectorSpan {s : Set P₁} :
    Submodule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s) := by
  simp [vectorSpan_def, f.image_vsub_image]

-- this name was backwards
@[deprecated (since := "2026-01-20")]
alias AffineMap.vectorSpan_image_eq_submodule_map := AffineMap.map_vectorSpan

namespace AffineSubspace

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (s : AffineSubspace k P₁)
  body: f '' s
  smul_vsub_vadd_mem' := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ in s by
    { simp only [SetLike.mem_coe, true_and, this]
      rw [AffineMap.map_vadd]; rw [map_smul]; rw [AffineMap.linearMap_vsub] }
    e

中文:
定义 map
  签名: (s : AffineSubspace k P₁)
  定义体: f '' s
  smul_vsub_vadd_mem' := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ in s by
    { simp only [SetLike.mem_coe, true_and, this]
      rw [AffineMap.map_vadd]; rw [map_smul]; rw [AffineMap.linearMap_vsub] }
    e
-/
def map (s : AffineSubspace k P₁) : AffineSubspace k P₂ where
  carrier := f '' s
  smul_vsub_vadd_mem' := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ in s by
    { simp only [SetLike.mem_coe, true_and, this]
      rw [AffineMap.map_vadd]; rw [map_smul]; rw [AffineMap.linearMap_vsub] }
    exact s.smul_vsub_vadd_mem t h₁ h₂ h₃

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (s : AffineSubspace k P₁)
  statement: (s.map f : Set P₂) = f '' s
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (s : AffineSubspace k P₁)
  结论: (s.map f : Set P₂) = f '' s
  证明: rfl

@[simp]
-/
theorem coe_map (s : AffineSubspace k P₁) : (s.map f : Set P₂) = f '' s :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁}
  proof: Iff.rfl

中文:
定理 mem_map
  条件: {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁} :
    x in s.map f ↔ exists y in s, f y = x :=
  Iff.rfl

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: {x : P₁} {s : AffineSubspace k P₁} (h : x in s)
  statement: f x in s.map f
  proof: Set.mem_image_of_mem _ h

@[simp 1100]

中文:
定理 mem_map_of_mem
  条件: {x : P₁} {s : AffineSubspace k P₁} (h : x in s)
  结论: f x in s.map f
  证明: Set.mem_image_of_mem _ h

@[simp 1100]

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem
-/
theorem mem_map_of_mem {x : P₁} {s : AffineSubspace k P₁} (h : x in s) : f x in s.map f :=
  Set.mem_image_of_mem _ h

@[simp 1100]
/--
theorem `mem_map_iff_mem_of_injective` / 定理 `mem_map_iff_mem_of_injective`

English:
theorem mem_map_iff_mem_of_injective
  statement: {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₁}
  proof: hf.mem_set_image

@[simp]

中文:
定理 mem_map_iff_mem_of_injective
  结论: {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₁}
  证明: hf.mem_set_image

@[simp]

Depends on / 依赖: hf.mem_set_image, mem_set_image
-/
theorem mem_map_iff_mem_of_injective {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₁}
    (hf : Function.Injective f) : f x in s.map f ↔ x in s :=
  hf.mem_set_image

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  statement: (⊥ : AffineSubspace k P₁).map f = ⊥
  proof: coe_injective image_empty f

@[simp]

中文:
定理 map_bot
  结论: (⊥ : AffineSubspace k P₁).map f = ⊥
  证明: coe_injective image_empty f

@[simp]

Depends on / 依赖: coe_injective, image_empty
-/
theorem map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥ :=
coe_injective image_empty f

@[simp]
/--
theorem `map_eq_bot_iff` / 定理 `map_eq_bot_iff`

English:
theorem map_eq_bot_iff
  given: {s : AffineSubspace k P₁}
  statement: s.map f = ⊥ ↔ s = ⊥
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← coe_eq_bot_iff, coe_map, image_eq_empty, coe_eq_bot_iff] at h
  · rw [h, map_bot]

@[simp]

中文:
定理 map_eq_bot_iff
  条件: {s : AffineSubspace k P₁}
  结论: s.map f = ⊥ ↔ s = ⊥
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← coe_eq_bot_iff, coe_map, image_eq_empty, coe_eq_bot_iff] at h
  · rw [h, map_bot]

@[simp]

Depends on / 依赖: coe_eq_bot_iff, coe_map, image_eq_empty, map_bot
-/
theorem map_eq_bot_iff {s : AffineSubspace k P₁} : s.map f = ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← coe_eq_bot_iff, coe_map, image_eq_empty, coe_eq_bot_iff] at h
  · rw [h, map_bot]

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (s : AffineSubspace k P₁)
  statement: s.map (AffineMap.id k P₁) = s
  proof: coe_injective image_id _

中文:
定理 map_id
  条件: (s : AffineSubspace k P₁)
  结论: s.map (AffineMap.id k P₁) = s
  证明: coe_injective image_id _

Depends on / 依赖: coe_injective, image_id
-/
theorem map_id (s : AffineSubspace k P₁) : s.map (AffineMap.id k P₁) = s :=
coe_injective image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃)
  proof: coe_injective image_image _ _ _

@[simp]

中文:
定理 map_map
  条件: (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃)
  证明: coe_injective image_image _ _ _

@[simp]

Depends on / 依赖: coe_injective, image_image
-/
theorem map_map (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃) :
    (s.map f).map g = s.map (g.comp f) :=
coe_injective image_image _ _ _

@[simp]
/--
theorem `map_direction` / 定理 `map_direction`

English:
theorem map_direction
  given: (s : AffineSubspace k P₁)
  proof: by
  simp [direction_eq_vectorSpan, AffineMap.map_vectorSpan]

中文:
定理 map_direction
  条件: (s : AffineSubspace k P₁)
  证明: by
  simp [direction_eq_vectorSpan, AffineMap.map_vectorSpan]

Depends on / 依赖: AffineMap, AffineMap.map_vectorSpan, direction_eq_vectorSpan, map_vectorSpan
-/
theorem map_direction (s : AffineSubspace k P₁) :
    (s.map f).direction = s.direction.map f.linear := by
  simp [direction_eq_vectorSpan, AffineMap.map_vectorSpan]

/--
theorem `map_span` / 定理 `map_span`

English:
theorem map_span
  given: (s : Set P₁)
  statement: (affineSpan k s).map f = affineSpan k (f '' s)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
  apply ext_of_direction_eq
  · simp [direction_affineSpan]
  · exact ⟨f p, mem_image_of_mem f (subset_affineSpan k _ hp),
          subset_affineSpan k _ (mem_image_of_mem f hp)⟩

@[gcongr]

中文:
定理 map_span
  条件: (s : Set P₁)
  结论: (affineSpan k s).map f = affineSpan k (f '' s)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
  apply ext_of_direction_eq
  · simp [direction_affineSpan]
  · exact ⟨f p, mem_image_of_mem f (subset_affineSpan k _ hp),
          subset_affineSpan k _ (mem_image_of_mem f hp)⟩

@[gcongr]

Depends on / 依赖: direction_affineSpan, eq_empty_or_nonempty, ext_of_direction_eq, mem_image_of_mem, s.eq_empty_or_nonempty, subset_affineSpan
-/
theorem map_span (s : Set P₁) : (affineSpan k s).map f = affineSpan k (f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
  apply ext_of_direction_eq
  · simp [direction_affineSpan]
  · exact ⟨f p, mem_image_of_mem f (subset_affineSpan k _ hp),
          subset_affineSpan k _ (mem_image_of_mem f hp)⟩

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {s₁ s₂ : AffineSubspace k P₁} (h : s₁ <= s₂)
  statement: s₁.map f <= s₂.map f
  proof: Set.image_mono h

中文:
定理 map_mono
  条件: {s₁ s₂ : AffineSubspace k P₁} (h : s₁ <= s₂)
  结论: s₁.map f <= s₂.map f
  证明: Set.image_mono h

Depends on / 依赖: Set.image_mono, image_mono
-/
theorem map_mono {s₁ s₂ : AffineSubspace k P₁} (h : s₁ <= s₂) : s₁.map f <= s₂.map f :=
  Set.image_mono h

/--
lemma `map_inf_le` / 引理 `map_inf_le`

English:
lemma map_inf_le
  given: (s₁ s₂ : AffineSubspace k P₁)
  statement: (s₁ ⊓ s₂).map f <= s₁.map f ⊓ s₂.map f
  proof: le_inf (map_mono _ inf_le_left) (map_mono _ inf_le_right)

中文:
引理 map_inf_le
  条件: (s₁ s₂ : AffineSubspace k P₁)
  结论: (s₁ ⊓ s₂).map f <= s₁.map f ⊓ s₂.map f
  证明: le_inf (map_mono _ inf_le_left) (map_mono _ inf_le_right)

Depends on / 依赖: inf_le_left, inf_le_right, le_inf, map_mono
-/
lemma map_inf_le (s₁ s₂ : AffineSubspace k P₁) : (s₁ ⊓ s₂).map f <= s₁.map f ⊓ s₂.map f :=
  le_inf (map_mono _ inf_le_left) (map_mono _ inf_le_right)

/--
lemma `map_inf_eq` / 引理 `map_inf_eq`

English:
lemma map_inf_eq
  given: (hf : Function.Injective f) (s₁ s₂ : AffineSubspace k P₁)
  proof: by
  ext p
  simp [mem_inf_iff]
  grind

中文:
引理 map_inf_eq
  条件: (hf : Function.Injective f) (s₁ s₂ : AffineSubspace k P₁)
  证明: by
  ext p
  simp [mem_inf_iff]
  grind

Depends on / 依赖: mem_inf_iff
-/
lemma map_inf_eq (hf : Function.Injective f) (s₁ s₂ : AffineSubspace k P₁) :
    (s₁ ⊓ s₂).map f = s₁.map f ⊓ s₂.map f := by
  ext p
  simp [mem_inf_iff]
  grind

/--
lemma `map_mk'` / 引理 `map_mk'`

English:
lemma map_mk'
  given: (p : P₁) (direction : Submodule k V₁)
  proof: by
  ext q
  simp only [mem_map, mem_mk', Submodule.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r -ᵥ p, hr, by simp⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨r +ᵥ p, by simp [hr], by simp [he]⟩

中文:
引理 map_mk'
  条件: (p : P₁) (direction : Submodule k V₁)
  证明: by
  ext q
  simp only [mem_map, mem_mk', Submodule.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r -ᵥ p, hr, by simp⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨r +ᵥ p, by simp [hr], by simp [he]⟩

Depends on / 依赖: Submodule, Submodule.mem_map, mem_map, mem_mk
-/
lemma map_mk' (p : P₁) (direction : Submodule k V₁) :
    (mk' p direction).map f = mk' (f p) (direction.map f.linear) := by
  ext q
  simp only [mem_map, mem_mk', Submodule.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r -ᵥ p, hr, by simp⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨r +ᵥ p, by simp [hr], by simp [he]⟩

section inclusion
variable {S₁ S₂ : AffineSubspace k P₁} [Nonempty S₁]

/-- Affine map from a smaller to a larger subspace of the same space.

This is the affine version of `Submodule.inclusion`. -/
@[simps linear]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (h : S₁ <= S₂)
  body: Nonempty.map (Set.inclusion h) ‹_›
    S₁ ->ᵃ[k] S₂ :=
  letI := Nonempty.map (Set.inclusion h) ‹_›
  { toFun := Set.inclusion h
linear := Submodule.inclusion AffineSubspace.direction_le h
    map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl }

@[simp]

中文:
定义 inclusion
  签名: (h : S₁ <= S₂)
  定义体: Nonempty.map (Set.inclusion h) ‹_›
    S₁ ->ᵃ[k] S₂ :=
  letI := Nonempty.map (Set.inclusion h) ‹_›
  { toFun := Set.inclusion h
linear := Submodule.inclusion AffineSubspace.direction_le h
    map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl }

@[simp]

Depends on / 依赖: Nonempty, Nonempty.map, Set.inclusion, inclusion
-/
def inclusion (h : S₁ <= S₂) :
    letI := Nonempty.map (Set.inclusion h) ‹_›
    S₁ ->ᵃ[k] S₂ :=
  letI := Nonempty.map (Set.inclusion h) ‹_›
  { toFun := Set.inclusion h
linear := Submodule.inclusion AffineSubspace.direction_le h
    map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl }

@[simp]
/--
theorem `coe_inclusion_apply` / 定理 `coe_inclusion_apply`

English:
theorem coe_inclusion_apply
  given: (h : S₁ <= S₂) (x : S₁)
  statement: (inclusion h x : P₁) = x
  proof: rfl

@[simp]

中文:
定理 coe_inclusion_apply
  条件: (h : S₁ <= S₂) (x : S₁)
  结论: (inclusion h x : P₁) = x
  证明: rfl

@[simp]
-/
theorem coe_inclusion_apply (h : S₁ <= S₂) (x : S₁) : (inclusion h x : P₁) = x :=
  rfl

@[simp]
/--
theorem `inclusion_rfl` / 定理 `inclusion_rfl`

English:
theorem inclusion_rfl
  statement: inclusion (le_refl S₁) = AffineMap.id k S₁
  proof: rfl

中文:
定理 inclusion_rfl
  结论: inclusion (le_refl S₁) = AffineMap.id k S₁
  证明: rfl
-/
theorem inclusion_rfl : inclusion (le_refl S₁) = AffineMap.id k S₁ := rfl

end inclusion

end AffineSubspace

namespace AffineMap

@[simp]
/--
theorem `map_top_of_surjective` / 定理 `map_top_of_surjective`

English:
theorem map_top_of_surjective
  given: (hf : Function.Surjective f)
  statement: AffineSubspace.map f ⊤ = ⊤
  proof: by
  rw [AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf

中文:
定理 map_top_of_surjective
  条件: (hf : Function.Surjective f)
  结论: AffineSubspace.map f ⊤ = ⊤
  证明: by
  rw [AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf

Depends on / 依赖: AffineSubspace, AffineSubspace.ext_iff, ext_iff, image_univ_of_surjective
-/
theorem map_top_of_surjective (hf : Function.Surjective f) : AffineSubspace.map f ⊤ = ⊤ := by
  rw [AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf

/--
theorem `span_eq_top_of_surjective` / 定理 `span_eq_top_of_surjective`

English:
theorem span_eq_top_of_surjective
  statement: {s : Set P₁} (hf : Function.Surjective f)
  proof: by
  rw [← AffineSubspace.map_span]; rw [h]; rw [map_top_of_surjective f hf]

中文:
定理 span_eq_top_of_surjective
  结论: {s : Set P₁} (hf : Function.Surjective f)
  证明: by
  rw [← AffineSubspace.map_span]; rw [h]; rw [map_top_of_surjective f hf]

Depends on / 依赖: AffineSubspace, AffineSubspace.map_span, map_span, map_top_of_surjective
-/
theorem span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f)
    (h : affineSpan k s = ⊤) : affineSpan k (f '' s) = ⊤ := by
  rw [← AffineSubspace.map_span]; rw [h]; rw [map_top_of_surjective f hf]

/--
theorem `linear_eqOn_vectorSpan` / 定理 `linear_eqOn_vectorSpan`

English:
theorem linear_eqOn_vectorSpan
  statement: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  proof: by
  simp only [vectorSpan_def]
  apply LinearMap.eqOn_span
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, h_agree hy]

中文:
定理 linear_eqOn_vectorSpan
  结论: {V₂ P₂ : 类型} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  证明: by
  simp only [vectorSpan_def]
  apply LinearMap.eqOn_span
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, h_agree hy]

Depends on / 依赖: LinearMap, LinearMap.eqOn_span, eqOn_span, h_agree, vectorSpan_def
-/
theorem linear_eqOn_vectorSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f.linear g.linear (vectorSpan k s) := by
  simp only [vectorSpan_def]
  apply LinearMap.eqOn_span
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, h_agree hy]

/--
theorem `eqOn_affineSpan` / 定理 `eqOn_affineSpan`

English:
theorem eqOn_affineSpan
  statement: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩; · simp
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, linear_eqOn_vectorSpan h_agree hy]

中文:
定理 eqOn_affineSpan
  结论: {V₂ P₂ : 类型} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩; · simp
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, linear_eqOn_vectorSpan h_agree hy]

Depends on / 依赖: eq_empty_or_nonempty, h_agree, linear_eqOn_vectorSpan, s.eq_empty_or_nonempty
-/
theorem eqOn_affineSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f g (affineSpan k s) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩; · simp
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, linear_eqOn_vectorSpan h_agree hy]

/--
theorem `ext_on` / 定理 `ext_on`

English:
theorem ext_on
  statement: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  proof: by
  simpa [h_span] using eqOn_affineSpan h_agree

中文:
定理 ext_on
  结论: {V₂ P₂ : 类型} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  证明: by
  simpa [h_span] using eqOn_affineSpan h_agree

Depends on / 依赖: eqOn_affineSpan, h_agree, h_span
-/
theorem ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂}
    (h_span : affineSpan k s = ⊤)
    (h_agree : s.EqOn f g) : f = g := by
  simpa [h_span] using eqOn_affineSpan h_agree

end AffineMap

namespace AffineEquiv

/--
theorem `ext_on` / 定理 `ext_on`

English:
theorem ext_on
  statement: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  proof: AffineEquiv.toAffineMap_inj.mp AffineMap.ext_on h_span h_agree

中文:
定理 ext_on
  结论: {V₂ P₂ : 类型} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  证明: AffineEquiv.toAffineMap_inj.mp AffineMap.ext_on h_span h_agree

Depends on / 依赖: AffineEquiv, AffineEquiv.toAffineMap_inj.mp, AffineMap, AffineMap.ext_on, ext_on, h_agree, h_span, toAffineMap_inj
-/
theorem ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} (h_span : affineSpan k s = ⊤)
    (T₁ T₂ : P₁ ≃ᵃ[k] P₂) (h_agree : s.EqOn T₁ T₂) : T₁ = T₂ :=
AffineEquiv.toAffineMap_inj.mp AffineMap.ext_on h_span h_agree

section ofEq
variable (S₁ S₂ : AffineSubspace k P₁) [Nonempty S₁] [Nonempty S₂]

/-- Affine equivalence between two equal affine subspace.

This is the affine version of `LinearEquiv.ofEq`. -/
@[simps linear]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : S₁ = S₂)
  body: Equiv.setCongr congr_arg _ h
linear := .ofEq _ _ congr_arg _ h
  map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl

@[simp]

中文:
定义 ofEq
  签名: (h : S₁ = S₂)
  定义体: Equiv.setCongr congr_arg _ h
linear := .ofEq _ _ congr_arg _ h
  map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl

@[simp]

Depends on / 依赖: Equiv.setCongr, congr_arg, setCongr
-/
def ofEq (h : S₁ = S₂) : S₁ ≃ᵃ[k] S₂ where
toEquiv := Equiv.setCongr congr_arg _ h
linear := .ofEq _ _ congr_arg _ h
  map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl

@[simp]
/--
theorem `coe_ofEq_apply` / 定理 `coe_ofEq_apply`

English:
theorem coe_ofEq_apply
  given: (h : S₁ = S₂) (x : S₁)
  statement: (ofEq S₁ S₂ h x : P₁) = x
  proof: rfl

@[simp]

中文:
定理 coe_ofEq_apply
  条件: (h : S₁ = S₂) (x : S₁)
  结论: (ofEq S₁ S₂ h x : P₁) = x
  证明: rfl

@[simp]
-/
theorem coe_ofEq_apply (h : S₁ = S₂) (x : S₁) : (ofEq S₁ S₂ h x : P₁) = x :=
  rfl

@[simp]
/--
theorem `ofEq_symm` / 定理 `ofEq_symm`

English:
theorem ofEq_symm
  given: (h : S₁ = S₂)
  statement: (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm
  proof: by
  ext
  rfl

@[simp]

中文:
定理 ofEq_symm
  条件: (h : S₁ = S₂)
  结论: (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm
  证明: by
  ext
  rfl

@[simp]
-/
theorem ofEq_symm (h : S₁ = S₂) : (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm := by
  ext
  rfl

@[simp]
/--
theorem `ofEq_rfl` / 定理 `ofEq_rfl`

English:
theorem ofEq_rfl
  statement: ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁
  proof: rfl

中文:
定理 ofEq_rfl
  结论: ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁
  证明: rfl
-/
theorem ofEq_rfl : ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁ := rfl

end ofEq

/--
theorem `span_eq_top_iff` / 定理 `span_eq_top_iff`

English:
theorem span_eq_top_iff
  given: {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂)
  proof: by
  refine ⟨(e : P₁ ->ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, ?_⟩
  intro h
  have : s = e.symm '' e '' s := by rw [← image_comp]; simp
  rw [this]
  exact (e.symm : P₂ ->ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h

中文:
定理 span_eq_top_iff
  条件: {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂)
  证明: by
  refine ⟨(e : P₁ ->ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, ?_⟩
  intro h
  have : s = e.symm '' e '' s := by rw [← image_comp]; simp
  rw [this]
  exact (e.symm : P₂ ->ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h

Depends on / 依赖: e.surjective, e.symm, e.symm.surjective, image_comp, span_eq_top_of_surjective, surjective
-/
theorem span_eq_top_iff {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂) :
    affineSpan k s = ⊤ ↔ affineSpan k (e '' s) = ⊤ := by
  refine ⟨(e : P₁ ->ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, ?_⟩
  intro h
  have : s = e.symm '' e '' s := by rw [← image_comp]; simp
  rw [this]
  exact (e.symm : P₂ ->ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h

end AffineEquiv

end

namespace AffineSubspace

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂)
  body: f ⁻¹' s
  smul_vsub_vadd_mem' t p₁ p₂ p₃ (hp₁ : f p₁ in s) (hp₂ : f p₂ in s) (hp₃ : f p₃ in s) :=
    show f _ in s by
      rw [AffineMap.map_vadd]; rw [map_smul]; rw [AffineMap.linearMap_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃

@[simp]

中文:
定义 comap
  签名: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂)
  定义体: f ⁻¹' s
  smul_vsub_vadd_mem' t p₁ p₂ p₃ (hp₁ : f p₁ in s) (hp₂ : f p₂ in s) (hp₃ : f p₃ in s) :=
    show f _ in s by
      rw [AffineMap.map_vadd]; rw [map_smul]; rw [AffineMap.linearMap_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃

@[simp]
-/
def comap (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂) : AffineSubspace k P₁ where
  carrier := f ⁻¹' s
  smul_vsub_vadd_mem' t p₁ p₂ p₃ (hp₁ : f p₁ in s) (hp₂ : f p₂ in s) (hp₃ : f p₃ in s) :=
    show f _ in s by
      rw [AffineMap.map_vadd]; rw [map_smul]; rw [AffineMap.linearMap_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂)
  statement: (s.comap f : Set P₁) = f ⁻¹' ↑s
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂)
  结论: (s.comap f : Set P₁) = f ⁻¹' ↑s
  证明: rfl

@[simp]
-/
theorem coe_comap (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f : Set P₁) = f ⁻¹' ↑s :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂}
  statement: x in s.comap f ↔ f x in s
  proof: Iff.rfl

@[gcongr]

中文:
定理 mem_comap
  条件: {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂}
  结论: x in s.comap f ↔ f x in s
  证明: Iff.rfl

@[gcongr]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂} : x in s.comap f ↔ f x in s :=
  Iff.rfl

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: {f : P₁ ->ᵃ[k] P₂} {s t : AffineSubspace k P₂}
  statement: s <= t -> s.comap f <= t.comap f
  proof: preimage_mono

@[simp]

中文:
定理 comap_mono
  条件: {f : P₁ ->ᵃ[k] P₂} {s t : AffineSubspace k P₂}
  结论: s <= t -> s.comap f <= t.comap f
  证明: preimage_mono

@[simp]

Depends on / 依赖: preimage_mono
-/
theorem comap_mono {f : P₁ ->ᵃ[k] P₂} {s t : AffineSubspace k P₂} : s <= t -> s.comap f <= t.comap f :=
  preimage_mono

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: {f : P₁ ->ᵃ[k] P₂}
  statement: (⊤ : AffineSubspace k P₂).comap f = ⊤
  proof: by
  rw [AffineSubspace.ext_iff]
  exact preimage_univ (f := f)

中文:
定理 comap_top
  条件: {f : P₁ ->ᵃ[k] P₂}
  结论: (⊤ : AffineSubspace k P₂).comap f = ⊤
  证明: by
  rw [AffineSubspace.ext_iff]
  exact preimage_univ (f := f)

Depends on / 依赖: AffineSubspace, AffineSubspace.ext_iff, ext_iff, preimage_univ
-/
theorem comap_top {f : P₁ ->ᵃ[k] P₂} : (⊤ : AffineSubspace k P₂).comap f = ⊤ := by
  rw [AffineSubspace.ext_iff]
  exact preimage_univ (f := f)

/--
theorem `comap_bot` / 定理 `comap_bot`

English:
theorem comap_bot
  given: (f : P₁ ->ᵃ[k] P₂)
  statement: comap f ⊥ = ⊥
  proof: rfl

@[simp]

中文:
定理 comap_bot
  条件: (f : P₁ ->ᵃ[k] P₂)
  结论: comap f ⊥ = ⊥
  证明: rfl

@[simp]
-/
@[simp] theorem comap_bot (f : P₁ ->ᵃ[k] P₂) : comap f ⊥ = ⊥ := rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (s : AffineSubspace k P₁)
  statement: s.comap (AffineMap.id k P₁) = s
  proof: rfl

中文:
定理 comap_id
  条件: (s : AffineSubspace k P₁)
  结论: s.comap (AffineMap.id k P₁) = s
  证明: rfl
-/
theorem comap_id (s : AffineSubspace k P₁) : s.comap (AffineMap.id k P₁) = s :=
  rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (s : AffineSubspace k P₃) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃)
  proof: rfl

中文:
定理 comap_comap
  条件: (s : AffineSubspace k P₃) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃)
  证明: rfl
-/
theorem comap_comap (s : AffineSubspace k P₃) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

-- lemmas about map and comap derived from the Galois connection
/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : P₁ ->ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂}
  proof: image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : P₁ ->ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂}
  证明: image_subset_iff

Depends on / 依赖: image_subset_iff
-/
theorem map_le_iff_le_comap {f : P₁ ->ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂} :
    s.map f <= t ↔ s <= t.comap f :=
  image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : P₁ ->ᵃ[k] P₂)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : P₁ ->ᵃ[k] P₂)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap
-/
theorem gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂)
  statement: (s.comap f).map f <= s
  proof: (gc_map_comap f).l_u_le _

中文:
定理 map_comap_le
  条件: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂)
  结论: (s.comap f).map f <= s
  证明: (gc_map_comap f).l_u_le _

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).map f <= s :=
  (gc_map_comap f).l_u_le _

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₁)
  statement: s <= (s.map f).comap f
  proof: (gc_map_comap f).le_u_l _

中文:
定理 le_comap_map
  条件: (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₁)
  结论: s <= (s.map f).comap f
  证明: (gc_map_comap f).le_u_l _

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₁) : s <= (s.map f).comap f :=
  (gc_map_comap f).le_u_l _

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (s t : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂)
  statement: (s ⊔ t).map f = s.map f ⊔ t.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (s t : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂)
  结论: (s ⊔ t).map f = s.map f ⊔ t.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (s t : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₁)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₁)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₁) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (s t : AffineSubspace k P₂) (f : P₁ ->ᵃ[k] P₂)
  proof: (gc_map_comap f).u_inf

中文:
定理 comap_inf
  条件: (s t : AffineSubspace k P₂) (f : P₁ ->ᵃ[k] P₂)
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (s t : AffineSubspace k P₂) (f : P₁ ->ᵃ[k] P₂) :
    (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

/--
theorem `comap_supr` / 定理 `comap_supr`

English:
theorem comap_supr
  given: {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₂)
  proof: (gc_map_comap f).u_iInf

@[simp]

中文:
定理 comap_supr
  条件: {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₂)
  证明: (gc_map_comap f).u_iInf

@[simp]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_supr {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₂) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/--
theorem `comap_symm` / 定理 `comap_symm`

English:
theorem comap_symm
  given: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
  proof: coe_injective e.preimage_symm _

@[simp]

中文:
定理 comap_symm
  条件: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
  证明: coe_injective e.preimage_symm _

@[simp]

Depends on / 依赖: coe_injective, e.preimage_symm, preimage_symm
-/
theorem comap_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) :
    s.comap (e.symm : P₂ ->ᵃ[k] P₁) = s.map e :=
coe_injective e.preimage_symm _

@[simp]
/--
theorem `map_symm` / 定理 `map_symm`

English:
theorem map_symm
  given: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₂)
  proof: coe_injective e.image_symm _

中文:
定理 map_symm
  条件: (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₂)
  证明: coe_injective e.image_symm _

Depends on / 依赖: coe_injective, e.image_symm, image_symm
-/
theorem map_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₂) :
    s.map (e.symm : P₂ ->ᵃ[k] P₁) = s.comap e :=
coe_injective e.image_symm _

/--
theorem `comap_span` / 定理 `comap_span`

English:
theorem comap_span
  given: (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂)
  proof: by
  rw [← map_symm]; rw [map_span]; rw [AffineEquiv.coe_coe]; rw [f.image_symm]

中文:
定理 comap_span
  条件: (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂)
  证明: by
  rw [← map_symm]; rw [map_span]; rw [AffineEquiv.coe_coe]; rw [f.image_symm]

Depends on / 依赖: AffineEquiv, AffineEquiv.coe_coe, coe_coe, f.image_symm, image_symm, map_span, map_symm
-/
theorem comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) :
    (affineSpan k s).comap (f : P₁ ->ᵃ[k] P₂) = affineSpan k (f ⁻¹' s) := by
  rw [← map_symm]; rw [map_span]; rw [AffineEquiv.coe_coe]; rw [f.image_symm]

/--
Definition of `gciMapComap` / `gciMapComap` 的定义

English:
definition gciMapComap
  signature: {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f)
  body: (gc_map_comap f).toGaloisCoinsertion fun s p => by simp; grind

中文:
定义 gciMapComap
  签名: {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f)
  定义体: (gc_map_comap f).toGaloisCoinsertion fun s p => by simp; grind

Depends on / 依赖: gc_map_comap, toGaloisCoinsertion
-/
def gciMapComap {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f) :
    GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun s p => by simp; grind

/--
lemma `comap_map_eq_of_injective` / 引理 `comap_map_eq_of_injective`

English:
lemma comap_map_eq_of_injective
  statement: {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f)
  proof: (gciMapComap hf).u_l_eq _

中文:
引理 comap_map_eq_of_injective
  结论: {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f)
  证明: (gciMapComap hf).u_l_eq _

Depends on / 依赖: gciMapComap, u_l_eq
-/
lemma comap_map_eq_of_injective {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f)
    (s : AffineSubspace k P₁) : (s.map f).comap f = s :=
  (gciMapComap hf).u_l_eq _

end AffineSubspace

end MapComap

namespace AffineSubspace

open AffineEquiv

variable {k V W P Q : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]
  [AddCommGroup W] [Module k W] [AffineSpace W Q]

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : AffineSubspace k P) (t : AffineSubspace k Q)
  body: (s : Set P) ×ˢ (t : Set Q)
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    ⟨s.smul_vsub_vadd_mem' c hp₁.1 hp₂.1 hp₃.1, t.smul_vsub_vadd_mem' c hp₁.2 hp₂.2 hp₃.2⟩

@[simp]

中文:
定义 prod
  签名: (s : AffineSubspace k P) (t : AffineSubspace k Q)
  定义体: (s : Set P) ×ˢ (t : Set Q)
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    ⟨s.smul_vsub_vadd_mem' c hp₁.1 hp₂.1 hp₃.1, t.smul_vsub_vadd_mem' c hp₁.2 hp₂.2 hp₃.2⟩

@[simp]
-/
def prod (s : AffineSubspace k P) (t : AffineSubspace k Q) : AffineSubspace k (P × Q) where
  carrier := (s : Set P) ×ˢ (t : Set Q)
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    ⟨s.smul_vsub_vadd_mem' c hp₁.1 hp₂.1 hp₃.1, t.smul_vsub_vadd_mem' c hp₁.2 hp₂.2 hp₃.2⟩

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : AffineSubspace k P) (t : AffineSubspace k Q)
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (s : AffineSubspace k P) (t : AffineSubspace k Q)
  证明: rfl

@[simp]
-/
theorem coe_prod (s : AffineSubspace k P) (t : AffineSubspace k Q) :
    (s.prod t : Set (P × Q)) = (s : Set P) ×ˢ (t : Set Q) :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: (s : AffineSubspace k P) (t : AffineSubspace k Q) (x : P × Q)
  proof: Set.mem_prod

@[gcongr]

中文:
定理 mem_prod
  条件: (s : AffineSubspace k P) (t : AffineSubspace k Q) (x : P × Q)
  证明: Set.mem_prod

@[gcongr]

Depends on / 依赖: Set.mem_prod, mem_prod
-/
theorem mem_prod (s : AffineSubspace k P) (t : AffineSubspace k Q) (x : P × Q) :
    x in s.prod t ↔ x.1 in s ∧ x.2 in t :=
  Set.mem_prod

@[gcongr]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  statement: {s₁ s₂ : AffineSubspace k P} {t₁ t₂ : AffineSubspace k Q}
  proof: Set.prod_mono hs ht

@[simp]

中文:
定理 prod_mono
  结论: {s₁ s₂ : AffineSubspace k P} {t₁ t₂ : AffineSubspace k Q}
  证明: Set.prod_mono hs ht

@[simp]

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {s₁ s₂ : AffineSubspace k P} {t₁ t₂ : AffineSubspace k Q}
    (hs : s₁ <= s₂) (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

@[simp]
/--
theorem `prod_top_top` / 定理 `prod_top_top`

English:
theorem prod_top_top
  statement: (⊤ : AffineSubspace k P).prod (⊤ : AffineSubspace k Q) = ⊤
  proof: by
  ext; simp

@[simp]

中文:
定理 prod_top_top
  结论: (⊤ : AffineSubspace k P).prod (⊤ : AffineSubspace k Q) = ⊤
  证明: by
  ext; simp

@[simp]
-/
theorem prod_top_top : (⊤ : AffineSubspace k P).prod (⊤ : AffineSubspace k Q) = ⊤ := by
  ext; simp

@[simp]
/--
theorem `prod_bot_right` / 定理 `prod_bot_right`

English:
theorem prod_bot_right
  given: (s : AffineSubspace k P)
  statement: s.prod (⊥ : AffineSubspace k Q) = ⊥
  proof: by
  simp [AffineSubspace.ext_iff]

@[simp]

中文:
定理 prod_bot_right
  条件: (s : AffineSubspace k P)
  结论: s.prod (⊥ : AffineSubspace k Q) = ⊥
  证明: by
  simp [AffineSubspace.ext_iff]

@[simp]

Depends on / 依赖: AffineSubspace, AffineSubspace.ext_iff, ext_iff
-/
theorem prod_bot_right (s : AffineSubspace k P) : s.prod (⊥ : AffineSubspace k Q) = ⊥ := by
  simp [AffineSubspace.ext_iff]

@[simp]
/--
theorem `prod_bot_left` / 定理 `prod_bot_left`

English:
theorem prod_bot_left
  given: (t : AffineSubspace k P)
  statement: (⊥ : AffineSubspace k Q).prod t = ⊥
  proof: by
  simp [AffineSubspace.ext_iff]

中文:
定理 prod_bot_left
  条件: (t : AffineSubspace k P)
  结论: (⊥ : AffineSubspace k Q).prod t = ⊥
  证明: by
  simp [AffineSubspace.ext_iff]

Depends on / 依赖: AffineSubspace, AffineSubspace.ext_iff, ext_iff
-/
theorem prod_bot_left (t : AffineSubspace k P) : (⊥ : AffineSubspace k Q).prod t = ⊥ := by
  simp [AffineSubspace.ext_iff]

/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  given: (s₁ s₂ : AffineSubspace k P) (t₁ t₂ : AffineSubspace k Q)
  proof: SetLike.coe_injective Set.prod_inter_prod

中文:
定理 prod_inf_prod
  条件: (s₁ s₂ : AffineSubspace k P) (t₁ t₂ : AffineSubspace k Q)
  证明: SetLike.coe_injective Set.prod_inter_prod

Depends on / 依赖: Set.prod_inter_prod, SetLike, SetLike.coe_injective, coe_injective, prod_inter_prod
-/
theorem prod_inf_prod (s₁ s₂ : AffineSubspace k P) (t₁ t₂ : AffineSubspace k Q) :
    s₁.prod t₁ ⊓ s₂.prod t₂ = (s₁ ⊓ s₂).prod (t₁ ⊓ t₂) :=
  SetLike.coe_injective Set.prod_inter_prod

/--
theorem `_root_.vectorSpan_prod_le` / 定理 `_root_.vectorSpan_prod_le`

English:
theorem _root_.vectorSpan_prod_le
  given: (s : Set P) (t : Set Q)
  proof: by
  simpa [vectorSpan_def, Set.prod_vsub_prod_comm] using Submodule.span_prod_le (s -ᵥ s) (t -ᵥ t)

中文:
定理 _root_.vectorSpan_prod_le
  条件: (s : Set P) (t : Set Q)
  证明: by
  simpa [vectorSpan_def, Set.prod_vsub_prod_comm] using Submodule.span_prod_le (s -ᵥ s) (t -ᵥ t)

Depends on / 依赖: Set.prod_vsub_prod_comm, Submodule, Submodule.span_prod_le, prod_vsub_prod_comm, span_prod_le, vectorSpan_def
-/
theorem _root_.vectorSpan_prod_le (s : Set P) (t : Set Q) :
    vectorSpan k (s ×ˢ t) <= (vectorSpan k s).prod (vectorSpan k t) := by
  simpa [vectorSpan_def, Set.prod_vsub_prod_comm] using Submodule.span_prod_le (s -ᵥ s) (t -ᵥ t)

/--
theorem `direction_prod_le` / 定理 `direction_prod_le`

English:
theorem direction_prod_le
  given: (s : AffineSubspace k P) (t : AffineSubspace k Q)
  proof: by
  simpa [direction_eq_vectorSpan, coe_prod] using vectorSpan_prod_le (s : Set P) (t : Set Q)

中文:
定理 direction_prod_le
  条件: (s : AffineSubspace k P) (t : AffineSubspace k Q)
  证明: by
  simpa [direction_eq_vectorSpan, coe_prod] using vectorSpan_prod_le (s : Set P) (t : Set Q)

Depends on / 依赖: coe_prod, direction_eq_vectorSpan, vectorSpan_prod_le
-/
theorem direction_prod_le (s : AffineSubspace k P) (t : AffineSubspace k Q) :
    (s.prod t).direction <= s.direction.prod t.direction := by
  simpa [direction_eq_vectorSpan, coe_prod] using vectorSpan_prod_le (s : Set P) (t : Set Q)

/--
theorem `_root_.vectorSpan_prod_eq` / 定理 `_root_.vectorSpan_prod_eq`

English:
theorem _root_.vectorSpan_prod_eq
  given: {s : Set P} {t : Set Q} (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  rw [vectorSpan_def]; rw [Set.prod_vsub_prod_comm]
  exact Submodule.span_prod_eq k hs.zero_mem_vsub_self ht.zero_mem_vsub_self

中文:
定理 _root_.vectorSpan_prod_eq
  条件: {s : Set P} {t : Set Q} (hs : s.Nonempty) (ht : t.Nonempty)
  证明: by
  rw [vectorSpan_def]; rw [Set.prod_vsub_prod_comm]
  exact Submodule.span_prod_eq k hs.zero_mem_vsub_self ht.zero_mem_vsub_self

Depends on / 依赖: Set.prod_vsub_prod_comm, Submodule, Submodule.span_prod_eq, hs.zero_mem_vsub_self, ht.zero_mem_vsub_self, prod_vsub_prod_comm, span_prod_eq, vectorSpan_def, zero_mem_vsub_self
-/
theorem _root_.vectorSpan_prod_eq {s : Set P} {t : Set Q} (hs : s.Nonempty) (ht : t.Nonempty) :
    vectorSpan k (s ×ˢ t) = (vectorSpan k s).prod (vectorSpan k t) := by
  rw [vectorSpan_def]; rw [Set.prod_vsub_prod_comm]
  exact Submodule.span_prod_eq k hs.zero_mem_vsub_self ht.zero_mem_vsub_self

/--
theorem `direction_prod_eq` / 定理 `direction_prod_eq`

English:
theorem direction_prod_eq
  statement: {s : AffineSubspace k P} {t : AffineSubspace k Q}
  proof: by
  simp [direction_eq_vectorSpan, vectorSpan_prod_eq, nonempty_iff_ne_bot, ht, hs]

中文:
定理 direction_prod_eq
  结论: {s : AffineSubspace k P} {t : AffineSubspace k Q}
  证明: by
  simp [direction_eq_vectorSpan, vectorSpan_prod_eq, nonempty_iff_ne_bot, ht, hs]

Depends on / 依赖: direction_eq_vectorSpan, nonempty_iff_ne_bot, vectorSpan_prod_eq
-/
theorem direction_prod_eq {s : AffineSubspace k P} {t : AffineSubspace k Q}
    (hs : s != ⊥) (ht : t != ⊥) :
    (s.prod t).direction = s.direction.prod t.direction := by
  simp [direction_eq_vectorSpan, vectorSpan_prod_eq, nonempty_iff_ne_bot, ht, hs]

/--
theorem `_root_.affineSpan_prod_eq` / 定理 `_root_.affineSpan_prod_eq`

English:
theorem _root_.affineSpan_prod_eq
  given: (s : Set P) (t : Set Q)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  apply AffineSubspace.ext_of_direction_eq
  · simp [direction_prod_eq, Set.nonempty_iff_ne_empty.mp, hs, ht, direction_affineSpan,
      vectorSpan_prod_eq]
  · obtain ⟨x, hx⟩ := hs
    

中文:
定理 _root_.affineSpan_prod_eq
  条件: (s : Set P) (t : Set Q)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  apply AffineSubspace.ext_of_direction_eq
  · simp [direction_prod_eq, Set.nonempty_iff_ne_empty.mp, hs, ht, direction_affineSpan,
      vectorSpan_prod_eq]
  · obtain ⟨x, hx⟩ := hs
    

Depends on / 依赖: AffineSubspace, AffineSubspace.ext_of_direction_eq, Set.nonempty_iff_ne_empty.mp, direction_affineSpan, direction_prod_eq, eq_empty_or_nonempty, ext_of_direction_eq, mem_affineSpan, nonempty_iff_ne_empty, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty, vectorSpan_prod_eq
-/
theorem _root_.affineSpan_prod_eq (s : Set P) (t : Set Q) :
    affineSpan k (s ×ˢ t) = (affineSpan k s).prod (affineSpan k t) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  apply AffineSubspace.ext_of_direction_eq
  · simp [direction_prod_eq, Set.nonempty_iff_ne_empty.mp, hs, ht, direction_affineSpan,
      vectorSpan_prod_eq]
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    use ⟨x, y⟩
    simp [mem_affineSpan, hx, hy]

/-- Two affine subspaces are parallel if one is related to the other by adding the same vector
to all points. -/
@[wikidata Q53875]
/--
Definition of `Parallel` / `Parallel` 的定义

English:
definition Parallel
  signature: (s₁ s₂ : AffineSubspace k P)
  body: exists v : V, s₂ = s₁.map (constVAdd k P v)

@[inherit_doc]
scoped[Affine] infixl:50 " ∥ " => AffineSubspace.Parallel

@[symm]

中文:
定义 Parallel
  签名: (s₁ s₂ : AffineSubspace k P)
  定义体: exists v : V, s₂ = s₁.map (constVAdd k P v)

@[inherit_doc]
scoped[Affine] infixl:50 " ∥ " => AffineSubspace.Parallel

@[symm]

Depends on / 依赖: constVAdd
-/
def Parallel (s₁ s₂ : AffineSubspace k P) : Prop :=
  exists v : V, s₂ = s₁.map (constVAdd k P v)

@[inherit_doc]
scoped[Affine] infixl:50 " ∥ " => AffineSubspace.Parallel

@[symm]
/--
theorem `Parallel.symm` / 定理 `Parallel.symm`

English:
theorem Parallel.symm
  given: {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂)
  statement: s₂ ∥ s₁
  proof: by
  rcases h with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  rw [map_map]; rw [← coe_trans_to_affineMap]; rw [← constVAdd_add]; rw [neg_add_cancel]; rw [constVAdd_zero]; rw [coe_refl_to_affineMap]; rw [map_id]

中文:
定理 Parallel.symm
  条件: {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂)
  结论: s₂ ∥ s₁
  证明: by
  rcases h with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  rw [map_map]; rw [← coe_trans_to_affineMap]; rw [← constVAdd_add]; rw [neg_add_cancel]; rw [constVAdd_zero]; rw [coe_refl_to_affineMap]; rw [map_id]

Depends on / 依赖: coe_refl_to_affineMap, coe_trans_to_affineMap, constVAdd_add, constVAdd_zero, map_id, map_map, neg_add_cancel
-/
theorem Parallel.symm {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) : s₂ ∥ s₁ := by
  rcases h with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  rw [map_map]; rw [← coe_trans_to_affineMap]; rw [← constVAdd_add]; rw [neg_add_cancel]; rw [constVAdd_zero]; rw [coe_refl_to_affineMap]; rw [map_id]

/--
theorem `parallel_comm` / 定理 `parallel_comm`

English:
theorem parallel_comm
  given: {s₁ s₂ : AffineSubspace k P}
  statement: s₁ ∥ s₂ ↔ s₂ ∥ s₁
  proof: ⟨Parallel.symm, Parallel.symm⟩

@[refl]

中文:
定理 parallel_comm
  条件: {s₁ s₂ : AffineSubspace k P}
  结论: s₁ ∥ s₂ ↔ s₂ ∥ s₁
  证明: ⟨Parallel.symm, Parallel.symm⟩

@[refl]

Depends on / 依赖: Parallel, Parallel.symm
-/
theorem parallel_comm {s₁ s₂ : AffineSubspace k P} : s₁ ∥ s₂ ↔ s₂ ∥ s₁ :=
  ⟨Parallel.symm, Parallel.symm⟩

@[refl]
/--
theorem `Parallel.refl` / 定理 `Parallel.refl`

English:
theorem Parallel.refl
  given: (s : AffineSubspace k P)
  statement: s ∥ s
  proof: ⟨0, by simp⟩

@[trans]

中文:
定理 Parallel.refl
  条件: (s : AffineSubspace k P)
  结论: s ∥ s
  证明: ⟨0, by simp⟩

@[trans]
-/
theorem Parallel.refl (s : AffineSubspace k P) : s ∥ s :=
  ⟨0, by simp⟩

@[trans]
/--
theorem `Parallel.trans` / 定理 `Parallel.trans`

English:
theorem Parallel.trans
  given: {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃)
  proof: by
  rcases h₁₂ with ⟨v₁₂, rfl⟩
  rcases h₂₃ with ⟨v₂₃, rfl⟩
  refine ⟨v₂₃ + v₁₂, ?_⟩
  rw [map_map]; rw [← coe_trans_to_affineMap]; rw [← constVAdd_add]

中文:
定理 Parallel.trans
  条件: {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃)
  证明: by
  rcases h₁₂ with ⟨v₁₂, rfl⟩
  rcases h₂₃ with ⟨v₂₃, rfl⟩
  refine ⟨v₂₃ + v₁₂, ?_⟩
  rw [map_map]; rw [← coe_trans_to_affineMap]; rw [← constVAdd_add]

Depends on / 依赖: coe_trans_to_affineMap, constVAdd_add, map_map
-/
theorem Parallel.trans {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃) :
    s₁ ∥ s₃ := by
  rcases h₁₂ with ⟨v₁₂, rfl⟩
  rcases h₂₃ with ⟨v₂₃, rfl⟩
  refine ⟨v₂₃ + v₁₂, ?_⟩
  rw [map_map]; rw [← coe_trans_to_affineMap]; rw [← constVAdd_add]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Refl (α := AffineSubspace k P) Parallel
  body: .refl

中文:
实例 :
  签名: Std.Refl (α := AffineSubspace k P) Parallel
  定义体: .refl

Depends on / 依赖: AffineSubspace, Parallel
-/
instance : Std.Refl (α := AffineSubspace k P) Parallel where
  refl := .refl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (α := AffineSubspace k P) Parallel
  body: .symm

中文:
实例 :
  签名: Std.Symm (α := AffineSubspace k P) Parallel
  定义体: .symm

Depends on / 依赖: AffineSubspace, Parallel
-/
instance : Std.Symm (α := AffineSubspace k P) Parallel where
  symm _ _ := .symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans (AffineSubspace k P) Parallel
  body: .trans

中文:
实例 :
  签名: IsTrans (AffineSubspace k P) Parallel
  定义体: .trans
-/
instance : IsTrans (AffineSubspace k P) Parallel where
  trans _ _ _ := .trans

/--
theorem `Parallel.equivalence` / 定理 `Parallel.equivalence`

English:
theorem Parallel.equivalence
  statement: Equivalence (α := AffineSubspace k P) Parallel
  proof: ⟨.refl, .symm, .trans⟩

中文:
定理 Parallel.equivalence
  结论: Equivalence (α := AffineSubspace k P) Parallel
  证明: ⟨.refl, .symm, .trans⟩

Depends on / 依赖: AffineSubspace, Parallel
-/
theorem Parallel.equivalence : Equivalence (α := AffineSubspace k P) Parallel :=
  ⟨.refl, .symm, .trans⟩

/--
theorem `Parallel.direction_eq` / 定理 `Parallel.direction_eq`

English:
theorem Parallel.direction_eq
  given: {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂)
  proof: by
  rcases h with ⟨v, rfl⟩
  simp

@[simp]

中文:
定理 Parallel.direction_eq
  条件: {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂)
  证明: by
  rcases h with ⟨v, rfl⟩
  simp

@[simp]
-/
theorem Parallel.direction_eq {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) :
    s₁.direction = s₂.direction := by
  rcases h with ⟨v, rfl⟩
  simp

@[simp]
/--
theorem `parallel_bot_iff_eq_bot` / 定理 `parallel_bot_iff_eq_bot`

English:
theorem parallel_bot_iff_eq_bot
  given: {s : AffineSubspace k P}
  statement: s ∥ ⊥ ↔ s = ⊥
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ Parallel.refl _⟩
  rcases h with ⟨v, h⟩
  rwa [eq_comm, map_eq_bot_iff] at h

@[simp]

中文:
定理 parallel_bot_iff_eq_bot
  条件: {s : AffineSubspace k P}
  结论: s ∥ ⊥ ↔ s = ⊥
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ Parallel.refl _⟩
  rcases h with ⟨v, h⟩
  rwa [eq_comm, map_eq_bot_iff] at h

@[simp]

Depends on / 依赖: Parallel, Parallel.refl, eq_comm, map_eq_bot_iff
-/
theorem parallel_bot_iff_eq_bot {s : AffineSubspace k P} : s ∥ ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => h ▸ Parallel.refl _⟩
  rcases h with ⟨v, h⟩
  rwa [eq_comm, map_eq_bot_iff] at h

@[simp]
/--
theorem `bot_parallel_iff_eq_bot` / 定理 `bot_parallel_iff_eq_bot`

English:
theorem bot_parallel_iff_eq_bot
  given: {s : AffineSubspace k P}
  statement: ⊥ ∥ s ↔ s = ⊥
  proof: by
  rw [parallel_comm]; rw [parallel_bot_iff_eq_bot]

中文:
定理 bot_parallel_iff_eq_bot
  条件: {s : AffineSubspace k P}
  结论: ⊥ ∥ s ↔ s = ⊥
  证明: by
  rw [parallel_comm]; rw [parallel_bot_iff_eq_bot]

Depends on / 依赖: parallel_bot_iff_eq_bot, parallel_comm
-/
theorem bot_parallel_iff_eq_bot {s : AffineSubspace k P} : ⊥ ∥ s ↔ s = ⊥ := by
  rw [parallel_comm]; rw [parallel_bot_iff_eq_bot]

/--
theorem `parallel_iff_direction_eq_and_eq_bot_iff_eq_bot` / 定理 `parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`

English:
theorem parallel_iff_direction_eq_and_eq_bot_iff_eq_bot
  given: {s₁ s₂ : AffineSubspace k P}
  proof: by
  refine ⟨fun h => ⟨h.direction_eq, ?_, ?_⟩, fun h => ?_⟩
  · rintro rfl
    exact bot_parallel_iff_eq_bot.1 h
  · rintro rfl
    exact parallel_bot_iff_eq_bot.1 h
  · rcases h with ⟨hd, hb⟩
    by_cases hs₁ : s₁ = ⊥
    · rw [hs₁, bot_parallel_iff_eq_bot]
      exact hb.1 hs₁
    · have hs₂ : s₂

中文:
定理 parallel_iff_direction_eq_and_eq_bot_iff_eq_bot
  条件: {s₁ s₂ : AffineSubspace k P}
  证明: by
  refine ⟨fun h => ⟨h.direction_eq, ?_, ?_⟩, fun h => ?_⟩
  · rintro rfl
    exact bot_parallel_iff_eq_bot.1 h
  · rintro rfl
    exact parallel_bot_iff_eq_bot.1 h
  · rcases h with ⟨hd, hb⟩
    by_cases hs₁ : s₁ = ⊥
    · rw [hs₁, bot_parallel_iff_eq_bot]
      exact hb.1 hs₁
    · have hs₂ : s₂

Depends on / 依赖: bot_parallel_iff_eq_bot, direction_eq, eq_iff_direction_eq_of_mem, h.direction_eq, hb.not, mem_map, nonempty_iff_ne_bot, parallel_bot_iff_eq_bot
-/
theorem parallel_iff_direction_eq_and_eq_bot_iff_eq_bot {s₁ s₂ : AffineSubspace k P} :
    s₁ ∥ s₂ ↔ s₁.direction = s₂.direction ∧ (s₁ = ⊥ ↔ s₂ = ⊥) := by
  refine ⟨fun h => ⟨h.direction_eq, ?_, ?_⟩, fun h => ?_⟩
  · rintro rfl
    exact bot_parallel_iff_eq_bot.1 h
  · rintro rfl
    exact parallel_bot_iff_eq_bot.1 h
  · rcases h with ⟨hd, hb⟩
    by_cases hs₁ : s₁ = ⊥
    · rw [hs₁, bot_parallel_iff_eq_bot]
      exact hb.1 hs₁
    · have hs₂ : s₂ != ⊥ := hb.not.1 hs₁
      rcases (nonempty_iff_ne_bot s₁).2 hs₁ with ⟨p₁, hp₁⟩
      rcases (nonempty_iff_ne_bot s₂).2 hs₂ with ⟨p₂, hp₂⟩
      refine ⟨p₂ -ᵥ p₁, (eq_iff_direction_eq_of_mem hp₂ ?_).2 ?_⟩
      · rw [mem_map]
        refine ⟨p₁, hp₁, ?_⟩
        simp
      · simpa using hd.symm

/--
theorem `Parallel.vectorSpan_eq` / 定理 `Parallel.vectorSpan_eq`

English:
theorem Parallel.vectorSpan_eq
  given: {s₁ s₂ : Set P} (h : affineSpan k s₁ ∥ affineSpan k s₂)
  proof: by
  simp_rw [← direction_affineSpan]
  exact h.direction_eq

中文:
定理 Parallel.vectorSpan_eq
  条件: {s₁ s₂ : Set P} (h : affineSpan k s₁ ∥ affineSpan k s₂)
  证明: by
  simp_rw [← direction_affineSpan]
  exact h.direction_eq

Depends on / 依赖: direction_affineSpan, direction_eq, h.direction_eq, simp_rw
-/
theorem Parallel.vectorSpan_eq {s₁ s₂ : Set P} (h : affineSpan k s₁ ∥ affineSpan k s₂) :
    vectorSpan k s₁ = vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan]
  exact h.direction_eq

/--
theorem `affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty` / 定理 `affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty`

English:
theorem affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty
  given: {s₁ s₂ : Set P}
  proof: by
  repeat rw [← direction_affineSpan, ← affineSpan_eq_bot k]
  exact parallel_iff_direction_eq_and_eq_bot_iff_eq_bot

中文:
定理 affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty
  条件: {s₁ s₂ : Set P}
  证明: by
  repeat rw [← direction_affineSpan, ← affineSpan_eq_bot k]
  exact parallel_iff_direction_eq_and_eq_bot_iff_eq_bot

Depends on / 依赖: affineSpan_eq_bot, direction_affineSpan, parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, repeat
-/
theorem affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty {s₁ s₂ : Set P} :
    affineSpan k s₁ ∥ affineSpan k s₂ ↔ vectorSpan k s₁ = vectorSpan k s₂ ∧ (s₁ = ∅ ↔ s₂ = ∅) := by
  repeat rw [← direction_affineSpan, ← affineSpan_eq_bot k]
  exact parallel_iff_direction_eq_and_eq_bot_iff_eq_bot

/--
theorem `affineSpan_pair_parallel_iff_vectorSpan_eq` / 定理 `affineSpan_pair_parallel_iff_vectorSpan_eq`

English:
theorem affineSpan_pair_parallel_iff_vectorSpan_eq
  given: {p₁ p₂ p₃ p₄ : P}
  proof: by
  simp [affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty, ←
    not_nonempty_iff_eq_empty]

中文:
定理 affineSpan_pair_parallel_iff_vectorSpan_eq
  条件: {p₁ p₂ p₃ p₄ : P}
  证明: by
  simp [affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty, ←
    not_nonempty_iff_eq_empty]

Depends on / 依赖: affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty, not_nonempty_iff_eq_empty
-/
theorem affineSpan_pair_parallel_iff_vectorSpan_eq {p₁ p₂ p₃ p₄ : P} :
    line[k, p₁, p₂] ∥ line[k, p₃, p₄] ↔
      vectorSpan k ({p₁, p₂} : Set P) = vectorSpan k ({p₃, p₄} : Set P) := by
  simp [affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty, ←
    not_nonempty_iff_eq_empty]

/--
lemma `affineSpan_pair_parallel_iff_exists_unit_smul'` / 引理 `affineSpan_pair_parallel_iff_exists_unit_smul'`

English:
lemma affineSpan_pair_parallel_iff_exists_unit_smul'
  statement: [IsDomain k] [Module.IsTorsionFree k V]
  proof: by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq]; rw [vectorSpan_pair_rev]; rw [vectorSpan_pair_rev]; rw [Submodule.span_singleton_eq_span_singleton]

中文:
引理 affineSpan_pair_parallel_iff_exists_unit_smul'
  结论: [IsDomain k] [Module.IsTorsionFree k V]
  证明: by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq]; rw [vectorSpan_pair_rev]; rw [vectorSpan_pair_rev]; rw [Submodule.span_singleton_eq_span_singleton]

Depends on / 依赖: AffineSubspace, AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, Submodule, Submodule.span_singleton_eq_span_singleton, affineSpan_pair_parallel_iff_vectorSpan_eq, span_singleton_eq_span_singleton, vectorSpan_pair_rev
-/
lemma affineSpan_pair_parallel_iff_exists_unit_smul' [IsDomain k] [Module.IsTorsionFree k V]
    {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ exists z : kˣ, z • (q₁ -ᵥ p₁) = q₂ -ᵥ p₂ := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq]; rw [vectorSpan_pair_rev]; rw [vectorSpan_pair_rev]; rw [Submodule.span_singleton_eq_span_singleton]

/--
lemma `affineSpan_pair_parallel_iff_exists_unit_smul` / 引理 `affineSpan_pair_parallel_iff_exists_unit_smul`

English:
lemma affineSpan_pair_parallel_iff_exists_unit_smul
  statement: [IsDomain k] [Module.IsTorsionFree k V]
  proof: by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul']
  exact ⟨fun ⟨z, hz⟩ => ⟨z⁻¹, by simp [← hz]⟩, fun ⟨z, hz⟩ => ⟨z⁻¹, by simp [← hz]⟩⟩

中文:
引理 affineSpan_pair_parallel_iff_exists_unit_smul
  结论: [IsDomain k] [Module.IsTorsionFree k V]
  证明: by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul']
  exact ⟨fun ⟨z, hz⟩ => ⟨z⁻¹, by simp [← hz]⟩, fun ⟨z, hz⟩ => ⟨z⁻¹, by simp [← hz]⟩⟩

Depends on / 依赖: affineSpan_pair_parallel_iff_exists_unit_smul
-/
lemma affineSpan_pair_parallel_iff_exists_unit_smul [IsDomain k] [Module.IsTorsionFree k V]
    {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ exists z : kˣ, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul']
  exact ⟨fun ⟨z, hz⟩ => ⟨z⁻¹, by simp [← hz]⟩, fun ⟨z, hz⟩ => ⟨z⁻¹, by simp [← hz]⟩⟩

/--
lemma `direction_affineSpan_pair_le_iff_exists_smul` / 引理 `direction_affineSpan_pair_le_iff_exists_smul`

English:
lemma direction_affineSpan_pair_le_iff_exists_smul
  given: {p₁ q₁ p₂ q₂ : P}
  proof: by
  rw [direction_affineSpan]; rw [direction_affineSpan]; rw [vectorSpan_pair_rev]; rw [vectorSpan_pair_rev]; rw [Submodule.span_singleton_le_iff_mem]; rw [Submodule.mem_span_singleton]

中文:
引理 direction_affineSpan_pair_le_iff_exists_smul
  条件: {p₁ q₁ p₂ q₂ : P}
  证明: by
  rw [direction_affineSpan]; rw [direction_affineSpan]; rw [vectorSpan_pair_rev]; rw [vectorSpan_pair_rev]; rw [Submodule.span_singleton_le_iff_mem]; rw [Submodule.mem_span_singleton]

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, Submodule.span_singleton_le_iff_mem, direction_affineSpan, mem_span_singleton, span_singleton_le_iff_mem, vectorSpan_pair_rev
-/
lemma direction_affineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁].direction <= line[k, p₂, q₂].direction ↔ exists z : k, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  rw [direction_affineSpan]; rw [direction_affineSpan]; rw [vectorSpan_pair_rev]; rw [vectorSpan_pair_rev]; rw [Submodule.span_singleton_le_iff_mem]; rw [Submodule.mem_span_singleton]

/--
theorem `affineSpan_pair_comm` / 定理 `affineSpan_pair_comm`

English:
theorem affineSpan_pair_comm
  given: {p₁ p₂ : P}
  proof: by
  rw [Set.pair_comm]

中文:
定理 affineSpan_pair_comm
  条件: {p₁ p₂ : P}
  证明: by
  rw [Set.pair_comm]

Depends on / 依赖: Set.pair_comm, pair_comm
-/
theorem affineSpan_pair_comm {p₁ p₂ : P} :
    line[k, p₁, p₂] = line[k, p₂, p₁] := by
  rw [Set.pair_comm]

end AffineSubspace

section DivisionRing

open AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/--
lemma `affineSpan_pair_eq_of_mem_of_mem_of_ne` / 引理 `affineSpan_pair_eq_of_mem_of_mem_of_ne`

English:
lemma affineSpan_pair_eq_of_mem_of_mem_of_ne
  statement: {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in line[k, p₃, p₄])
  proof: by
  refine le_antisymm (affineSpan_pair_le_of_mem_of_mem hp₁ hp₂) ?_
  rw [← vsub_vadd p₁ p₃]; rw [vadd_left_mem_affineSpan_pair] at hp₁
  rcases hp₁ with ⟨r₁, hp₁⟩
  rw [← vsub_vadd p₂ p₃]; rw [vadd_left_mem_affineSpan_pair] at hp₂
  rcases hp₂ with ⟨r₂, hp₂⟩
  have hr₀ : r₂ - r₁ != 0 := by
    rw

中文:
引理 affineSpan_pair_eq_of_mem_of_mem_of_ne
  结论: {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in line[k, p₃, p₄])
  证明: by
  refine le_antisymm (affineSpan_pair_le_of_mem_of_mem hp₁ hp₂) ?_
  rw [← vsub_vadd p₁ p₃]; rw [vadd_left_mem_affineSpan_pair] at hp₁
  rcases hp₁ with ⟨r₁, hp₁⟩
  rw [← vsub_vadd p₂ p₃]; rw [vadd_left_mem_affineSpan_pair] at hp₂
  rcases hp₂ with ⟨r₂, hp₂⟩
  have hr₀ : r₂ - r₁ != 0 := by
    rw

Depends on / 依赖: affineSpan_pair_le_of_mem_of_mem, convert, le_antisymm, smul_vsub_vadd, sub_ne_zero, sub_smul, vadd_left_mem_affineSpan_pair, vsub_vadd
-/
lemma affineSpan_pair_eq_of_mem_of_mem_of_ne {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in line[k, p₃, p₄])
    (hp₂ : p₂ in line[k, p₃, p₄]) (hp₁₂ : p₁ != p₂) : line[k, p₁, p₂] = line[k, p₃, p₄] := by
  refine le_antisymm (affineSpan_pair_le_of_mem_of_mem hp₁ hp₂) ?_
  rw [← vsub_vadd p₁ p₃]; rw [vadd_left_mem_affineSpan_pair] at hp₁
  rcases hp₁ with ⟨r₁, hp₁⟩
  rw [← vsub_vadd p₂ p₃]; rw [vadd_left_mem_affineSpan_pair] at hp₂
  rcases hp₂ with ⟨r₂, hp₂⟩
  have hr₀ : r₂ - r₁ != 0 := by
    rw [sub_ne_zero]
    rintro rfl
    simp_all
  have hr : (r₂ - r₁) • (p₄ -ᵥ p₃) = p₂ -ᵥ p₁ := by
    simp [sub_smul, hp₁, hp₂]
  rw [← eq_inv_smul_iff₀ hr₀] at hr
  refine affineSpan_pair_le_of_mem_of_mem ?_ ?_
  · convert! smul_vsub_vadd_mem_affineSpan_pair (-r₁ * (r₂ - r₁)⁻¹) p₁ p₂
    simp [mul_smul, ← hr, hp₁]
  · convert! smul_vsub_vadd_mem_affineSpan_pair ((1 - r₁) * (r₂ - r₁)⁻¹) p₁ p₂
    simp [mul_smul, ← hr, sub_smul, hp₁]

/--
lemma `affineSpan_pair_eq_of_left_mem_of_ne` / 引理 `affineSpan_pair_eq_of_left_mem_of_ne`

English:
lemma affineSpan_pair_eq_of_left_mem_of_ne
  statement: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  proof: affineSpan_pair_eq_of_mem_of_mem_of_ne h (right_mem_affineSpan_pair _ _ _) hne

中文:
引理 affineSpan_pair_eq_of_left_mem_of_ne
  结论: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  证明: affineSpan_pair_eq_of_mem_of_mem_of_ne h (right_mem_affineSpan_pair _ _ _) hne

Depends on / 依赖: affineSpan_pair_eq_of_mem_of_mem_of_ne, right_mem_affineSpan_pair
-/
lemma affineSpan_pair_eq_of_left_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
    (hne : p₁ != p₃) : line[k, p₁, p₃] = line[k, p₂, p₃] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne h (right_mem_affineSpan_pair _ _ _) hne

/--
lemma `affineSpan_pair_eq_of_right_mem_of_ne` / 引理 `affineSpan_pair_eq_of_right_mem_of_ne`

English:
lemma affineSpan_pair_eq_of_right_mem_of_ne
  statement: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  proof: affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) h hne.symm

中文:
引理 affineSpan_pair_eq_of_right_mem_of_ne
  结论: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  证明: affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) h hne.symm

Depends on / 依赖: affineSpan_pair_eq_of_mem_of_mem_of_ne, hne.symm, left_mem_affineSpan_pair
-/
lemma affineSpan_pair_eq_of_right_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
    (hne : p₁ != p₂) :
    line[k, p₂, p₁] = line[k, p₂, p₃] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) h hne.symm

/--
theorem `exists_eq_smul_of_parallel` / 定理 `exists_eq_smul_of_parallel`

English:
theorem exists_eq_smul_of_parallel
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[k, p₁, p₃])
  proof: by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul'] at h₁₂₄₅
  rw [direction_affineSpan_pair_le_iff_exists_smul] at h₂₃₅₆ h₃₁₆₄
  obtain ⟨r₁, hr₁⟩ := h₁₂₄₅
  obtain ⟨r₂, hr₂⟩ := h₂₃₅₆
  obtain ⟨r₃, hr₃⟩ := h₃₁₆₄
  rw [Units.smul_def] at hr₁
  by_cases h : (r₁ : k) = r₂
  · refine ⟨r₁, r₁.ne_zer

中文:
定理 exists_eq_smul_of_parallel
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[k, p₁, p₃])
  证明: by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul'] at h₁₂₄₅
  rw [direction_affineSpan_pair_le_iff_exists_smul] at h₂₃₅₆ h₃₁₆₄
  obtain ⟨r₁, hr₁⟩ := h₁₂₄₅
  obtain ⟨r₂, hr₂⟩ := h₂₃₅₆
  obtain ⟨r₃, hr₃⟩ := h₃₁₆₄
  rw [Units.smul_def] at hr₁
  by_cases h : (r₁ : k) = r₂
  · refine ⟨r₁, r₁.ne_zer

Depends on / 依赖: Units.smul_def, affineSpan_pair_parallel_iff_exists_unit_smul, direction_affineSpan_pair_le_iff_exists_smul, ne_zero, neg_inj, neg_vsub_eq_vsub_rev, smul_add, smul_def, smul_neg, vsub_add_vsub_cancel
-/
theorem exists_eq_smul_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[k, p₁, p₃])
    (h₁₂₄₅ : line[k, p₁, p₂] ∥ line[k, p₄, p₅])
    (h₂₃₅₆ : line[k, p₅, p₆].direction <= line[k, p₂, p₃].direction)
    (h₃₁₆₄ : line[k, p₆, p₄].direction <= line[k, p₃, p₁].direction) :
    exists r : k, r != 0 ∧ p₅ -ᵥ p₄ = r • (p₂ -ᵥ p₁) ∧ p₆ -ᵥ p₅ = r • (p₃ -ᵥ p₂) ∧
      p₄ -ᵥ p₆ = r • (p₁ -ᵥ p₃) := by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul'] at h₁₂₄₅
  rw [direction_affineSpan_pair_le_iff_exists_smul] at h₂₃₅₆ h₃₁₆₄
  obtain ⟨r₁, hr₁⟩ := h₁₂₄₅
  obtain ⟨r₂, hr₂⟩ := h₂₃₅₆
  obtain ⟨r₃, hr₃⟩ := h₃₁₆₄
  rw [Units.smul_def] at hr₁
  by_cases h : (r₁ : k) = r₂
  · refine ⟨r₁, r₁.ne_zero, hr₁.symm, h ▸ hr₂.symm, ?_⟩
    rw [← neg_inj]; rw [neg_vsub_eq_vsub_rev]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [← vsub_add_vsub_cancel p₆ p₅ p₄]; rw [← vsub_add_vsub_cancel p₃ p₂ p₁]; rw [smul_add]; rw [hr₁]; rw [h]; rw [hr₂]
  · exfalso
    have h₁₂ : (r₁ : k) • (p₂ -ᵥ p₁) + r₂ • (p₃ -ᵥ p₂) in vectorSpan k {p₁, p₃} := by
      rw [hr₁]; rw [hr₂]; rw [add_comm]; rw [vsub_add_vsub_cancel]; rw [← neg_vsub_eq_vsub_rev]; rw [neg_mem_iff]; rw [← hr₃]
      exact smul_vsub_mem_vectorSpan_pair _ _ _
    have h₁₁ : (r₁ : k) • (p₂ -ᵥ p₁) + (r₁ : k) • (p₃ -ᵥ p₂) in vectorSpan k {p₁, p₃} := by
      rw [add_comm]; rw [← smul_add]; rw [vsub_add_vsub_cancel]
      exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have h₂₁ : (r₂ - r₁) • (p₃ -ᵥ p₂) in vectorSpan k {p₁, p₃} := by
      simpa [sub_smul] using sub_mem h₁₂ h₁₁
    rw [Submodule.smul_mem_iff _ (by rwa [sub_ne_zero]; rw [ne_comm]), ← direction_affineSpan,
      vsub_left_mem_direction_iff_mem (right_mem_affineSpan_pair _ _ _)] at h₂₁
    exact h₂ h₂₁

end DivisionRing
