/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!

# Relative rank of subfields and intermediate fields

This file contains basics about the relative rank of subfields and intermediate fields.

## Main definitions

- `Subfield.relrank A B`, `IntermediateField.relrank A B`:
  defined to be `[B : A ⊓ B]` as a `Cardinal`.
  In particular, when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
  This is similar to `Subgroup.relIndex` but it is `Cardinal` valued.

- `Subfield.relfinrank A B`, `IntermediateField.relfinrank A B`:
  the `Nat` version of `Subfield.relrank A B` and `IntermediateField.relrank A B`, respectively.
  If `B / A ⊓ B` is an infinite extension, then it is zero.
  This is similar to `Subgroup.relIndex`.

-/

@[expose] public section

open Module Cardinal

universe u v w

namespace Subfield

variable {E : Type v} [Field E] {L : Type w} [Field L]

variable (A B C : Subfield E)

/--
Definition of `relrank` / `relrank` 的定义

English:
definition relrank
  body: Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B <= B))

中文:
定义 relrank
  定义体: Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B <= B))

Depends on / 依赖: Module, Module.rank, extendScalars, inf_le_right
-/
noncomputable def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B <= B))

/--
Definition of `relfinrank` / `relfinrank` 的定义

English:
definition relfinrank
  body: finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B <= B))

中文:
定义 relfinrank
  定义体: finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B <= B))

Depends on / 依赖: extendScalars, finrank, inf_le_right
-/
noncomputable def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B <= B))

/--
theorem `relfinrank_eq_toNat_relrank` / 定理 `relfinrank_eq_toNat_relrank`

English:
theorem relfinrank_eq_toNat_relrank
  statement: relfinrank A B = toNat (relrank A B)
  proof: rfl

中文:
定理 relfinrank_eq_to自然数_relrank
  结论: relfinrank A B = to自然数 (relrank A B)
  证明: rfl
-/
theorem relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B) := rfl

variable {A B C}

/--
theorem `relrank_eq_of_inf_eq` / 定理 `relrank_eq_of_inf_eq`

English:
theorem relrank_eq_of_inf_eq
  given: (h : A ⊓ C = B ⊓ C)
  statement: relrank A C = relrank B C
  proof: by
  simp_rw [relrank]
  congr!

中文:
定理 relrank_eq_of_inf_eq
  条件: (h : A ⊓ C = B ⊓ C)
  结论: relrank A C = relrank B C
  证明: by
  simp_rw [relrank]
  congr!

Depends on / 依赖: relrank, simp_rw
-/
theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C := by
  simp_rw [relrank]
  congr!

/--
theorem `relfinrank_eq_of_inf_eq` / 定理 `relfinrank_eq_of_inf_eq`

English:
theorem relfinrank_eq_of_inf_eq
  given: (h : A ⊓ C = B ⊓ C)
  statement: relfinrank A C = relfinrank B C
  proof: congr(toNat $(relrank_eq_of_inf_eq h))

中文:
定理 relfinrank_eq_of_inf_eq
  条件: (h : A ⊓ C = B ⊓ C)
  结论: relfinrank A C = relfinrank B C
  证明: congr(toNat $(relrank_eq_of_inf_eq h))

Depends on / 依赖: relrank_eq_of_inf_eq
-/
theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

/--
theorem `relrank_eq_rank_of_le` / 定理 `relrank_eq_rank_of_le`

English:
theorem relrank_eq_rank_of_le
  given: (h : A <= B)
  statement: relrank A B = Module.rank A (extendScalars h)
  proof: by
  rw [relrank]
  have := inf_of_le_left h
  congr!

中文:
定理 relrank_eq_rank_of_le
  条件: (h : A <= B)
  结论: relrank A B = 模.rank A (extendScalars h)
  证明: by
  rw [relrank]
  have := inf_of_le_left h
  congr!

Depends on / 依赖: inf_of_le_left, relrank
-/
theorem relrank_eq_rank_of_le (h : A <= B) : relrank A B = Module.rank A (extendScalars h) := by
  rw [relrank]
  have := inf_of_le_left h
  congr!

/--
theorem `relfinrank_eq_finrank_of_le` / 定理 `relfinrank_eq_finrank_of_le`

English:
theorem relfinrank_eq_finrank_of_le
  given: (h : A <= B)
  statement: relfinrank A B = finrank A (extendScalars h)
  proof: congr(toNat $(relrank_eq_rank_of_le h))

中文:
定理 relfinrank_eq_finrank_of_le
  条件: (h : A <= B)
  结论: relfinrank A B = finrank A (extendScalars h)
  证明: congr(toNat $(relrank_eq_rank_of_le h))

Depends on / 依赖: relrank_eq_rank_of_le
-/
theorem relfinrank_eq_finrank_of_le (h : A <= B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)

/--
theorem `inf_relrank_right` / 定理 `inf_relrank_right`

English:
theorem inf_relrank_right
  statement: relrank (A ⊓ B) B = relrank A B
  proof: relrank_eq_rank_of_le (inf_le_right : A ⊓ B <= B)

中文:
定理 inf_relrank_right
  结论: relrank (A ⊓ B) B = relrank A B
  证明: relrank_eq_rank_of_le (inf_le_right : A ⊓ B <= B)

Depends on / 依赖: inf_le_right, relrank_eq_rank_of_le
-/
theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B <= B)

/--
theorem `inf_relfinrank_right` / 定理 `inf_relfinrank_right`

English:
theorem inf_relfinrank_right
  statement: relfinrank (A ⊓ B) B = relfinrank A B
  proof: congr(toNat $(inf_relrank_right A B))

中文:
定理 inf_relfinrank_right
  结论: relfinrank (A ⊓ B) B = relfinrank A B
  证明: congr(toNat $(inf_relrank_right A B))

Depends on / 依赖: inf_relrank_right
-/
theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))

/--
theorem `inf_relrank_left` / 定理 `inf_relrank_left`

English:
theorem inf_relrank_left
  statement: relrank (A ⊓ B) A = relrank B A
  proof: by
  rw [inf_comm]; rw [inf_relrank_right]

中文:
定理 inf_relrank_left
  结论: relrank (A ⊓ B) A = relrank B A
  证明: by
  rw [inf_comm]; rw [inf_relrank_right]

Depends on / 依赖: inf_comm, inf_relrank_right
-/
theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm]; rw [inf_relrank_right]

/--
theorem `inf_relfinrank_left` / 定理 `inf_relfinrank_left`

English:
theorem inf_relfinrank_left
  statement: relfinrank (A ⊓ B) A = relfinrank B A
  proof: congr(toNat $(inf_relrank_left A B))

@[simp]

中文:
定理 inf_relfinrank_left
  结论: relfinrank (A ⊓ B) A = relfinrank B A
  证明: congr(toNat $(inf_relrank_left A B))

@[simp]

Depends on / 依赖: inf_relrank_left
-/
theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

@[simp]
/--
theorem `relrank_self` / 定理 `relrank_self`

English:
theorem relrank_self
  statement: relrank A A = 1
  proof: by
  rw [relrank_eq_rank_of_le (le_refl A)]; rw [extendScalars_self]; rw [IntermediateField.rank_bot]

@[simp]

中文:
定理 relrank_self
  结论: relrank A A = 1
  证明: by
  rw [relrank_eq_rank_of_le (le_refl A)]; rw [extendScalars_self]; rw [IntermediateField.rank_bot]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.rank_bot, extendScalars_self, le_refl, rank_bot, relrank_eq_rank_of_le
-/
theorem relrank_self : relrank A A = 1 := by
  rw [relrank_eq_rank_of_le (le_refl A)]; rw [extendScalars_self]; rw [IntermediateField.rank_bot]

@[simp]
/--
theorem `relfinrank_self` / 定理 `relfinrank_self`

English:
theorem relfinrank_self
  statement: relfinrank A A = 1
  proof: by
  simp [relfinrank_eq_toNat_relrank]

中文:
定理 relfinrank_self
  结论: relfinrank A A = 1
  证明: by
  simp [relfinrank_eq_toNat_relrank]

Depends on / 依赖: relfinrank_eq_toNat_relrank
-/
theorem relfinrank_self : relfinrank A A = 1 := by
  simp [relfinrank_eq_toNat_relrank]

variable {A B}

/--
theorem `relrank_eq_one_iff` / 定理 `relrank_eq_one_iff`

English:
theorem relrank_eq_one_iff
  statement: relrank A B = 1 ↔ B <= A
  proof: by
  rw [relrank]; rw [IntermediateField.rank_eq_one_iff]; rw [← IntermediateField.toSubfield_inj]; rw [extendScalars_toSubfield]; rw [IntermediateField.bot_toSubfield]; rw [algebraMap_ofSubfield]; rw [fieldRange_subtype]; rw [right_eq_inf]

中文:
定理 relrank_eq_one_iff
  结论: relrank A B = 1 ↔ B <= A
  证明: by
  rw [relrank]; rw [IntermediateField.rank_eq_one_iff]; rw [← IntermediateField.toSubfield_inj]; rw [extendScalars_toSubfield]; rw [IntermediateField.bot_toSubfield]; rw [algebraMap_ofSubfield]; rw [fieldRange_subtype]; rw [right_eq_inf]

Depends on / 依赖: IntermediateField, IntermediateField.bot_toSubfield, IntermediateField.rank_eq_one_iff, IntermediateField.toSubfield_inj, algebraMap_ofSubfield, bot_toSubfield, extendScalars_toSubfield, fieldRange_subtype, rank_eq_one_iff, relrank, right_eq_inf, toSubfield_inj
-/
theorem relrank_eq_one_iff : relrank A B = 1 ↔ B <= A := by
  rw [relrank]; rw [IntermediateField.rank_eq_one_iff]; rw [← IntermediateField.toSubfield_inj]; rw [extendScalars_toSubfield]; rw [IntermediateField.bot_toSubfield]; rw [algebraMap_ofSubfield]; rw [fieldRange_subtype]; rw [right_eq_inf]

/--
theorem `relfinrank_eq_one_iff` / 定理 `relfinrank_eq_one_iff`

English:
theorem relfinrank_eq_one_iff
  statement: relfinrank A B = 1 ↔ B <= A
  proof: by
  rw [relfinrank_eq_toNat_relrank]; rw [toNat_eq_one]; rw [relrank_eq_one_iff]

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

中文:
定理 relfinrank_eq_one_iff
  结论: relfinrank A B = 1 ↔ B <= A
  证明: by
  rw [relfinrank_eq_toNat_relrank]; rw [toNat_eq_one]; rw [relrank_eq_one_iff]

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

Depends on / 依赖: relfinrank_eq_toNat_relrank, relrank_eq_one_iff, toNat_eq_one
-/
theorem relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B <= A := by
  rw [relfinrank_eq_toNat_relrank]; rw [toNat_eq_one]; rw [relrank_eq_one_iff]

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

/--
theorem `relrank_mul_rank_top` / 定理 `relrank_mul_rank_top`

English:
theorem relrank_mul_rank_top
  given: (h : A <= B)
  statement: relrank A B * Module.rank B E = Module.rank A E
  proof: by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  have : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E

中文:
定理 relrank_mul_rank_top
  条件: (h : A <= B)
  结论: relrank A B * 模.rank B E = 模.rank A E
  证明: by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  have : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E

Depends on / 依赖: Algebra, IsScalarTower, IsScalarTower.of_algebraMap_eq, inclusion, of_algebraMap_eq, rank_mul_rank, relrank_eq_rank_of_le, toAlgebra
-/
theorem relrank_mul_rank_top (h : A <= B) : relrank A B * Module.rank B E = Module.rank A E := by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  have : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E

/--
theorem `relfinrank_mul_finrank_top` / 定理 `relfinrank_mul_finrank_top`

English:
theorem relfinrank_mul_finrank_top
  given: (h : A <= B)
  statement: relfinrank A B * finrank B E = finrank A E
  proof: by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

中文:
定理 relfinrank_mul_finrank_top
  条件: (h : A <= B)
  结论: relfinrank A B * finrank B E = finrank A E
  证明: by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

Depends on / 依赖: relrank_mul_rank_top
-/
theorem relfinrank_mul_finrank_top (h : A <= B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

variable (A B)

@[simp]
/--
theorem `relrank_top_left` / 定理 `relrank_top_left`

English:
theorem relrank_top_left
  statement: relrank ⊤ A = 1
  proof: relrank_eq_one_of_le le_top

@[simp]

中文:
定理 relrank_top_left
  结论: relrank ⊤ A = 1
  证明: relrank_eq_one_of_le le_top

@[simp]

Depends on / 依赖: le_top, relrank_eq_one_of_le
-/
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
/--
theorem `relfinrank_top_left` / 定理 `relfinrank_top_left`

English:
theorem relfinrank_top_left
  statement: relfinrank ⊤ A = 1
  proof: relfinrank_eq_one_of_le le_top

@[simp]

中文:
定理 relfinrank_top_left
  结论: relfinrank ⊤ A = 1
  证明: relfinrank_eq_one_of_le le_top

@[simp]

Depends on / 依赖: le_top, relfinrank_eq_one_of_le
-/
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := relfinrank_eq_one_of_le le_top

@[simp]
/--
theorem `relrank_top_right` / 定理 `relrank_top_right`

English:
theorem relrank_top_right
  statement: relrank A ⊤ = Module.rank A E
  proof: by
  rw [relrank_eq_rank_of_le (show A <= ⊤ from le_top)]; rw [extendScalars_top]; rw [IntermediateField.topEquiv.toLinearEquiv.rank_eq]

@[simp]

中文:
定理 relrank_top_right
  结论: relrank A ⊤ = 模.rank A E
  证明: by
  rw [relrank_eq_rank_of_le (show A <= ⊤ from le_top)]; rw [extendScalars_top]; rw [IntermediateField.topEquiv.toLinearEquiv.rank_eq]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.topEquiv.toLinearEquiv.rank_eq, extendScalars_top, le_top, rank_eq, relrank_eq_rank_of_le, toLinearEquiv, topEquiv
-/
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [relrank_eq_rank_of_le (show A <= ⊤ from le_top)]; rw [extendScalars_top]; rw [IntermediateField.topEquiv.toLinearEquiv.rank_eq]

@[simp]
/--
theorem `relfinrank_top_right` / 定理 `relfinrank_top_right`

English:
theorem relfinrank_top_right
  statement: relfinrank A ⊤ = finrank A E
  proof: by
  simp [relfinrank_eq_toNat_relrank, finrank]

中文:
定理 relfinrank_top_right
  结论: relfinrank A ⊤ = finrank A E
  证明: by
  simp [relfinrank_eq_toNat_relrank, finrank]

Depends on / 依赖: finrank, relfinrank_eq_toNat_relrank
-/
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_eq_toNat_relrank, finrank]

/--
theorem `lift_relrank_map_map` / 定理 `lift_relrank_map_map`

English:
theorem lift_relrank_map_map
  given: (f : E ->+* L)
  proof: -- typeclass inference is slow
.symm Algebra.lift_rank_eq_of_equiv_equiv (((A ⊓ B).equivMapOfInjective f f.injective).trans
 .subringCongr by rw [← map_inf]; rfl) (B.equivMapOfInjective f f.injective) rfl

中文:
定理 lift_relrank_map_map
  条件: (f : E ->+* L)
  证明: -- typeclass inference is slow
.symm Algebra.lift_rank_eq_of_equiv_equiv (((A ⊓ B).equivMapOfInjective f f.injective).trans
 .subringCongr by rw [← map_inf]; rfl) (B.equivMapOfInjective f f.injective) rfl
-/
theorem lift_relrank_map_map (f : E ->+* L) :
    lift.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B) :=
  -- typeclass inference is slow
.symm Algebra.lift_rank_eq_of_equiv_equiv (((A ⊓ B).equivMapOfInjective f f.injective).trans
 .subringCongr by rw [← map_inf]; rfl) (B.equivMapOfInjective f f.injective) rfl

/--
theorem `relrank_map_map` / 定理 `relrank_map_map`

English:
theorem relrank_map_map
  given: {L : Type v} [Field L] (f : E ->+* L)
  proof: by
  simpa only [lift_id] using lift_relrank_map_map A B f

中文:
定理 relrank_map_map
  条件: {L : 类型v} [域 L] (f : E ->+* L)
  证明: by
  simpa only [lift_id] using lift_relrank_map_map A B f

Depends on / 依赖: lift_id, lift_relrank_map_map
-/
theorem relrank_map_map {L : Type v} [Field L] (f : E ->+* L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_map_map A B f

/--
theorem `lift_relrank_comap` / 定理 `lift_relrank_comap`

English:
theorem lift_relrank_comap
  given: (f : L ->+* E) (B : Subfield L)
  proof: (lift_relrank_map_map _ _ f).symm.trans congr_arg lift relrank_eq_of_inf_eq by
    rw [map_comap_eq]; rw [f.fieldRange_eq_map]; rw [inf_assoc]; rw [← map_inf]; rw [top_inf_eq]

中文:
定理 lift_relrank_comap
  条件: (f : L ->+* E) (B : 子域 L)
  证明: (lift_relrank_map_map _ _ f).symm.trans congr_arg lift relrank_eq_of_inf_eq by
    rw [map_comap_eq]; rw [f.fieldRange_eq_map]; rw [inf_assoc]; rw [← map_inf]; rw [top_inf_eq]

Depends on / 依赖: congr_arg, f.fieldRange_eq_map, fieldRange_eq_map, inf_assoc, lift_relrank_map_map, map_comap_eq, map_inf, relrank_eq_of_inf_eq, symm.trans, top_inf_eq
-/
theorem lift_relrank_comap (f : L ->+* E) (B : Subfield L) :
    lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f)) :=
(lift_relrank_map_map _ _ f).symm.trans congr_arg lift relrank_eq_of_inf_eq by
    rw [map_comap_eq]; rw [f.fieldRange_eq_map]; rw [inf_assoc]; rw [← map_inf]; rw [top_inf_eq]

/--
theorem `relrank_comap` / 定理 `relrank_comap`

English:
theorem relrank_comap
  statement: {L : Type v} [Field L] (f : L ->+* E)
  proof: by
  simpa only [lift_id] using A.lift_relrank_comap f B

中文:
定理 relrank_comap
  结论: {L : 类型v} [域 L] (f : L ->+* E)
  证明: by
  simpa only [lift_id] using A.lift_relrank_comap f B

Depends on / 依赖: A.lift_relrank_comap, lift_id, lift_relrank_comap
-/
theorem relrank_comap {L : Type v} [Field L] (f : L ->+* E)
    (B : Subfield L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [lift_id] using A.lift_relrank_comap f B

/--
theorem `relfinrank_comap` / 定理 `relfinrank_comap`

English:
theorem relfinrank_comap
  given: (f : L ->+* E) (B : Subfield L)
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap A f B))

中文:
定理 relfinrank_comap
  条件: (f : L ->+* E) (B : 子域 L)
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap A f B))

Depends on / 依赖: lift_relrank_comap
-/
theorem relfinrank_comap (f : L ->+* E) (B : Subfield L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using! congr(toNat $(lift_relrank_comap A f B))

/--
theorem `lift_rank_comap` / 定理 `lift_rank_comap`

English:
theorem lift_rank_comap
  given: (f : L ->+* E)
  proof: by
  simpa only [relrank_top_right, ← RingHom.fieldRange_eq_map] using lift_relrank_comap A f ⊤

中文:
定理 lift_rank_comap
  条件: (f : L ->+* E)
  证明: by
  simpa only [relrank_top_right, ← RingHom.fieldRange_eq_map] using lift_relrank_comap A f ⊤

Depends on / 依赖: RingHom, RingHom.fieldRange_eq_map, fieldRange_eq_map, lift_relrank_comap, relrank_top_right
-/
theorem lift_rank_comap (f : L ->+* E) :
    lift.{v} (Module.rank (A.comap f) L) = lift.{w} (relrank A f.fieldRange) := by
  simpa only [relrank_top_right, ← RingHom.fieldRange_eq_map] using lift_relrank_comap A f ⊤

/--
theorem `rank_comap` / 定理 `rank_comap`

English:
theorem rank_comap
  given: {L : Type v} [Field L] (f : L ->+* E)
  proof: by
  simpa only [lift_id] using A.lift_rank_comap f

中文:
定理 rank_comap
  条件: {L : 类型v} [域 L] (f : L ->+* E)
  证明: by
  simpa only [lift_id] using A.lift_rank_comap f

Depends on / 依赖: A.lift_rank_comap, lift_id, lift_rank_comap
-/
theorem rank_comap {L : Type v} [Field L] (f : L ->+* E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [lift_id] using A.lift_rank_comap f

/--
theorem `finrank_comap` / 定理 `finrank_comap`

English:
theorem finrank_comap
  given: (f : L ->+* E)
  statement: finrank (A.comap f) L = relfinrank A f.fieldRange
  proof: by
  simpa using! congr(toNat $(lift_rank_comap A f))

中文:
定理 finrank_comap
  条件: (f : L ->+* E)
  结论: finrank (A.comap f) L = relfinrank A f.fieldRange
  证明: by
  simpa using! congr(toNat $(lift_rank_comap A f))

Depends on / 依赖: lift_rank_comap
-/
theorem finrank_comap (f : L ->+* E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using! congr(toNat $(lift_rank_comap A f))

/--
theorem `relfinrank_map_map` / 定理 `relfinrank_map_map`

English:
theorem relfinrank_map_map
  given: (f : E ->+* L)
  proof: by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))

中文:
定理 relfinrank_map_map
  条件: (f : E ->+* L)
  证明: by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))

Depends on / 依赖: lift_relrank_map_map
-/
theorem relfinrank_map_map (f : E ->+* L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))

/--
theorem `lift_relrank_comap_comap_eq_lift_relrank_inf` / 定理 `lift_relrank_comap_comap_eq_lift_relrank_inf`

English:
theorem lift_relrank_comap_comap_eq_lift_relrank_inf
  given: (f : L ->+* E)
  proof: by
  conv_lhs => rw [← lift_relrank_map_map _ _ f, map_comap_eq, map_comap_eq]
  congr 1
  apply relrank_eq_of_inf_eq
  rw [inf_assoc]; rw [inf_left_comm _ B]; rw [inf_of_le_left (le_refl _)]

中文:
定理 lift_relrank_comap_comap_eq_lift_relrank_inf
  条件: (f : L ->+* E)
  证明: by
  conv_lhs => rw [← lift_relrank_map_map _ _ f, map_comap_eq, map_comap_eq]
  congr 1
  apply relrank_eq_of_inf_eq
  rw [inf_assoc]; rw [inf_left_comm _ B]; rw [inf_of_le_left (le_refl _)]

Depends on / 依赖: conv_lhs, inf_assoc, inf_left_comm, inf_of_le_left, le_refl, lift_relrank_map_map, map_comap_eq, relrank_eq_of_inf_eq
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L ->+* E) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A (B ⊓ f.fieldRange)) := by
  conv_lhs => rw [← lift_relrank_map_map _ _ f, map_comap_eq, map_comap_eq]
  congr 1
  apply relrank_eq_of_inf_eq
  rw [inf_assoc]; rw [inf_left_comm _ B]; rw [inf_of_le_left (le_refl _)]

/--
theorem `relrank_comap_comap_eq_relrank_inf` / 定理 `relrank_comap_comap_eq_relrank_inf`

English:
theorem relrank_comap_comap_eq_relrank_inf
  proof: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

中文:
定理 relrank_comap_comap_eq_relrank_inf
  证明: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

Depends on / 依赖: lift_id, lift_relrank_comap_comap_eq_lift_relrank_inf
-/
theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] (f : L ->+* E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

/--
theorem `relfinrank_comap_comap_eq_relfinrank_inf` / 定理 `relfinrank_comap_comap_eq_relfinrank_inf`

English:
theorem relfinrank_comap_comap_eq_relfinrank_inf
  given: (f : L ->+* E)
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

中文:
定理 relfinrank_comap_comap_eq_relfinrank_inf
  条件: (f : L ->+* E)
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_inf
-/
theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L ->+* E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

/--
theorem `lift_relrank_comap_comap_eq_lift_relrank_of_le` / 定理 `lift_relrank_comap_comap_eq_lift_relrank_of_le`

English:
theorem lift_relrank_comap_comap_eq_lift_relrank_of_le
  given: (f : L ->+* E) (h : B <= f.fieldRange)
  proof: by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

中文:
定理 lift_relrank_comap_comap_eq_lift_relrank_of_le
  条件: (f : L ->+* E) (h : B <= f.fieldRange)
  证明: by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

Depends on / 依赖: inf_of_le_left, lift_relrank_comap_comap_eq_lift_relrank_inf
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L ->+* E) (h : B <= f.fieldRange) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

/--
theorem `relrank_comap_comap_eq_relrank_of_le` / 定理 `relrank_comap_comap_eq_relrank_of_le`

English:
theorem relrank_comap_comap_eq_relrank_of_le
  proof: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

中文:
定理 relrank_comap_comap_eq_relrank_of_le
  证明: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

Depends on / 依赖: lift_id, lift_relrank_comap_comap_eq_lift_relrank_of_le
-/
theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] (f : L ->+* E) (h : B <= f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

/--
theorem `relfinrank_comap_comap_eq_relfinrank_of_le` / 定理 `relfinrank_comap_comap_eq_relfinrank_of_le`

English:
theorem relfinrank_comap_comap_eq_relfinrank_of_le
  given: (f : L ->+* E) (h : B <= f.fieldRange)
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

中文:
定理 relfinrank_comap_comap_eq_relfinrank_of_le
  条件: (f : L ->+* E) (h : B <= f.fieldRange)
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_le
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L ->+* E) (h : B <= f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

/--
theorem `lift_relrank_comap_comap_eq_lift_relrank_of_surjective` / 定理 `lift_relrank_comap_comap_eq_lift_relrank_of_surjective`

English:
theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
  proof: lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ => h x

中文:
定理 lift_relrank_comap_comap_eq_lift_relrank_of_surjective
  证明: lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ => h x

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_le
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L ->+* E) (h : Function.Surjective f) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ => h x

/--
theorem `relrank_comap_comap_eq_relrank_of_surjective` / 定理 `relrank_comap_comap_eq_relrank_of_surjective`

English:
theorem relrank_comap_comap_eq_relrank_of_surjective
  proof: by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

中文:
定理 relrank_comap_comap_eq_relrank_of_surjective
  证明: by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_surjective
-/
theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] (f : L ->+* E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

/--
theorem `relfinrank_comap_comap_eq_relfinrank_of_surjective` / 定理 `relfinrank_comap_comap_eq_relfinrank_of_surjective`

English:
theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

中文:
定理 relfinrank_comap_comap_eq_relfinrank_of_surjective
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_surjective
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L ->+* E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
/--
theorem `relrank_dvd_rank_top_of_le` / 定理 `relrank_dvd_rank_top_of_le`

English:
theorem relrank_dvd_rank_top_of_le
  given: (h : A <= B)
  statement: relrank A B ∣ Module.rank A E
  proof: dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

中文:
定理 relrank_dvd_rank_top_of_le
  条件: (h : A <= B)
  结论: relrank A B ∣ 模.rank A E
  证明: dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

Depends on / 依赖: dvd_of_mul_right_eq, relrank_mul_rank_top
-/
theorem relrank_dvd_rank_top_of_le (h : A <= B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

variable {A B} in
/--
theorem `relfinrank_dvd_finrank_top_of_le` / 定理 `relfinrank_dvd_finrank_top_of_le`

English:
theorem relfinrank_dvd_finrank_top_of_le
  given: (h : A <= B)
  statement: relfinrank A B ∣ finrank A E
  proof: dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

中文:
定理 relfinrank_dvd_finrank_top_of_le
  条件: (h : A <= B)
  结论: relfinrank A B ∣ finrank A E
  证明: dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

Depends on / 依赖: dvd_of_mul_right_eq, relfinrank_mul_finrank_top
-/
theorem relfinrank_dvd_finrank_top_of_le (h : A <= B) : relfinrank A B ∣ finrank A E :=
  dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

variable {A B C} in
/--
theorem `relrank_mul_relrank` / 定理 `relrank_mul_relrank`

English:
theorem relrank_mul_relrank
  given: (h1 : A <= B) (h2 : B <= C)
  proof: by
  have h3 := h1.trans h2
  rw [relrank_eq_rank_of_le h1]; rw [relrank_eq_rank_of_le h2]; rw [relrank_eq_rank_of_le h3]
  let : Algebra A B := (inclusion h1).toAlgebra
  let : Algebra B C := (inclusion h2).toAlgebra
  let : Algebra A C := (inclusion h3).toAlgebra
  have : IsScalarTower A B C := Is

中文:
定理 relrank_mul_relrank
  条件: (h1 : A <= B) (h2 : B <= C)
  证明: by
  have h3 := h1.trans h2
  rw [relrank_eq_rank_of_le h1]; rw [relrank_eq_rank_of_le h2]; rw [relrank_eq_rank_of_le h3]
  let : Algebra A B := (inclusion h1).toAlgebra
  let : Algebra B C := (inclusion h2).toAlgebra
  let : Algebra A C := (inclusion h3).toAlgebra
  have : IsScalarTower A B C := Is

Depends on / 依赖: Algebra, IsScalarTower, IsScalarTower.of_algebraMap_eq, h1.trans, inclusion, of_algebraMap_eq, rank_mul_rank, relrank_eq_rank_of_le, toAlgebra
-/
theorem relrank_mul_relrank (h1 : A <= B) (h2 : B <= C) :
    relrank A B * relrank B C = relrank A C := by
  have h3 := h1.trans h2
  rw [relrank_eq_rank_of_le h1]; rw [relrank_eq_rank_of_le h2]; rw [relrank_eq_rank_of_le h3]
  let : Algebra A B := (inclusion h1).toAlgebra
  let : Algebra B C := (inclusion h2).toAlgebra
  let : Algebra A C := (inclusion h3).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B C

variable {A B C} in
/--
theorem `relfinrank_mul_relfinrank` / 定理 `relfinrank_mul_relfinrank`

English:
theorem relfinrank_mul_relfinrank
  given: (h1 : A <= B) (h2 : B <= C)
  proof: by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))

中文:
定理 relfinrank_mul_relfinrank
  条件: (h1 : A <= B) (h2 : B <= C)
  证明: by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))

Depends on / 依赖: relrank_mul_relrank
-/
theorem relfinrank_mul_relfinrank (h1 : A <= B) (h2 : B <= C) :
    relfinrank A B * relfinrank B C = relfinrank A C := by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))

/--
theorem `relrank_inf_mul_relrank` / 定理 `relrank_inf_mul_relrank`

English:
theorem relrank_inf_mul_relrank
  statement: A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
  proof: by
  rw [← inf_relrank_right A (B ⊓ C)]; rw [← inf_relrank_right B C]; rw [← inf_relrank_right (A ⊓ B) C]; rw [inf_assoc]; rw [relrank_mul_relrank inf_le_right inf_le_right]

中文:
定理 relrank_inf_mul_relrank
  结论: A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
  证明: by
  rw [← inf_relrank_right A (B ⊓ C)]; rw [← inf_relrank_right B C]; rw [← inf_relrank_right (A ⊓ B) C]; rw [inf_assoc]; rw [relrank_mul_relrank inf_le_right inf_le_right]

Depends on / 依赖: inf_assoc, inf_le_right, inf_relrank_right, relrank_mul_relrank
-/
theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C := by
  rw [← inf_relrank_right A (B ⊓ C)]; rw [← inf_relrank_right B C]; rw [← inf_relrank_right (A ⊓ B) C]; rw [inf_assoc]; rw [relrank_mul_relrank inf_le_right inf_le_right]

/--
theorem `relfinrank_inf_mul_relfinrank` / 定理 `relfinrank_inf_mul_relfinrank`

English:
theorem relfinrank_inf_mul_relfinrank
  proof: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

中文:
定理 relfinrank_inf_mul_relfinrank
  证明: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

Depends on / 依赖: relrank_inf_mul_relrank
-/
theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
/--
theorem `relrank_mul_relrank_eq_inf_relrank` / 定理 `relrank_mul_relrank_eq_inf_relrank`

English:
theorem relrank_mul_relrank_eq_inf_relrank
  given: (h : B <= C)
  proof: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

中文:
定理 relrank_mul_relrank_eq_inf_relrank
  条件: (h : B <= C)
  证明: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

Depends on / 依赖: inf_of_le_left, relrank_inf_mul_relrank
-/
theorem relrank_mul_relrank_eq_inf_relrank (h : B <= C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
/--
theorem `relfinrank_mul_relfinrank_eq_inf_relfinrank` / 定理 `relfinrank_mul_relfinrank_eq_inf_relfinrank`

English:
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank
  given: (h : B <= C)
  proof: by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

中文:
定理 relfinrank_mul_relfinrank_eq_inf_relfinrank
  条件: (h : B <= C)
  证明: by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

Depends on / 依赖: relrank_mul_relrank_eq_inf_relrank
-/
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B <= C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
/--
theorem `relrank_inf_mul_relrank_of_le` / 定理 `relrank_inf_mul_relrank_of_le`

English:
theorem relrank_inf_mul_relrank_of_le
  given: (h : A <= B)
  proof: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

中文:
定理 relrank_inf_mul_relrank_of_le
  条件: (h : A <= B)
  证明: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

Depends on / 依赖: inf_of_le_left, relrank_inf_mul_relrank
-/
theorem relrank_inf_mul_relrank_of_le (h : A <= B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
/--
theorem `relfinrank_inf_mul_relfinrank_of_le` / 定理 `relfinrank_inf_mul_relfinrank_of_le`

English:
theorem relfinrank_inf_mul_relfinrank_of_le
  given: (h : A <= B)
  proof: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

中文:
定理 relfinrank_inf_mul_relfinrank_of_le
  条件: (h : A <= B)
  证明: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

Depends on / 依赖: relrank_inf_mul_relrank_of_le
-/
theorem relfinrank_inf_mul_relfinrank_of_le (h : A <= B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

variable {A B} in
/--
theorem `relrank_dvd_of_le_left` / 定理 `relrank_dvd_of_le_left`

English:
theorem relrank_dvd_of_le_left
  given: (h : A <= B)
  statement: B.relrank C ∣ A.relrank C
  proof: dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

中文:
定理 relrank_dvd_of_le_left
  条件: (h : A <= B)
  结论: B.relrank C ∣ A.relrank C
  证明: dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

Depends on / 依赖: dvd_of_mul_left_eq, relrank_inf_mul_relrank_of_le
-/
theorem relrank_dvd_of_le_left (h : A <= B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

variable {A B} in
/--
theorem `relfinrank_dvd_of_le_left` / 定理 `relfinrank_dvd_of_le_left`

English:
theorem relfinrank_dvd_of_le_left
  given: (h : A <= B)
  statement: B.relfinrank C ∣ A.relfinrank C
  proof: dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

中文:
定理 relfinrank_dvd_of_le_left
  条件: (h : A <= B)
  结论: B.relfinrank C ∣ A.relfinrank C
  证明: dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

Depends on / 依赖: dvd_of_mul_left_eq, relfinrank_inf_mul_relfinrank_of_le
-/
theorem relfinrank_dvd_of_le_left (h : A <= B) : B.relfinrank C ∣ A.relfinrank C :=
  dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

end Subfield

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable {L : Type w} [Field L] [Algebra F L]

variable (A B C : IntermediateField F E)

/--
Definition of `relrank` / `relrank` 的定义

English:
definition relrank
  body: A.toSubfield.relrank B.toSubfield

中文:
定义 relrank
  定义体: A.toSubfield.relrank B.toSubfield

Depends on / 依赖: A.toSubfield.relrank, B.toSubfield, relrank, toSubfield
-/
noncomputable def relrank := A.toSubfield.relrank B.toSubfield

/--
Definition of `relfinrank` / `relfinrank` 的定义

English:
definition relfinrank
  body: A.toSubfield.relfinrank B.toSubfield

中文:
定义 relfinrank
  定义体: A.toSubfield.relfinrank B.toSubfield

Depends on / 依赖: A.toSubfield.relfinrank, B.toSubfield, relfinrank, toSubfield
-/
noncomputable def relfinrank := A.toSubfield.relfinrank B.toSubfield

/--
theorem `relfinrank_eq_toNat_relrank` / 定理 `relfinrank_eq_toNat_relrank`

English:
theorem relfinrank_eq_toNat_relrank
  statement: relfinrank A B = toNat (relrank A B)
  proof: rfl

中文:
定理 relfinrank_eq_to自然数_relrank
  结论: relfinrank A B = to自然数 (relrank A B)
  证明: rfl
-/
theorem relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B) := rfl

variable {A B C}

/--
theorem `relrank_eq_of_inf_eq` / 定理 `relrank_eq_of_inf_eq`

English:
theorem relrank_eq_of_inf_eq
  given: (h : A ⊓ C = B ⊓ C)
  statement: relrank A C = relrank B C
  proof: Subfield.relrank_eq_of_inf_eq congr(toSubfield $h)

中文:
定理 relrank_eq_of_inf_eq
  条件: (h : A ⊓ C = B ⊓ C)
  结论: relrank A C = relrank B C
  证明: Subfield.relrank_eq_of_inf_eq congr(toSubfield $h)

Depends on / 依赖: Subfield, Subfield.relrank_eq_of_inf_eq, relrank_eq_of_inf_eq, toSubfield
-/
theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C :=
  Subfield.relrank_eq_of_inf_eq congr(toSubfield $h)

/--
theorem `relfinrank_eq_of_inf_eq` / 定理 `relfinrank_eq_of_inf_eq`

English:
theorem relfinrank_eq_of_inf_eq
  given: (h : A ⊓ C = B ⊓ C)
  statement: relfinrank A C = relfinrank B C
  proof: congr(toNat $(relrank_eq_of_inf_eq h))

中文:
定理 relfinrank_eq_of_inf_eq
  条件: (h : A ⊓ C = B ⊓ C)
  结论: relfinrank A C = relfinrank B C
  证明: congr(toNat $(relrank_eq_of_inf_eq h))

Depends on / 依赖: relrank_eq_of_inf_eq
-/
theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

/--
theorem `relrank_eq_rank_of_le` / 定理 `relrank_eq_rank_of_le`

English:
theorem relrank_eq_rank_of_le
  given: (h : A <= B)
  statement: relrank A B = Module.rank A (extendScalars h)
  proof: Subfield.relrank_eq_rank_of_le h

中文:
定理 relrank_eq_rank_of_le
  条件: (h : A <= B)
  结论: relrank A B = 模.rank A (extendScalars h)
  证明: Subfield.relrank_eq_rank_of_le h

Depends on / 依赖: Subfield, Subfield.relrank_eq_rank_of_le, relrank_eq_rank_of_le
-/
theorem relrank_eq_rank_of_le (h : A <= B) : relrank A B = Module.rank A (extendScalars h) :=
  Subfield.relrank_eq_rank_of_le h

/--
theorem `relfinrank_eq_finrank_of_le` / 定理 `relfinrank_eq_finrank_of_le`

English:
theorem relfinrank_eq_finrank_of_le
  given: (h : A <= B)
  statement: relfinrank A B = finrank A (extendScalars h)
  proof: congr(toNat $(relrank_eq_rank_of_le h))

中文:
定理 relfinrank_eq_finrank_of_le
  条件: (h : A <= B)
  结论: relfinrank A B = finrank A (extendScalars h)
  证明: congr(toNat $(relrank_eq_rank_of_le h))

Depends on / 依赖: relrank_eq_rank_of_le
-/
theorem relfinrank_eq_finrank_of_le (h : A <= B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)

/--
theorem `inf_relrank_right` / 定理 `inf_relrank_right`

English:
theorem inf_relrank_right
  statement: relrank (A ⊓ B) B = relrank A B
  proof: relrank_eq_rank_of_le (inf_le_right : A ⊓ B <= B)

中文:
定理 inf_relrank_right
  结论: relrank (A ⊓ B) B = relrank A B
  证明: relrank_eq_rank_of_le (inf_le_right : A ⊓ B <= B)

Depends on / 依赖: inf_le_right, relrank_eq_rank_of_le
-/
theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B <= B)

/--
theorem `inf_relfinrank_right` / 定理 `inf_relfinrank_right`

English:
theorem inf_relfinrank_right
  statement: relfinrank (A ⊓ B) B = relfinrank A B
  proof: congr(toNat $(inf_relrank_right A B))

中文:
定理 inf_relfinrank_right
  结论: relfinrank (A ⊓ B) B = relfinrank A B
  证明: congr(toNat $(inf_relrank_right A B))

Depends on / 依赖: inf_relrank_right
-/
theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))

/--
theorem `inf_relrank_left` / 定理 `inf_relrank_left`

English:
theorem inf_relrank_left
  statement: relrank (A ⊓ B) A = relrank B A
  proof: by
  rw [inf_comm]; rw [inf_relrank_right]

中文:
定理 inf_relrank_left
  结论: relrank (A ⊓ B) A = relrank B A
  证明: by
  rw [inf_comm]; rw [inf_relrank_right]

Depends on / 依赖: inf_comm, inf_relrank_right
-/
theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm]; rw [inf_relrank_right]

/--
theorem `inf_relfinrank_left` / 定理 `inf_relfinrank_left`

English:
theorem inf_relfinrank_left
  statement: relfinrank (A ⊓ B) A = relfinrank B A
  proof: congr(toNat $(inf_relrank_left A B))

@[simp]

中文:
定理 inf_relfinrank_left
  结论: relfinrank (A ⊓ B) A = relfinrank B A
  证明: congr(toNat $(inf_relrank_left A B))

@[simp]

Depends on / 依赖: inf_relrank_left
-/
theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

@[simp]
/--
theorem `relrank_self` / 定理 `relrank_self`

English:
theorem relrank_self
  statement: relrank A A = 1
  proof: A.toSubfield.relrank_self

@[simp]

中文:
定理 relrank_self
  结论: relrank A A = 1
  证明: A.toSubfield.relrank_self

@[simp]

Depends on / 依赖: A.toSubfield.relrank_self, relrank_self, toSubfield
-/
theorem relrank_self : relrank A A = 1 := A.toSubfield.relrank_self

@[simp]
/--
theorem `relfinrank_self` / 定理 `relfinrank_self`

English:
theorem relfinrank_self
  statement: relfinrank A A = 1
  proof: A.toSubfield.relfinrank_self

中文:
定理 relfinrank_self
  结论: relfinrank A A = 1
  证明: A.toSubfield.relfinrank_self

Depends on / 依赖: A.toSubfield.relfinrank_self, relfinrank_self, toSubfield
-/
theorem relfinrank_self : relfinrank A A = 1 := A.toSubfield.relfinrank_self

variable {A B}

/--
theorem `relrank_eq_one_iff` / 定理 `relrank_eq_one_iff`

English:
theorem relrank_eq_one_iff
  statement: relrank A B = 1 ↔ B <= A
  proof: Subfield.relrank_eq_one_iff

中文:
定理 relrank_eq_one_iff
  结论: relrank A B = 1 ↔ B <= A
  证明: Subfield.relrank_eq_one_iff

Depends on / 依赖: Subfield, Subfield.relrank_eq_one_iff, relrank_eq_one_iff
-/
theorem relrank_eq_one_iff : relrank A B = 1 ↔ B <= A :=
  Subfield.relrank_eq_one_iff

/--
theorem `relfinrank_eq_one_iff` / 定理 `relfinrank_eq_one_iff`

English:
theorem relfinrank_eq_one_iff
  statement: relfinrank A B = 1 ↔ B <= A
  proof: Subfield.relfinrank_eq_one_iff

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

中文:
定理 relfinrank_eq_one_iff
  结论: relfinrank A B = 1 ↔ B <= A
  证明: Subfield.relfinrank_eq_one_iff

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

Depends on / 依赖: Subfield, Subfield.relfinrank_eq_one_iff, relfinrank_eq_one_iff
-/
theorem relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B <= A :=
  Subfield.relfinrank_eq_one_iff

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

variable (A B)

/--
theorem `lift_rank_comap` / 定理 `lift_rank_comap`

English:
theorem lift_rank_comap
  given: (f : L ->ₐ[F] E)
  proof: A.toSubfield.lift_rank_comap f.toRingHom

中文:
定理 lift_rank_comap
  条件: (f : L ->ₐ[F] E)
  证明: A.toSubfield.lift_rank_comap f.toRingHom

Depends on / 依赖: A.toSubfield.lift_rank_comap, f.toRingHom, lift_rank_comap, toRingHom, toSubfield
-/
theorem lift_rank_comap (f : L ->ₐ[F] E) :
    Cardinal.lift.{v} (Module.rank (A.comap f) L) = Cardinal.lift.{w} (relrank A f.fieldRange) :=
  A.toSubfield.lift_rank_comap f.toRingHom

/--
theorem `rank_comap` / 定理 `rank_comap`

English:
theorem rank_comap
  given: {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E)
  proof: by
  simpa only [lift_id] using A.lift_rank_comap f

中文:
定理 rank_comap
  条件: {L : 类型v} [域 L] [代数 F L] (f : L ->ₐ[F] E)
  证明: by
  simpa only [lift_id] using A.lift_rank_comap f

Depends on / 依赖: A.lift_rank_comap, lift_id, lift_rank_comap
-/
theorem rank_comap {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [lift_id] using A.lift_rank_comap f

/--
theorem `finrank_comap` / 定理 `finrank_comap`

English:
theorem finrank_comap
  given: (f : L ->ₐ[F] E)
  statement: finrank (A.comap f) L = relfinrank A f.fieldRange
  proof: by
  simpa using! congr(toNat $(lift_rank_comap A f))

中文:
定理 finrank_comap
  条件: (f : L ->ₐ[F] E)
  结论: finrank (A.comap f) L = relfinrank A f.fieldRange
  证明: by
  simpa using! congr(toNat $(lift_rank_comap A f))

Depends on / 依赖: lift_rank_comap
-/
theorem finrank_comap (f : L ->ₐ[F] E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using! congr(toNat $(lift_rank_comap A f))

/--
theorem `lift_relrank_comap` / 定理 `lift_relrank_comap`

English:
theorem lift_relrank_comap
  given: (f : L ->ₐ[F] E) (B : IntermediateField F L)
  proof: A.toSubfield.lift_relrank_comap f.toRingHom B.toSubfield

中文:
定理 lift_relrank_comap
  条件: (f : L ->ₐ[F] E) (B : 中间域 F L)
  证明: A.toSubfield.lift_relrank_comap f.toRingHom B.toSubfield

Depends on / 依赖: A.toSubfield.lift_relrank_comap, B.toSubfield, f.toRingHom, lift_relrank_comap, toRingHom, toSubfield
-/
theorem lift_relrank_comap (f : L ->ₐ[F] E) (B : IntermediateField F L) :
    Cardinal.lift.{v} (relrank (A.comap f) B) = Cardinal.lift.{w} (relrank A (B.map f)) :=
  A.toSubfield.lift_relrank_comap f.toRingHom B.toSubfield

/--
theorem `relrank_comap` / 定理 `relrank_comap`

English:
theorem relrank_comap
  statement: {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E)
  proof: by
  simpa only [lift_id] using A.lift_relrank_comap f B

中文:
定理 relrank_comap
  结论: {L : 类型v} [域 L] [代数 F L] (f : L ->ₐ[F] E)
  证明: by
  simpa only [lift_id] using A.lift_relrank_comap f B

Depends on / 依赖: A.lift_relrank_comap, lift_id, lift_relrank_comap
-/
theorem relrank_comap {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E)
    (B : IntermediateField F L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [lift_id] using A.lift_relrank_comap f B

/--
theorem `relfinrank_comap` / 定理 `relfinrank_comap`

English:
theorem relfinrank_comap
  given: (f : L ->ₐ[F] E) (B : IntermediateField F L)
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap A f B))

中文:
定理 relfinrank_comap
  条件: (f : L ->ₐ[F] E) (B : 中间域 F L)
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap A f B))

Depends on / 依赖: lift_relrank_comap
-/
theorem relfinrank_comap (f : L ->ₐ[F] E) (B : IntermediateField F L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using! congr(toNat $(lift_relrank_comap A f B))

/--
theorem `lift_relrank_map_map` / 定理 `lift_relrank_map_map`

English:
theorem lift_relrank_map_map
  given: (f : E ->ₐ[F] L)
  proof: by
  rw [← lift_relrank_comap]; rw [comap_map]

中文:
定理 lift_relrank_map_map
  条件: (f : E ->ₐ[F] L)
  证明: by
  rw [← lift_relrank_comap]; rw [comap_map]

Depends on / 依赖: comap_map, lift_relrank_comap
-/
theorem lift_relrank_map_map (f : E ->ₐ[F] L) :
    Cardinal.lift.{v} (relrank (A.map f) (B.map f)) = Cardinal.lift.{w} (relrank A B) := by
  rw [← lift_relrank_comap]; rw [comap_map]

/--
theorem `relrank_map_map` / 定理 `relrank_map_map`

English:
theorem relrank_map_map
  given: {L : Type v} [Field L] [Algebra F L] (f : E ->ₐ[F] L)
  proof: by
  simpa only [lift_id] using lift_relrank_map_map A B f

中文:
定理 relrank_map_map
  条件: {L : 类型v} [域 L] [代数 F L] (f : E ->ₐ[F] L)
  证明: by
  simpa only [lift_id] using lift_relrank_map_map A B f

Depends on / 依赖: lift_id, lift_relrank_map_map
-/
theorem relrank_map_map {L : Type v} [Field L] [Algebra F L] (f : E ->ₐ[F] L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_map_map A B f

/--
theorem `relfinrank_map_map` / 定理 `relfinrank_map_map`

English:
theorem relfinrank_map_map
  given: (f : E ->ₐ[F] L)
  proof: by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))

中文:
定理 relfinrank_map_map
  条件: (f : E ->ₐ[F] L)
  证明: by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))

Depends on / 依赖: lift_relrank_map_map
-/
theorem relfinrank_map_map (f : E ->ₐ[F] L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))

/--
theorem `lift_relrank_comap_comap_eq_lift_relrank_inf` / 定理 `lift_relrank_comap_comap_eq_lift_relrank_inf`

English:
theorem lift_relrank_comap_comap_eq_lift_relrank_inf
  given: (f : L ->ₐ[F] E)
  proof: A.toSubfield.lift_relrank_comap_comap_eq_lift_relrank_inf B.toSubfield f.toRingHom

中文:
定理 lift_relrank_comap_comap_eq_lift_relrank_inf
  条件: (f : L ->ₐ[F] E)
  证明: A.toSubfield.lift_relrank_comap_comap_eq_lift_relrank_inf B.toSubfield f.toRingHom

Depends on / 依赖: A.toSubfield.lift_relrank_comap_comap_eq_lift_relrank_inf, B.toSubfield, f.toRingHom, lift_relrank_comap_comap_eq_lift_relrank_inf, toRingHom, toSubfield
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L ->ₐ[F] E) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) =
    Cardinal.lift.{w} (relrank A (B ⊓ f.fieldRange)) :=
  A.toSubfield.lift_relrank_comap_comap_eq_lift_relrank_inf B.toSubfield f.toRingHom

/--
theorem `relrank_comap_comap_eq_relrank_inf` / 定理 `relrank_comap_comap_eq_relrank_inf`

English:
theorem relrank_comap_comap_eq_relrank_inf
  proof: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

中文:
定理 relrank_comap_comap_eq_relrank_inf
  证明: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

Depends on / 依赖: lift_id, lift_relrank_comap_comap_eq_lift_relrank_inf
-/
theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

/--
theorem `relfinrank_comap_comap_eq_relfinrank_inf` / 定理 `relfinrank_comap_comap_eq_relfinrank_inf`

English:
theorem relfinrank_comap_comap_eq_relfinrank_inf
  given: (f : L ->ₐ[F] E)
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

中文:
定理 relfinrank_comap_comap_eq_relfinrank_inf
  条件: (f : L ->ₐ[F] E)
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_inf
-/
theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L ->ₐ[F] E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))

/--
theorem `lift_relrank_comap_comap_eq_lift_relrank_of_le` / 定理 `lift_relrank_comap_comap_eq_lift_relrank_of_le`

English:
theorem lift_relrank_comap_comap_eq_lift_relrank_of_le
  given: (f : L ->ₐ[F] E) (h : B <= f.fieldRange)
  proof: by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

中文:
定理 lift_relrank_comap_comap_eq_lift_relrank_of_le
  条件: (f : L ->ₐ[F] E) (h : B <= f.fieldRange)
  证明: by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

Depends on / 依赖: inf_of_le_left, lift_relrank_comap_comap_eq_lift_relrank_inf
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L ->ₐ[F] E) (h : B <= f.fieldRange) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f

/--
theorem `relrank_comap_comap_eq_relrank_of_le` / 定理 `relrank_comap_comap_eq_relrank_of_le`

English:
theorem relrank_comap_comap_eq_relrank_of_le
  proof: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

中文:
定理 relrank_comap_comap_eq_relrank_of_le
  证明: by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

Depends on / 依赖: lift_id, lift_relrank_comap_comap_eq_lift_relrank_of_le
-/
theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E) (h : B <= f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h

/--
theorem `relfinrank_comap_comap_eq_relfinrank_of_le` / 定理 `relfinrank_comap_comap_eq_relfinrank_of_le`

English:
theorem relfinrank_comap_comap_eq_relfinrank_of_le
  given: (f : L ->ₐ[F] E) (h : B <= f.fieldRange)
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

中文:
定理 relfinrank_comap_comap_eq_relfinrank_of_le
  条件: (f : L ->ₐ[F] E) (h : B <= f.fieldRange)
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_le
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L ->ₐ[F] E) (h : B <= f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))

/--
theorem `lift_relrank_comap_comap_eq_lift_relrank_of_surjective` / 定理 `lift_relrank_comap_comap_eq_lift_relrank_of_surjective`

English:
theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
  proof: lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ => h x

中文:
定理 lift_relrank_comap_comap_eq_lift_relrank_of_surjective
  证明: lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ => h x

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_le
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L ->ₐ[F] E) (h : Function.Surjective f) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ => h x

/--
theorem `relrank_comap_comap_eq_relrank_of_surjective` / 定理 `relrank_comap_comap_eq_relrank_of_surjective`

English:
theorem relrank_comap_comap_eq_relrank_of_surjective
  proof: by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

中文:
定理 relrank_comap_comap_eq_relrank_of_surjective
  证明: by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_surjective
-/
theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h

/--
theorem `relfinrank_comap_comap_eq_relfinrank_of_surjective` / 定理 `relfinrank_comap_comap_eq_relfinrank_of_surjective`

English:
theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
  proof: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

中文:
定理 relfinrank_comap_comap_eq_relfinrank_of_surjective
  证明: by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

Depends on / 依赖: lift_relrank_comap_comap_eq_lift_relrank_of_surjective
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L ->ₐ[F] E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
/--
theorem `relrank_mul_rank_top` / 定理 `relrank_mul_rank_top`

English:
theorem relrank_mul_rank_top
  given: (h : A <= B)
  statement: relrank A B * Module.rank B E = Module.rank A E
  proof: Subfield.relrank_mul_rank_top h

中文:
定理 relrank_mul_rank_top
  条件: (h : A <= B)
  结论: relrank A B * 模.rank B E = 模.rank A E
  证明: Subfield.relrank_mul_rank_top h

Depends on / 依赖: Subfield, Subfield.relrank_mul_rank_top, relrank_mul_rank_top
-/
theorem relrank_mul_rank_top (h : A <= B) : relrank A B * Module.rank B E = Module.rank A E :=
  Subfield.relrank_mul_rank_top h

variable {A B} in
/--
theorem `relfinrank_mul_finrank_top` / 定理 `relfinrank_mul_finrank_top`

English:
theorem relfinrank_mul_finrank_top
  given: (h : A <= B)
  statement: relfinrank A B * finrank B E = finrank A E
  proof: by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

中文:
定理 relfinrank_mul_finrank_top
  条件: (h : A <= B)
  结论: relfinrank A B * finrank B E = finrank A E
  证明: by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

Depends on / 依赖: relrank_mul_rank_top
-/
theorem relfinrank_mul_finrank_top (h : A <= B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

variable {A B} in
/--
theorem `rank_bot_mul_relrank` / 定理 `rank_bot_mul_relrank`

English:
theorem rank_bot_mul_relrank
  given: (h : A <= B)
  statement: Module.rank F A * relrank A B = Module.rank F B
  proof: by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  exact rank_mul_rank F A B

中文:
定理 rank_bot_mul_relrank
  条件: (h : A <= B)
  结论: 模.rank F A * relrank A B = 模.rank F B
  证明: by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  exact rank_mul_rank F A B

Depends on / 依赖: Algebra, inclusion, rank_mul_rank, relrank_eq_rank_of_le, toAlgebra
-/
theorem rank_bot_mul_relrank (h : A <= B) : Module.rank F A * relrank A B = Module.rank F B := by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  exact rank_mul_rank F A B

variable {A B} in
/--
theorem `finrank_bot_mul_relfinrank` / 定理 `finrank_bot_mul_relfinrank`

English:
theorem finrank_bot_mul_relfinrank
  given: (h : A <= B)
  statement: finrank F A * relfinrank A B = finrank F B
  proof: by
  simpa using! congr(toNat $(rank_bot_mul_relrank h))

中文:
定理 finrank_bot_mul_relfinrank
  条件: (h : A <= B)
  结论: finrank F A * relfinrank A B = finrank F B
  证明: by
  simpa using! congr(toNat $(rank_bot_mul_relrank h))

Depends on / 依赖: rank_bot_mul_relrank
-/
theorem finrank_bot_mul_relfinrank (h : A <= B) : finrank F A * relfinrank A B = finrank F B := by
  simpa using! congr(toNat $(rank_bot_mul_relrank h))

variable {A B} in
/--
theorem `relrank_dvd_rank_top_of_le` / 定理 `relrank_dvd_rank_top_of_le`

English:
theorem relrank_dvd_rank_top_of_le
  given: (h : A <= B)
  statement: relrank A B ∣ Module.rank A E
  proof: dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

中文:
定理 relrank_dvd_rank_top_of_le
  条件: (h : A <= B)
  结论: relrank A B ∣ 模.rank A E
  证明: dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

Depends on / 依赖: dvd_of_mul_right_eq, relrank_mul_rank_top
-/
theorem relrank_dvd_rank_top_of_le (h : A <= B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

variable {A B} in
/--
theorem `relfinrank_dvd_finrank_top_of_le` / 定理 `relfinrank_dvd_finrank_top_of_le`

English:
theorem relfinrank_dvd_finrank_top_of_le
  given: (h : A <= B)
  statement: relfinrank A B ∣ finrank A E
  proof: dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

中文:
定理 relfinrank_dvd_finrank_top_of_le
  条件: (h : A <= B)
  结论: relfinrank A B ∣ finrank A E
  证明: dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

Depends on / 依赖: dvd_of_mul_right_eq, relfinrank_mul_finrank_top
-/
theorem relfinrank_dvd_finrank_top_of_le (h : A <= B) : relfinrank A B ∣ finrank A E :=
  dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

/--
theorem `relrank_dvd_rank_bot` / 定理 `relrank_dvd_rank_bot`

English:
theorem relrank_dvd_rank_bot
  statement: relrank A B ∣ Module.rank F B
  proof: inf_relrank_right A B ▸ dvd_of_mul_left_eq _ (rank_bot_mul_relrank inf_le_right)

中文:
定理 relrank_dvd_rank_bot
  结论: relrank A B ∣ 模.rank F B
  证明: inf_relrank_right A B ▸ dvd_of_mul_left_eq _ (rank_bot_mul_relrank inf_le_right)

Depends on / 依赖: dvd_of_mul_left_eq, inf_le_right, inf_relrank_right, rank_bot_mul_relrank
-/
theorem relrank_dvd_rank_bot : relrank A B ∣ Module.rank F B :=
  inf_relrank_right A B ▸ dvd_of_mul_left_eq _ (rank_bot_mul_relrank inf_le_right)

/--
theorem `relfinrank_dvd_finrank_bot` / 定理 `relfinrank_dvd_finrank_bot`

English:
theorem relfinrank_dvd_finrank_bot
  statement: relfinrank A B ∣ finrank F B
  proof: inf_relfinrank_right A B ▸ dvd_of_mul_left_eq _ (finrank_bot_mul_relfinrank inf_le_right)

中文:
定理 relfinrank_dvd_finrank_bot
  结论: relfinrank A B ∣ finrank F B
  证明: inf_relfinrank_right A B ▸ dvd_of_mul_left_eq _ (finrank_bot_mul_relfinrank inf_le_right)

Depends on / 依赖: dvd_of_mul_left_eq, finrank_bot_mul_relfinrank, inf_le_right, inf_relfinrank_right
-/
theorem relfinrank_dvd_finrank_bot : relfinrank A B ∣ finrank F B :=
  inf_relfinrank_right A B ▸ dvd_of_mul_left_eq _ (finrank_bot_mul_relfinrank inf_le_right)

variable {A B C} in
/--
theorem `relrank_mul_relrank` / 定理 `relrank_mul_relrank`

English:
theorem relrank_mul_relrank
  given: (h1 : A <= B) (h2 : B <= C)
  proof: Subfield.relrank_mul_relrank h1 h2

中文:
定理 relrank_mul_relrank
  条件: (h1 : A <= B) (h2 : B <= C)
  证明: Subfield.relrank_mul_relrank h1 h2

Depends on / 依赖: Subfield, Subfield.relrank_mul_relrank, relrank_mul_relrank
-/
theorem relrank_mul_relrank (h1 : A <= B) (h2 : B <= C) :
    relrank A B * relrank B C = relrank A C :=
  Subfield.relrank_mul_relrank h1 h2

variable {A B C} in
/--
theorem `relfinrank_mul_relfinrank` / 定理 `relfinrank_mul_relfinrank`

English:
theorem relfinrank_mul_relfinrank
  given: (h1 : A <= B) (h2 : B <= C)
  proof: by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))

中文:
定理 relfinrank_mul_relfinrank
  条件: (h1 : A <= B) (h2 : B <= C)
  证明: by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))

Depends on / 依赖: relrank_mul_relrank
-/
theorem relfinrank_mul_relfinrank (h1 : A <= B) (h2 : B <= C) :
    relfinrank A B * relfinrank B C = relfinrank A C := by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))

/--
theorem `relrank_inf_mul_relrank` / 定理 `relrank_inf_mul_relrank`

English:
theorem relrank_inf_mul_relrank
  statement: A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
  proof: Subfield.relrank_inf_mul_relrank A.toSubfield B.toSubfield C.toSubfield

中文:
定理 relrank_inf_mul_relrank
  结论: A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
  证明: Subfield.relrank_inf_mul_relrank A.toSubfield B.toSubfield C.toSubfield

Depends on / 依赖: A.toSubfield, B.toSubfield, C.toSubfield, Subfield, Subfield.relrank_inf_mul_relrank, relrank_inf_mul_relrank, toSubfield
-/
theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C :=
  Subfield.relrank_inf_mul_relrank A.toSubfield B.toSubfield C.toSubfield

/--
theorem `relfinrank_inf_mul_relfinrank` / 定理 `relfinrank_inf_mul_relfinrank`

English:
theorem relfinrank_inf_mul_relfinrank
  proof: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

中文:
定理 relfinrank_inf_mul_relfinrank
  证明: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

Depends on / 依赖: relrank_inf_mul_relrank
-/
theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
/--
theorem `relrank_mul_relrank_eq_inf_relrank` / 定理 `relrank_mul_relrank_eq_inf_relrank`

English:
theorem relrank_mul_relrank_eq_inf_relrank
  given: (h : B <= C)
  proof: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

中文:
定理 relrank_mul_relrank_eq_inf_relrank
  条件: (h : B <= C)
  证明: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

Depends on / 依赖: inf_of_le_left, relrank_inf_mul_relrank
-/
theorem relrank_mul_relrank_eq_inf_relrank (h : B <= C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
/--
theorem `relfinrank_mul_relfinrank_eq_inf_relfinrank` / 定理 `relfinrank_mul_relfinrank_eq_inf_relfinrank`

English:
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank
  given: (h : B <= C)
  proof: by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

中文:
定理 relfinrank_mul_relfinrank_eq_inf_relfinrank
  条件: (h : B <= C)
  证明: by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

Depends on / 依赖: relrank_mul_relrank_eq_inf_relrank
-/
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B <= C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
/--
theorem `relrank_inf_mul_relrank_of_le` / 定理 `relrank_inf_mul_relrank_of_le`

English:
theorem relrank_inf_mul_relrank_of_le
  given: (h : A <= B)
  proof: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

中文:
定理 relrank_inf_mul_relrank_of_le
  条件: (h : A <= B)
  证明: by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

Depends on / 依赖: inf_of_le_left, relrank_inf_mul_relrank
-/
theorem relrank_inf_mul_relrank_of_le (h : A <= B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
/--
theorem `relfinrank_inf_mul_relfinrank_of_le` / 定理 `relfinrank_inf_mul_relfinrank_of_le`

English:
theorem relfinrank_inf_mul_relfinrank_of_le
  given: (h : A <= B)
  proof: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

@[simp]

中文:
定理 relfinrank_inf_mul_relfinrank_of_le
  条件: (h : A <= B)
  证明: by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

@[simp]

Depends on / 依赖: relrank_inf_mul_relrank_of_le
-/
theorem relfinrank_inf_mul_relfinrank_of_le (h : A <= B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

@[simp]
/--
theorem `relrank_top_left` / 定理 `relrank_top_left`

English:
theorem relrank_top_left
  statement: relrank ⊤ A = 1
  proof: relrank_eq_one_of_le le_top

@[simp]

中文:
定理 relrank_top_left
  结论: relrank ⊤ A = 1
  证明: relrank_eq_one_of_le le_top

@[simp]

Depends on / 依赖: le_top, relrank_eq_one_of_le
-/
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
/--
theorem `relfinrank_top_left` / 定理 `relfinrank_top_left`

English:
theorem relfinrank_top_left
  statement: relfinrank ⊤ A = 1
  proof: relfinrank_eq_one_of_le le_top

@[simp]

中文:
定理 relfinrank_top_left
  结论: relfinrank ⊤ A = 1
  证明: relfinrank_eq_one_of_le le_top

@[simp]

Depends on / 依赖: le_top, relfinrank_eq_one_of_le
-/
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := relfinrank_eq_one_of_le le_top

@[simp]
/--
theorem `relrank_top_right` / 定理 `relrank_top_right`

English:
theorem relrank_top_right
  statement: relrank A ⊤ = Module.rank A E
  proof: by
  rw [← relrank_mul_rank_top (show A <= ⊤ from le_top)]; rw [IntermediateField.rank_top]; rw [mul_one]

@[simp]

中文:
定理 relrank_top_right
  结论: relrank A ⊤ = 模.rank A E
  证明: by
  rw [← relrank_mul_rank_top (show A <= ⊤ from le_top)]; rw [IntermediateField.rank_top]; rw [mul_one]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.rank_top, le_top, mul_one, rank_top, relrank_mul_rank_top
-/
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [← relrank_mul_rank_top (show A <= ⊤ from le_top)]; rw [IntermediateField.rank_top]; rw [mul_one]

@[simp]
/--
theorem `relfinrank_top_right` / 定理 `relfinrank_top_right`

English:
theorem relfinrank_top_right
  statement: relfinrank A ⊤ = finrank A E
  proof: by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]

中文:
定理 relfinrank_top_right
  结论: relfinrank A ⊤ = finrank A E
  证明: by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]

Depends on / 依赖: finrank, relfinrank_eq_toNat_relrank
-/
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]
/--
theorem `relrank_bot_left` / 定理 `relrank_bot_left`

English:
theorem relrank_bot_left
  statement: relrank ⊥ A = Module.rank F A
  proof: by
  rw [← rank_bot_mul_relrank (show ⊥ <= A from bot_le)]; rw [IntermediateField.rank_bot]; rw [one_mul]

@[simp]

中文:
定理 relrank_bot_left
  结论: relrank ⊥ A = 模.rank F A
  证明: by
  rw [← rank_bot_mul_relrank (show ⊥ <= A from bot_le)]; rw [IntermediateField.rank_bot]; rw [one_mul]

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.rank_bot, bot_le, one_mul, rank_bot, rank_bot_mul_relrank
-/
theorem relrank_bot_left : relrank ⊥ A = Module.rank F A := by
  rw [← rank_bot_mul_relrank (show ⊥ <= A from bot_le)]; rw [IntermediateField.rank_bot]; rw [one_mul]

@[simp]
/--
theorem `relfinrank_bot_left` / 定理 `relfinrank_bot_left`

English:
theorem relfinrank_bot_left
  statement: relfinrank ⊥ A = finrank F A
  proof: by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]

中文:
定理 relfinrank_bot_left
  结论: relfinrank ⊥ A = finrank F A
  证明: by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]

Depends on / 依赖: finrank, relfinrank_eq_toNat_relrank
-/
theorem relfinrank_bot_left : relfinrank ⊥ A = finrank F A := by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]
/--
theorem `relrank_bot_right` / 定理 `relrank_bot_right`

English:
theorem relrank_bot_right
  statement: relrank A ⊥ = 1
  proof: relrank_eq_one_of_le bot_le

@[simp]

中文:
定理 relrank_bot_right
  结论: relrank A ⊥ = 1
  证明: relrank_eq_one_of_le bot_le

@[simp]

Depends on / 依赖: bot_le, relrank_eq_one_of_le
-/
theorem relrank_bot_right : relrank A ⊥ = 1 := relrank_eq_one_of_le bot_le

@[simp]
/--
theorem `relfinrank_bot_right` / 定理 `relfinrank_bot_right`

English:
theorem relfinrank_bot_right
  statement: relfinrank A ⊥ = 1
  proof: relfinrank_eq_one_of_le bot_le

中文:
定理 relfinrank_bot_right
  结论: relfinrank A ⊥ = 1
  证明: relfinrank_eq_one_of_le bot_le

Depends on / 依赖: bot_le, relfinrank_eq_one_of_le
-/
theorem relfinrank_bot_right : relfinrank A ⊥ = 1 := relfinrank_eq_one_of_le bot_le

variable {A B} in
/--
theorem `relrank_dvd_of_le_left` / 定理 `relrank_dvd_of_le_left`

English:
theorem relrank_dvd_of_le_left
  given: (h : A <= B)
  statement: B.relrank C ∣ A.relrank C
  proof: dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

中文:
定理 relrank_dvd_of_le_left
  条件: (h : A <= B)
  结论: B.relrank C ∣ A.relrank C
  证明: dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

Depends on / 依赖: dvd_of_mul_left_eq, relrank_inf_mul_relrank_of_le
-/
theorem relrank_dvd_of_le_left (h : A <= B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

variable {A B} in
/--
theorem `relfinrank_dvd_of_le_left` / 定理 `relfinrank_dvd_of_le_left`

English:
theorem relfinrank_dvd_of_le_left
  given: (h : A <= B)
  statement: B.relfinrank C ∣ A.relfinrank C
  proof: dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

中文:
定理 relfinrank_dvd_of_le_left
  条件: (h : A <= B)
  结论: B.relfinrank C ∣ A.relfinrank C
  证明: dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

Depends on / 依赖: dvd_of_mul_left_eq, relfinrank_inf_mul_relfinrank_of_le
-/
theorem relfinrank_dvd_of_le_left (h : A <= B) : B.relfinrank C ∣ A.relfinrank C :=
  dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

end IntermediateField
