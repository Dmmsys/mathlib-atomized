/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
public import Mathlib.RingTheory.LinearDisjoint

/-!

# Linearly disjoint fields

This file contains basics about the linearly disjoint fields.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean`
and `Mathlib/RingTheory/LinearDisjoint.lean` for details.

## Main definitions

- `IntermediateField.LinearDisjoint`: an intermediate field `A` of `E / F`
  and an abstract field `L` between `E / F`
  (as a special case, two intermediate fields) are linearly disjoint over `F`,
  if they are linearly disjoint as subalgebras (`Subalgebra.LinearDisjoint`).

## Implementation notes

The `Subalgebra.LinearDisjoint` is stated for two `Subalgebra`s. The original design of
`IntermediateField.LinearDisjoint` is also stated for two `IntermediateField`s
(see `IntermediateField.linearDisjoint_iff'` for the original statement).
But it's probably useful if one of them can be generalized to an abstract field
(see <https://github.com/leanprover-community/mathlib4/pull/9651#discussion_r1464070324>).
This leads to the current design of `IntermediateField.LinearDisjoint`
which is for one `IntermediateField` and one abstract field.
It is not generalized to two abstract fields as this will break the dot notation.

## Main results

### Equivalent characterization of linear disjointness

- `IntermediateField.LinearDisjoint.linearIndependent_left`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
  linearly independent over `L`.

- `IntermediateField.LinearDisjoint.of_basis_left`:
  conversely, if there exists an `F`-basis of `A` which remains linearly independent over `L`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_right`:
  `IntermediateField.LinearDisjoint.linearIndependent_right'`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
  linearly independent over `A`.

- `IntermediateField.LinearDisjoint.of_basis_right`:
  `IntermediateField.LinearDisjoint.of_basis_right'`:
  conversely, if there exists an `F`-basis of `L` which remains linearly independent over `A`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_mul`:
  `IntermediateField.LinearDisjoint.linearIndependent_mul'`:
  if `A` and `L` are linearly disjoint, then for any family of
  `F`-linearly independent elements `{ a_i }` of `A`, and any family of
  `F`-linearly independent elements `{ b_j }` of `L`, the family `{ a_i * b_j }` in `S` is
  also `F`-linearly independent.

- `IntermediateField.LinearDisjoint.of_basis_mul`:
  `IntermediateField.LinearDisjoint.of_basis_mul'`:
  conversely, if `{ a_i }` is an `F`-basis of `A`, if `{ b_j }` is an `F`-basis of `L`,
  such that the family `{ a_i * b_j }` in `E` is `F`-linearly independent,
  then `A` and `L` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `IntermediateField.LinearDisjoint.isDomain'`,
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a domain if and only if there exists a field extension of `F` that `A` and `B`
  embed into with linearly disjoint images.

- `IntermediateField.LinearDisjoint.isField_of_forall`,
  `IntermediateField.LinearDisjoint.of_isField'`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a field if and only if for any field extension of `F` that `A` and `B` embed into, their
  images are linearly disjoint.

- `Algebra.TensorProduct.isField_of_isAlgebraic`:
  if `E` and `K` are field extensions of `F`, one of them is algebraic, and
  `E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field.
  See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earlier file).

- `IntermediateField.LinearDisjoint.isField_of_isAlgebraic`,
  `IntermediateField.LinearDisjoint.isField_of_isAlgebraic'`:
  if `A` and `B` are field extensions of `F`, one of them is algebraic, such that they are linearly
  disjoint (more generally, if there exists a field extension of `F` that they embed into with
  linearly disjoint images), then `A ⊗[F] B` is a field.

### Other main results

- `IntermediateField.LinearDisjoint.symm`, `IntermediateField.linearDisjoint_comm`:
  linear disjointness is symmetric.

- `IntermediateField.LinearDisjoint.map`:
  linear disjointness is preserved by algebra homomorphism.

- `IntermediateField.LinearDisjoint.rank_sup`,
  `IntermediateField.LinearDisjoint.finrank_sup`:
  if `A` and `B` are linearly disjoint,
  then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `IntermediateField.LinearDisjoint.of_finrank_sup`:
  conversely, if `A` and `B` are finite extensions,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.of_finrank_coprime`:
  if the rank of `A` and `B` are coprime,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, then they are disjoint.

- `IntermediateField.LinearDisjoint.algEquiv_of_isAlgebraic`:
  linear disjointness is preserved by isomorphisms, provided that one of the field is algebraic.

## Tags

linearly disjoint, linearly independent, tensor product

-/

@[expose] public section

open scoped TensorProduct

open Module IntermediateField

noncomputable section

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/--
Definition of `LinearDisjoint` / `LinearDisjoint` 的定义

English:
abbreviation LinearDisjoint
  signature: : Prop
  body: A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range

中文:
缩写 LinearDisjoint
  签名: : 命题
  定义体: A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range
-/
protected abbrev LinearDisjoint : Prop :=
  A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range

/--
theorem `linearDisjoint_iff` / 定理 `linearDisjoint_iff`

English:
theorem linearDisjoint_iff
  proof: Iff.rfl

中文:
定理 linearDisjoint_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearDisjoint_iff :
    A.LinearDisjoint L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range :=
  Iff.rfl

variable {A B L}

/--
theorem `linearDisjoint_iff'` / 定理 `linearDisjoint_iff'`

English:
theorem linearDisjoint_iff'
  proof: by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

中文:
定理 linearDisjoint_iff'
  证明: by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

Depends on / 依赖: linearDisjoint_iff
-/
theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

/--
theorem `LinearDisjoint.symm` / 定理 `LinearDisjoint.symm`

English:
theorem LinearDisjoint.symm
  given: (H : A.LinearDisjoint B)
  statement: B.LinearDisjoint A
  proof: linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

中文:
定理 LinearDisjoint.symm
  条件: (H : A.LinearDisjoint B)
  结论: B.LinearDisjoint A
  证明: linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

Depends on / 依赖: linearDisjoint_iff
-/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

/--
theorem `linearDisjoint_comm` / 定理 `linearDisjoint_comm`

English:
theorem linearDisjoint_comm
  statement: A.LinearDisjoint B ↔ B.LinearDisjoint A
  proof: ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

中文:
定理 linearDisjoint_comm
  结论: A.LinearDisjoint B ↔ B.LinearDisjoint A
  证明: ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

Depends on / 依赖: LinearDisjoint, LinearDisjoint.symm
-/
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

section

variable {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]

/--
theorem `LinearDisjoint.symm'` / 定理 `LinearDisjoint.symm'`

English:
theorem LinearDisjoint.symm'
  given: (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L')
  proof: Subalgebra.LinearDisjoint.symm H

中文:
定理 LinearDisjoint.symm'
  条件: (H : (标量塔.toAlgHom F L E).fieldRange.LinearDisjoint L')
  证明: Subalgebra.LinearDisjoint.symm H

Depends on / 依赖: LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.symm
-/
theorem LinearDisjoint.symm' (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L') :
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.symm H

/--
theorem `linearDisjoint_comm'` / 定理 `linearDisjoint_comm'`

English:
theorem linearDisjoint_comm'
  proof: ⟨LinearDisjoint.symm', LinearDisjoint.symm'⟩

中文:
定理 linearDisjoint_comm'
  证明: ⟨LinearDisjoint.symm', LinearDisjoint.symm'⟩

Depends on / 依赖: LinearDisjoint, LinearDisjoint.symm
-/
theorem linearDisjoint_comm' :
    (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L' ↔
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  ⟨LinearDisjoint.symm', LinearDisjoint.symm'⟩

end

namespace LinearDisjoint

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: (H : A.LinearDisjoint B) {K : Type*} [Field K] [Algebra F K]
  proof: linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).map f f.injective)

中文:
定理 map
  结论: (H : A.LinearDisjoint B) {K : 类型} [域 K] [代数 F K]
  证明: linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).map f f.injective)

Depends on / 依赖: f.injective, injective, linearDisjoint_iff
-/
theorem map (H : A.LinearDisjoint B) {K : Type*} [Field K] [Algebra F K]
    (f : E ->ₐ[F] K) : (A.map f).LinearDisjoint (B.map f) :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).map f f.injective)

/--
theorem `map'` / 定理 `map'`

English:
theorem map'
  statement: (H : A.LinearDisjoint L) (K : Type*) [Field K] [Algebra F K] [Algebra L K]
  proof: by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  rw [← AlgHom.range_comp] at this
  convert! this
  ext; exact IsScalarTower.algebraMap_apply L E K _

中文:
定理 map'
  结论: (H : A.LinearDisjoint L) (K : 类型) [域 K] [代数 F K] [代数 L K]
  证明: by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  rw [← AlgHom.range_comp] at this
  convert! this
  ext; exact IsScalarTower.algebraMap_apply L E K _

Depends on / 依赖: AlgHom, AlgHom.range_comp, H.map, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.toAlgHom, RingHom, RingHom.injective, algebraMap_apply, convert, injective, linearDisjoint_iff, range_comp, toAlgHom
-/
theorem map' (H : A.LinearDisjoint L) (K : Type*) [Field K] [Algebra F K] [Algebra L K]
    [IsScalarTower F L K] [Algebra E K] [IsScalarTower F E K] [IsScalarTower L E K] :
    (A.map (IsScalarTower.toAlgHom F E K)).LinearDisjoint L := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  rw [← AlgHom.range_comp] at this
  convert! this
  ext; exact IsScalarTower.algebraMap_apply L E K _

/--
theorem `map''` / 定理 `map''`

English:
theorem map''
  statement: {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]
  proof: by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  simp_rw [AlgHom.fieldRange_toSubalgebra, ← AlgHom.range_comp] at this
  rw [AlgHom.fieldRange_toSubalgebra]
  convert! this <;> (ext; exact IsScalarTower.algebraMap_apply _ E K _)

中文:
定理 map''
  结论: {L' : 类型} [域 L'] [代数 F L'] [代数 L' E] [标量塔 F L' E]
  证明: by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  simp_rw [AlgHom.fieldRange_toSubalgebra, ← AlgHom.range_comp] at this
  rw [AlgHom.fieldRange_toSubalgebra]
  convert! this <;> (ext; exact IsScalarTower.algebraMap_apply _ E K _)

Depends on / 依赖: AlgHom, AlgHom.fieldRange_toSubalgebra, AlgHom.range_comp, H.map, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.toAlgHom, RingHom, RingHom.injective, algebraMap_apply, convert, fieldRange_toSubalgebra, injective, linearDisjoint_iff, range_comp, simp_rw, toAlgHom
-/
theorem map'' {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]
    (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L')
    (K : Type*) [Field K] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra L' K] [IsScalarTower F L' K] [Algebra E K] [IsScalarTower F E K]
    [IsScalarTower L E K] [IsScalarTower L' E K] :
    (IsScalarTower.toAlgHom F L K).fieldRange.LinearDisjoint L' := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  simp_rw [AlgHom.fieldRange_toSubalgebra, ← AlgHom.range_comp] at this
  rw [AlgHom.fieldRange_toSubalgebra]
  convert! this <;> (ext; exact IsScalarTower.algebraMap_apply _ E K _)

variable (A) in
/--
theorem `self_right` / 定理 `self_right`

English:
theorem self_right
  statement: A.LinearDisjoint F
  proof: Subalgebra.LinearDisjoint.bot_right _

中文:
定理 self_right
  结论: A.LinearDisjoint F
  证明: Subalgebra.LinearDisjoint.bot_right _

Depends on / 依赖: LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.bot_right, bot_right
-/
theorem self_right : A.LinearDisjoint F := Subalgebra.LinearDisjoint.bot_right _

variable (A) in
/--
theorem `bot_right` / 定理 `bot_right`

English:
theorem bot_right
  statement: A.LinearDisjoint (⊥ : IntermediateField F E)
  proof: linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)

中文:
定理 bot_right
  结论: A.LinearDisjoint (⊥ : 中间域 F E)
  证明: linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)

Depends on / 依赖: LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.bot_right, bot_right, linearDisjoint_iff
-/
theorem bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)

variable (F E L) in
/--
theorem `bot_left` / 定理 `bot_left`

English:
theorem bot_left
  statement: (⊥ : IntermediateField F E).LinearDisjoint L
  proof: Subalgebra.LinearDisjoint.bot_left _

中文:
定理 bot_left
  结论: (⊥ : 中间域 F E).LinearDisjoint L
  证明: Subalgebra.LinearDisjoint.bot_left _

Depends on / 依赖: LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.bot_left, bot_left
-/
theorem bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  Subalgebra.LinearDisjoint.bot_left _

/--
theorem `linearIndependent_left` / 定理 `linearIndependent_left`

English:
theorem linearIndependent_left
  statement: (H : A.LinearDisjoint L)
  proof: (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)

中文:
定理 linearIndependent_left
  结论: (H : A.LinearDisjoint L)
  证明: (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.smul_def, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.linearIndependent_left_of_flat, linearIndependent_left_of_flat, map_of_injective_injective, ofInjectiveField, simp_rw, smul_def, toAlgHom
-/
theorem linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι -> A} (ha : LinearIndependent F a) : LinearIndependent L (A.val ∘ a) :=
  (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)

/--
theorem `of_basis_left` / 定理 `of_basis_left`

English:
theorem of_basis_left
  statement: {ι : Type*} (a : Basis ι F A)
  proof: Subalgebra.LinearDisjoint.of_basis_left _ _ a H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)

中文:
定理 of_basis_left
  结论: {ι : 类型} (a : 基 ι F A)
  证明: Subalgebra.LinearDisjoint.of_basis_left _ _ a H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, AlgEquiv, AlgEquiv.ofInjectiveField, AlgEquiv.surjective, Algebra, Algebra.smul_def, H.map_of_surjective_injective, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_basis_left, map_of_surjective_injective, ofInjectiveField, of_basis_left, simp_rw, smul_def, surjective, toAlgHom
-/
theorem of_basis_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) : A.LinearDisjoint L :=
Subalgebra.LinearDisjoint.of_basis_left _ _ a H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)

/--
theorem `linearIndependent_right` / 定理 `linearIndependent_right`

English:
theorem linearIndependent_right
  statement: (H : A.LinearDisjoint B)
  proof: (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb

中文:
定理 linearIndependent_right
  结论: (H : A.LinearDisjoint B)
  证明: (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb

Depends on / 依赖: linearDisjoint_iff, linearIndependent_right_of_flat
-/
theorem linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι -> B} (hb : LinearIndependent F b) : LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb

/--
Definition of `basisOfBasisRight` / `basisOfBasisRight` 的定义

English:
definition basisOfBasisRight
  signature: (H : A.LinearDisjoint B)
  body: (linearDisjoint_iff'.mp H).basisOfBasisRight H' b

@[simp]

中文:
定义 basisOfBasisRight
  签名: (H : A.LinearDisjoint B)
  定义体: (linearDisjoint_iff'.mp H).basisOfBasisRight H' b

@[simp]

Depends on / 依赖: basisOfBasisRight, linearDisjoint_iff
-/
noncomputable def basisOfBasisRight (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) :
    Basis ι A E :=
  (linearDisjoint_iff'.mp H).basisOfBasisRight H' b

@[simp]
/--
theorem `basisOfBasisRight_apply` / 定理 `basisOfBasisRight_apply`

English:
theorem basisOfBasisRight_apply
  statement: (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
  proof: (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_apply H' b i

中文:
定理 basisOfBasisRight_apply
  结论: (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
  证明: (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_apply H' b i

Depends on / 依赖: algebraMap_basisOfBasisRight_apply, linearDisjoint_iff
-/
theorem basisOfBasisRight_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
    {ι : Type*} (b : Basis ι F B) (i : ι) :
    H.basisOfBasisRight H' b i = algebraMap B E (b i) :=
  (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_apply H' b i

/--
theorem `algebraMap_basisOfBasisRight_repr_apply` / 定理 `algebraMap_basisOfBasisRight_repr_apply`

English:
theorem algebraMap_basisOfBasisRight_repr_apply
  statement: (H : A.LinearDisjoint B)
  proof: (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_repr_apply H' b x i

中文:
定理 algebraMap_basisOfBasisRight_repr_apply
  结论: (H : A.LinearDisjoint B)
  证明: (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_repr_apply H' b x i

Depends on / 依赖: algebraMap_basisOfBasisRight_repr_apply, linearDisjoint_iff
-/
theorem algebraMap_basisOfBasisRight_repr_apply (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) (x : B) (i : ι) :
    algebraMap A E ((H.basisOfBasisRight H' b).repr x i) = algebraMap F E (b.repr x i) :=
  (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_repr_apply H' b x i

/--
Definition of `basisOfBasisLeft` / `basisOfBasisLeft` 的定义

English:
definition basisOfBasisLeft
  signature: (H : A.LinearDisjoint B)
  body: (linearDisjoint_iff'.mp H).basisOfBasisLeft H' b

@[simp]

中文:
定义 basisOfBasisLeft
  签名: (H : A.LinearDisjoint B)
  定义体: (linearDisjoint_iff'.mp H).basisOfBasisLeft H' b

@[simp]

Depends on / 依赖: basisOfBasisLeft, linearDisjoint_iff
-/
noncomputable def basisOfBasisLeft (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) :
    Basis ι B E :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft H' b

@[simp]
/--
theorem `basisOfBasisLeft_apply` / 定理 `basisOfBasisLeft_apply`

English:
theorem basisOfBasisLeft_apply
  statement: (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
  proof: (linearDisjoint_iff'.mp H).basisOfBasisLeft_apply H' b i

中文:
定理 basisOfBasisLeft_apply
  结论: (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
  证明: (linearDisjoint_iff'.mp H).basisOfBasisLeft_apply H' b i

Depends on / 依赖: basisOfBasisLeft_apply, linearDisjoint_iff
-/
theorem basisOfBasisLeft_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
    {ι : Type*} (b : Basis ι F A) (i : ι) :
    H.basisOfBasisLeft H' b i = algebraMap A E (b i) :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft_apply H' b i

/--
theorem `basisOfBasisLeft_repr_apply` / 定理 `basisOfBasisLeft_repr_apply`

English:
theorem basisOfBasisLeft_repr_apply
  statement: (H : A.LinearDisjoint B)
  proof: (linearDisjoint_iff'.mp H).basisOfBasisLeft_repr_apply H' b x i

中文:
定理 basisOfBasisLeft_repr_apply
  结论: (H : A.LinearDisjoint B)
  证明: (linearDisjoint_iff'.mp H).basisOfBasisLeft_repr_apply H' b x i

Depends on / 依赖: basisOfBasisLeft_repr_apply, linearDisjoint_iff
-/
theorem basisOfBasisLeft_repr_apply (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) (x : A) (i : ι) :
    algebraMap B E ((H.basisOfBasisLeft H' b).repr x i) = algebraMap F E (b.repr x i) :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft_repr_apply H' b x i

/--
theorem `of_basis_right` / 定理 `of_basis_right`

English:
theorem of_basis_right
  statement: {ι : Type*} (b : Basis ι F B)
  proof: linearDisjoint_iff'.2 (.of_basis_right _ _ b H)

中文:
定理 of_basis_right
  结论: {ι : 类型} (b : 基 ι F B)
  证明: linearDisjoint_iff'.2 (.of_basis_right _ _ b H)

Depends on / 依赖: linearDisjoint_iff, of_basis_right
-/
theorem of_basis_right {ι : Type*} (b : Basis ι F B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_right _ _ b H)

/--
theorem `linearIndependent_right'` / 定理 `linearIndependent_right'`

English:
theorem linearIndependent_right'
  statement: (H : A.LinearDisjoint L) {ι : Type*} {b : ι -> L}
  proof: by
apply Subalgebra.LinearDisjoint.linearIndependent_right_of_flat H hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

中文:
定理 linearIndependent_right'
  结论: (H : A.LinearDisjoint L) {ι : 类型} {b : ι -> L}
  证明: by
apply Subalgebra.LinearDisjoint.linearIndependent_right_of_flat H hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.linearIndependent_right_of_flat, hb.map, linearIndependent_right_of_flat, ofInjectiveField, toAlgHom, toLinearEquiv, toLinearEquiv.ker
-/
theorem linearIndependent_right' (H : A.LinearDisjoint L) {ι : Type*} {b : ι -> L}
    (hb : LinearIndependent F b) : LinearIndependent A (algebraMap L E ∘ b) := by
apply Subalgebra.LinearDisjoint.linearIndependent_right_of_flat H hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

/--
theorem `of_basis_right'` / 定理 `of_basis_right'`

English:
theorem of_basis_right'
  statement: {ι : Type*} (b : Basis ι F L)
  proof: Subalgebra.LinearDisjoint.of_basis_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

中文:
定理 of_basis_right'
  结论: {ι : 类型} (b : 基 ι F L)
  证明: Subalgebra.LinearDisjoint.of_basis_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_basis_right, b.map, ofInjectiveField, of_basis_right, toAlgHom, toLinearEquiv
-/
theorem of_basis_right' {ι : Type*} (b : Basis ι F L)
    (H : LinearIndependent A (algebraMap L E ∘ b)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

/--
theorem `linearIndependent_mul` / 定理 `linearIndependent_mul`

English:
theorem linearIndependent_mul
  statement: (H : A.LinearDisjoint B) {κ ι : Type*} {a : κ -> A} {b : ι -> B}
  proof: (linearDisjoint_iff'.1 H).linearIndependent_mul_of_flat_left ha hb

中文:
定理 linearIndependent_mul
  结论: (H : A.LinearDisjoint B) {κ ι : 类型} {a : κ -> A} {b : ι -> B}
  证明: (linearDisjoint_iff'.1 H).linearIndependent_mul_of_flat_left ha hb

Depends on / 依赖: linearDisjoint_iff, linearIndependent_mul_of_flat_left
-/
theorem linearIndependent_mul (H : A.LinearDisjoint B) {κ ι : Type*} {a : κ -> A} {b : ι -> B}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) => (a i.1).1 * (b i.2).1 :=
  (linearDisjoint_iff'.1 H).linearIndependent_mul_of_flat_left ha hb

/--
theorem `linearIndependent_mul'` / 定理 `linearIndependent_mul'`

English:
theorem linearIndependent_mul'
  statement: (H : A.LinearDisjoint L) {κ ι : Type*} {a : κ -> A} {b : ι -> L}
  proof: by
apply Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

中文:
定理 linearIndependent_mul'
  结论: (H : A.LinearDisjoint L) {κ ι : 类型} {a : κ -> A} {b : ι -> L}
  证明: by
apply Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left, hb.map, linearIndependent_mul_of_flat_left, ofInjectiveField, toAlgHom, toLinearEquiv, toLinearEquiv.ker
-/
theorem linearIndependent_mul' (H : A.LinearDisjoint L) {κ ι : Type*} {a : κ -> A} {b : ι -> L}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) => (a i.1).1 * algebraMap L E (b i.2) := by
apply Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

/--
theorem `of_basis_mul` / 定理 `of_basis_mul`

English:
theorem of_basis_mul
  statement: {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
  proof: linearDisjoint_iff'.2 (.of_basis_mul _ _ a b H)

中文:
定理 of_basis_mul
  结论: {κ ι : 类型} (a : 基 κ F A) (b : 基 ι F B)
  证明: linearDisjoint_iff'.2 (.of_basis_mul _ _ a b H)

Depends on / 依赖: linearDisjoint_iff, of_basis_mul
-/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
    (H : LinearIndependent F fun (i : κ × ι) => (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_mul _ _ a b H)

/--
theorem `of_basis_mul'` / 定理 `of_basis_mul'`

English:
theorem of_basis_mul'
  statement: {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
  proof: Subalgebra.LinearDisjoint.of_basis_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

中文:
定理 of_basis_mul'
  结论: {κ ι : 类型} (a : 基 κ F A) (b : 基 ι F L)
  证明: Subalgebra.LinearDisjoint.of_basis_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_basis_mul, b.map, ofInjectiveField, of_basis_mul, toAlgHom, toLinearEquiv
-/
theorem of_basis_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
    (H : LinearIndependent F fun (i : κ × ι) => (a i.1).1 * algebraMap L E (b i.2)) :
    A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

/--
theorem `of_le_left` / 定理 `of_le_left`

English:
theorem of_le_left
  statement: {A' : IntermediateField F E} (H : A.LinearDisjoint L)
  proof: Subalgebra.LinearDisjoint.of_le_left_of_flat H h

中文:
定理 of_le_left
  结论: {A' : 中间域 F E} (H : A.LinearDisjoint L)
  证明: Subalgebra.LinearDisjoint.of_le_left_of_flat H h

Depends on / 依赖: LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_le_left_of_flat, of_le_left_of_flat
-/
theorem of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (h : A' <= A) : A'.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_le_left_of_flat H h

/--
theorem `of_le_right` / 定理 `of_le_right`

English:
theorem of_le_right
  statement: {B' : IntermediateField F E} (H : A.LinearDisjoint B)
  proof: linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

中文:
定理 of_le_right
  结论: {B' : 中间域 F E} (H : A.LinearDisjoint B)
  证明: linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

Depends on / 依赖: linearDisjoint_iff, of_le_right_of_flat
-/
theorem of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' <= B) : A.LinearDisjoint B' :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

/--
theorem `of_le_right'` / 定理 `of_le_right'`

English:
theorem of_le_right'
  statement: (H : A.LinearDisjoint L) (L' : Type*) [Field L']
  proof: by
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat H ?_
  convert! AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext; exact IsScalarTower.algebraMap_apply L' L E _

中文:
定理 of_le_right'
  结论: (H : A.LinearDisjoint L) (L' : 类型) [域 L']
  证明: by
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat H ?_
  convert! AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext; exact IsScalarTower.algebraMap_apply L' L E _

Depends on / 依赖: AlgHom, AlgHom.range_comp_le_range, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_le_right_of_flat, algebraMap_apply, convert, of_le_right_of_flat, range_comp_le_range, toAlgHom
-/
theorem of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A.LinearDisjoint L' := by
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat H ?_
  convert! AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext; exact IsScalarTower.algebraMap_apply L' L E _

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  statement: {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
  proof: .of_le_right hB H.of_le_left hA

中文:
定理 of_le
  结论: {A' B' : 中间域 F E} (H : A.LinearDisjoint B)
  证明: .of_le_right hB H.of_le_left hA

Depends on / 依赖: H.of_le_left, of_le_left, of_le_right
-/
theorem of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' <= A) (hB : B' <= B) : A'.LinearDisjoint B' :=
.of_le_right hB H.of_le_left hA

/--
theorem `of_le'` / 定理 `of_le'`

English:
theorem of_le'
  statement: {A' : IntermediateField F E} (H : A.LinearDisjoint L)
  proof: .of_le_right' L' H.of_le_left hA

中文:
定理 of_le'
  结论: {A' : 中间域 F E} (H : A.LinearDisjoint L)
  证明: .of_le_right' L' H.of_le_left hA

Depends on / 依赖: H.of_le_left, of_le_left, of_le_right
-/
theorem of_le' {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (hA : A' <= A) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A'.LinearDisjoint L' :=
.of_le_right' L' H.of_le_left hA

/--
theorem `inf_eq_bot` / 定理 `inf_eq_bot`

English:
theorem inf_eq_bot
  given: (H : A.LinearDisjoint B)
  proof: toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot

中文:
定理 inf_eq_bot
  条件: (H : A.LinearDisjoint B)
  证明: toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot

Depends on / 依赖: inf_eq_bot, linearDisjoint_iff, toSubalgebra_injective
-/
theorem inf_eq_bot (H : A.LinearDisjoint B) :
    A ⊓ B = ⊥ := toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot

/--
theorem `eq_bot_of_self` / 定理 `eq_bot_of_self`

English:
theorem eq_bot_of_self
  given: (H : A.LinearDisjoint A)
  statement: A = ⊥
  proof: inf_idem A ▸ H.inf_eq_bot

中文:
定理 eq_bot_of_self
  条件: (H : A.LinearDisjoint A)
  结论: A = ⊥
  证明: inf_idem A ▸ H.inf_eq_bot

Depends on / 依赖: H.inf_eq_bot, inf_eq_bot, inf_idem
-/
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  inf_idem A ▸ H.inf_eq_bot

/--
theorem `rank_sup` / 定理 `rank_sup`

English:
theorem rank_sup
  given: (H : A.LinearDisjoint B)
  proof: have h := le_sup_toSubalgebra A B
(rank_sup_le A B).antisymm
(linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

中文:
定理 rank_sup
  条件: (H : A.LinearDisjoint B)
  证明: have h := le_sup_toSubalgebra A B
(rank_sup_le A B).antisymm
(linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

Depends on / 依赖: Subalgebra, Subalgebra.inclusion, Subalgebra.inclusion_injective, antisymm, inclusion, inclusion_injective, le_sup_toSubalgebra, linearDisjoint_iff, rank_le_of_injective, rank_sup_le, rank_sup_of_free, rank_sup_of_free.ge.trans, toLinearMap, toLinearMap.rank_le_of_injective
-/
theorem rank_sup (H : A.LinearDisjoint B) :
    Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B :=
  have h := le_sup_toSubalgebra A B
(rank_sup_le A B).antisymm
(linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

/--
theorem `finrank_sup` / 定理 `finrank_sup`

English:
theorem finrank_sup
  given: (H : A.LinearDisjoint B)
  statement: finrank F ↥(A ⊔ B) = finrank F A * finrank F B
  proof: by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup))

中文:
定理 finrank_sup
  条件: (H : A.LinearDisjoint B)
  结论: finrank F ↥(A ⊔ B) = finrank F A * finrank F B
  证明: by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup))

Depends on / 依赖: Cardinal, Cardinal.toNat, H.rank_sup, map_mul, rank_sup
-/
theorem finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
  simpa only [map_mul] using! congr(Cardinal.toNat $(H.rank_sup))

/--
theorem `of_finrank_sup` / 定理 `of_finrank_sup`

English:
theorem of_finrank_sup
  statement: [FiniteDimensional F A] [FiniteDimensional F B]
  proof: linearDisjoint_iff'.2 .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])

中文:
定理 of_finrank_sup
  结论: [有限维 F A] [有限维 F B]
  证明: linearDisjoint_iff'.2 .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])

Depends on / 依赖: linearDisjoint_iff, of_finrank_sup_of_free, sup_toSubalgebra_of_left
-/
theorem of_finrank_sup [FiniteDimensional F A] [FiniteDimensional F B]
    (H : finrank F ↥(A ⊔ B) = finrank F A * finrank F B) : A.LinearDisjoint B :=
linearDisjoint_iff'.2 .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])

/--
theorem `finrank_left_eq_finrank` / 定理 `finrank_left_eq_finrank`

English:
theorem finrank_left_eq_finrank
  given: [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  proof: by
  have := h₁.finrank_sup
  rwa [h₂, finrank_top', ← finrank_mul_finrank F A E, mul_right_inj' finrank_pos.ne'] at this

中文:
定理 finrank_left_eq_finrank
  条件: [模.有限 F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  证明: by
  have := h₁.finrank_sup
  rwa [h₂, finrank_top', ← finrank_mul_finrank F A E, mul_right_inj' finrank_pos.ne'] at this

Depends on / 依赖: finrank_mul_finrank, finrank_pos, finrank_pos.ne, finrank_sup, finrank_top, mul_right_inj
-/
theorem finrank_left_eq_finrank [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) :
    finrank A E = finrank F B := by
  have := h₁.finrank_sup
  rwa [h₂, finrank_top', ← finrank_mul_finrank F A E, mul_right_inj' finrank_pos.ne'] at this

/--
theorem `finrank_right_eq_finrank` / 定理 `finrank_right_eq_finrank`

English:
theorem finrank_right_eq_finrank
  given: [Module.Finite F B] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  proof: h₁.symm.finrank_left_eq_finrank (by rwa [sup_comm])

中文:
定理 finrank_right_eq_finrank
  条件: [模.有限 F B] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  证明: h₁.symm.finrank_left_eq_finrank (by rwa [sup_comm])

Depends on / 依赖: finrank_left_eq_finrank, sup_comm, symm.finrank_left_eq_finrank
-/
theorem finrank_right_eq_finrank [Module.Finite F B] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) :
    finrank B E = finrank F A :=
  h₁.symm.finrank_left_eq_finrank (by rwa [sup_comm])

/--
theorem `of_inf_eq_bot_aux` / 定理 `of_inf_eq_bot_aux`

English:
theorem of_inf_eq_bot_aux
  statement: [IsGalois F A] [FiniteDimensional F E] (h₁ : A ⊔ B = ⊤)
  proof: by
  apply LinearDisjoint.of_finrank_sup
  rw [h₁]; rw [finrank_top']; rw [← Module.finrank_mul_finrank F B E]; rw [mul_comm]; rw [mul_left_inj'
    Module.finrank_pos.ne']
  have : IsGalois B E := IsGalois.sup_right A B h₁
  rw [← IsGalois.card_aut_eq_finrank]; rw [← IsGalois.card_aut_eq_finrank]
e

中文:
定理 of_inf_eq_bot_aux
  结论: [是Galois F A] [有限维 F E] (h₁ : A ⊔ B = ⊤)
  证明: by
  apply LinearDisjoint.of_finrank_sup
  rw [h₁]; rw [finrank_top']; rw [← Module.finrank_mul_finrank F B E]; rw [mul_comm]; rw [mul_left_inj'
    Module.finrank_pos.ne']
  have : IsGalois B E := IsGalois.sup_right A B h₁
  rw [← IsGalois.card_aut_eq_finrank]; rw [← IsGalois.card_aut_eq_finrank]
e
-/
private theorem of_inf_eq_bot_aux [IsGalois F A] [FiniteDimensional F E] (h₁ : A ⊔ B = ⊤)
    (h₂ : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  apply LinearDisjoint.of_finrank_sup
  rw [h₁]; rw [finrank_top']; rw [← Module.finrank_mul_finrank F B E]; rw [mul_comm]; rw [mul_left_inj'
    Module.finrank_pos.ne']
  have : IsGalois B E := IsGalois.sup_right A B h₁
  rw [← IsGalois.card_aut_eq_finrank]; rw [← IsGalois.card_aut_eq_finrank]
exact Nat.card_congr Equiv.ofBijective (restrictRestrictAlgEquivMapHom _ _ _ _)
    ⟨restrictRestrictAlgEquivMapHom_injective _ _ h₁,
      restrictRestrictAlgEquivMapHom_surjective _ _ h₂⟩

/--
theorem `of_inf_eq_bot` / 定理 `of_inf_eq_bot`

English:
theorem of_inf_eq_bot
  statement: [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
  proof: by
  let C : IntermediateField F E := A ⊔ B
  let A' : IntermediateField F C := A.restrict le_sup_left
  let B' : IntermediateField F C := B.restrict le_sup_right
  have hA : IntermediateField.map C.val A' = A := lift_restrict le_sup_left
  have hB : IntermediateField.map C.val B' = B := lift_restri

中文:
定理 of_inf_eq_bot
  结论: [是Galois F A] [有限维 F A] [有限维 F B]
  证明: by
  let C : IntermediateField F E := A ⊔ B
  let A' : IntermediateField F C := A.restrict le_sup_left
  let B' : IntermediateField F C := B.restrict le_sup_right
  have hA : IntermediateField.map C.val A' = A := lift_restrict le_sup_left
  have hB : IntermediateField.map C.val B' = B := lift_restri

Depends on / 依赖: A.restrict, B.restrict, C.val, IntermediateField, IntermediateField.map, LinearDisjoint, LinearDisjoint.map, le_sup_left, le_sup_right, lift_inj, lift_res, lift_restrict, lift_sup, lift_top, restrict
-/
theorem of_inf_eq_bot [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
    (h : A ⊓ B = ⊥) : A.LinearDisjoint B := by
  let C : IntermediateField F E := A ⊔ B
  let A' : IntermediateField F C := A.restrict le_sup_left
  let B' : IntermediateField F C := B.restrict le_sup_right
  have hA : IntermediateField.map C.val A' = A := lift_restrict le_sup_left
  have hB : IntermediateField.map C.val B' = B := lift_restrict le_sup_right
  suffices A'.LinearDisjoint B' from hA ▸ hB ▸ LinearDisjoint.map this C.val
  have h₁ : A' ⊔ B' = ⊤ := by
    rw [← lift_inj]; rw [lift_top]; rw [lift_sup]; rw [lift_restrict le_sup_left]; rw [lift_restrict le_sup_right]
  have h₂ : A' ⊓ B' = ⊥ := by
    rw [← lift_inj]; rw [lift_bot]; rw [lift_inf]; rw [lift_restrict le_sup_left]; rw [lift_restrict le_sup_right]; rw [h]
have : IsGalois F A' := IsGalois.of_algEquiv restrictAlgEquiv ..
  exact of_inf_eq_bot_aux h₁ h₂

@[simp]
/--
theorem `iff_inf_eq_bot` / 定理 `iff_inf_eq_bot`

English:
theorem iff_inf_eq_bot
  given: [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
  proof: ⟨fun h => inf_eq_bot h, fun h => of_inf_eq_bot h⟩

中文:
定理 iff_inf_eq_bot
  条件: [是Galois F A] [有限维 F A] [有限维 F B]
  证明: ⟨fun h => inf_eq_bot h, fun h => of_inf_eq_bot h⟩

Depends on / 依赖: inf_eq_bot, of_inf_eq_bot
-/
theorem iff_inf_eq_bot [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B] :
    A.LinearDisjoint B ↔ A ⊓ B = ⊥ :=
  ⟨fun h => inf_eq_bot h, fun h => of_inf_eq_bot h⟩

/--
theorem `adjoin_rank_eq_rank_left_of_isAlgebraic` / 定理 `adjoin_rank_eq_rank_left_of_isAlgebraic`

English:
theorem adjoin_rank_eq_rank_left_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: by
  refine Eq.trans ?_ (Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left H)
  set L' := (IsScalarTower.toAlgHom F L E).range
  let i : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin L' (

中文:
定理 adjoin_rank_eq_rank_left_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: by
  refine Eq.trans ?_ (Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left H)
  set L' := (IsScalarTower.toAlgHom F L E).range
  let i : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin L' (

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.adjoin, Algebra.adjoin_toSubsemiring, Eq.trans, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Set.mem_range, Subalgebra, Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left, adjoin, adjoin_intermediateField_toSubalgebra_of_isAlgebraic, adjoin_rank_eq_rank_left, adjoin_toSubsemiring, halg.symm, mem_range, ofInjectiveField, toAlgHom
-/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank L (adjoin L (A : Set E)) = Module.rank F A := by
  refine Eq.trans ?_ (Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left H)
  set L' := (IsScalarTower.toAlgHom F L E).range
  let i : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin L' (A : Set E)).toSubsemiring := by
    rw [adjoin_intermediateField_toSubalgebra_of_isAlgebraic _ _ halg.symm]; rw [Algebra.adjoin_toSubsemiring]; rw [Algebra.adjoin_toSubsemiring]
    congr 2
    ext x
    simp only [Set.mem_range, Subtype.exists]
    exact ⟨fun ⟨y, h⟩ => ⟨x, ⟨y, h⟩, rfl⟩, fun ⟨a, ⟨y, h1⟩, h2⟩ => ⟨y, h1.trans h2⟩⟩
  refine rank_eq_of_equiv_equiv i (RingEquiv.subsemiringCongr heq).toAddEquiv
    i.bijective fun a ⟨x, hx⟩ => ?_
  ext
  simp_rw [Algebra.smul_def]
  rfl

/--
theorem `adjoin_rank_eq_rank_left_of_isAlgebraic_left` / 定理 `adjoin_rank_eq_rank_left_of_isAlgebraic_left`

English:
theorem adjoin_rank_eq_rank_left_of_isAlgebraic_left
  statement: (H : A.LinearDisjoint L)
  proof: H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl ‹_›)

中文:
定理 adjoin_rank_eq_rank_left_of_isAlgebraic_left
  结论: (H : A.LinearDisjoint L)
  证明: H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl ‹_›)

Depends on / 依赖: H.adjoin_rank_eq_rank_left_of_isAlgebraic, adjoin_rank_eq_rank_left_of_isAlgebraic
-/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A :=
  H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl ‹_›)

/--
theorem `adjoin_rank_eq_rank_left_of_isAlgebraic_right` / 定理 `adjoin_rank_eq_rank_left_of_isAlgebraic_right`

English:
theorem adjoin_rank_eq_rank_left_of_isAlgebraic_right
  statement: (H : A.LinearDisjoint L)
  proof: H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inr ‹_›)

中文:
定理 adjoin_rank_eq_rank_left_of_isAlgebraic_right
  结论: (H : A.LinearDisjoint L)
  证明: H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inr ‹_›)

Depends on / 依赖: H.adjoin_rank_eq_rank_left_of_isAlgebraic, adjoin_rank_eq_rank_left_of_isAlgebraic
-/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A :=
  H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inr ‹_›)

/--
theorem `lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic` / 定理 `lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic`

English:
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: by
  rw [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.lift_rank_eq]; rw [Cardinal.lift_inj]; rw [← Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right H]
  set L' := (IsScalarTower.toAlgHom F L E).range
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
    

中文:
定理 lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: by
  rw [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.lift_rank_eq]; rw [Cardinal.lift_inj]; rw [← Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right H]
  set L' := (IsScalarTower.toAlgHom F L E).range
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
    

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.adjoin, Algebra.adjoin_toSubsemiring, Cardinal, Cardinal.lift_inj, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Set.union_c, Subalgebra, Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right, adjoin, adjoin_intermediateField_toSubalgebra_of_isAlgebraic, adjoin_rank_eq_rank_right, adjoin_toSubsemiring, halg.symm, lift_inj, lift_rank_eq
-/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) := by
  rw [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.lift_rank_eq]; rw [Cardinal.lift_inj]; rw [← Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right H]
  set L' := (IsScalarTower.toAlgHom F L E).range
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin A (L' : Set E)).toSubsemiring := by
    rw [adjoin_intermediateField_toSubalgebra_of_isAlgebraic _ _ halg.symm]; rw [Algebra.adjoin_toSubsemiring]; rw [Algebra.adjoin_toSubsemiring]; rw [Set.union_comm]
    congr 2
    ext x
    simp
  refine rank_eq_of_equiv_equiv (RingHom.id A) (RingEquiv.subsemiringCongr heq).toAddEquiv
    Function.bijective_id fun ⟨a, ha⟩ ⟨x, hx⟩ => ?_
  ext
  simp_rw [Algebra.smul_def]
  rfl

/--
theorem `lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left` / 定理 `lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left`

English:
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left
  statement: (H : A.LinearDisjoint L)
  proof: H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inl ‹_›)

中文:
定理 lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left
  结论: (H : A.LinearDisjoint L)
  证明: H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inl ‹_›)

Depends on / 依赖: H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic, lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic
-/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) :=
  H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inl ‹_›)

/--
theorem `lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right` / 定理 `lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right`

English:
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right
  statement: (H : A.LinearDisjoint L)
  proof: H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inr ‹_›)

中文:
定理 lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right
  结论: (H : A.LinearDisjoint L)
  证明: H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inr ‹_›)

Depends on / 依赖: H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic, lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic
-/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) :=
  H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inr ‹_›)

/--
theorem `lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic` / 定理 `lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic`

English:
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: by
  rw [← H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg]; rw [← Cardinal.lift_mul]; rw [Cardinal.lift_inj]
  exact rank_mul_rank A (extendScalars
    (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E))) E

中文:
定理 lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: by
  rw [← H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg]; rw [← Cardinal.lift_mul]; rw [Cardinal.lift_inj]
  exact rank_mul_rank A (extendScalars
    (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E))) E

Depends on / 依赖: Cardinal, Cardinal.lift_inj, Cardinal.lift_mul, H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic, adjoin, extendScalars, lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic, lift_inj, lift_mul, rank_mul_rank, restrictScalars, subset_adjoin
-/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) := by
  rw [← H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg]; rw [← Cardinal.lift_mul]; rw [Cardinal.lift_inj]
  exact rank_mul_rank A (extendScalars
    (show A <= (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E))) E

/--
theorem `lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left` / 定理 `lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left`

English:
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  statement: (H : A.LinearDisjoint L)
  proof: H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

中文:
定理 lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  结论: (H : A.LinearDisjoint L)
  证明: H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

Depends on / 依赖: H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic, lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic
-/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) :=
  H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

/--
theorem `lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right` / 定理 `lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right`

English:
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right
  statement: (H : A.LinearDisjoint L)
  proof: H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

中文:
定理 lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right
  结论: (H : A.LinearDisjoint L)
  证明: H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

Depends on / 依赖: H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic, lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic
-/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) :=
  H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

section

variable {L : Type v} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/--
theorem `adjoin_rank_eq_rank_right_of_isAlgebraic` / 定理 `adjoin_rank_eq_rank_right_of_isAlgebraic`

English:
theorem adjoin_rank_eq_rank_right_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: by
  simpa only [Cardinal.lift_id] using H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg

中文:
定理 adjoin_rank_eq_rank_right_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: by
  simpa only [Cardinal.lift_id] using H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg

Depends on / 依赖: Cardinal, Cardinal.lift_id, H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic, lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic, lift_id
-/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank A (extendScalars (show A <= (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L := by
  simpa only [Cardinal.lift_id] using H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg

/--
theorem `adjoin_rank_eq_rank_right_of_isAlgebraic_left` / 定理 `adjoin_rank_eq_rank_right_of_isAlgebraic_left`

English:
theorem adjoin_rank_eq_rank_right_of_isAlgebraic_left
  statement: (H : A.LinearDisjoint L)
  proof: H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inl ‹_›)

中文:
定理 adjoin_rank_eq_rank_right_of_isAlgebraic_left
  结论: (H : A.LinearDisjoint L)
  证明: H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inl ‹_›)

Depends on / 依赖: H.adjoin_rank_eq_rank_right_of_isAlgebraic, adjoin_rank_eq_rank_right_of_isAlgebraic
-/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Module.rank A (extendScalars (show A <= (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L :=
  H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inl ‹_›)

/--
theorem `adjoin_rank_eq_rank_right_of_isAlgebraic_right` / 定理 `adjoin_rank_eq_rank_right_of_isAlgebraic_right`

English:
theorem adjoin_rank_eq_rank_right_of_isAlgebraic_right
  statement: (H : A.LinearDisjoint L)
  proof: H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inr ‹_›)

中文:
定理 adjoin_rank_eq_rank_right_of_isAlgebraic_right
  结论: (H : A.LinearDisjoint L)
  证明: H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inr ‹_›)

Depends on / 依赖: H.adjoin_rank_eq_rank_right_of_isAlgebraic, adjoin_rank_eq_rank_right_of_isAlgebraic
-/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Module.rank A (extendScalars (show A <= (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L :=
  H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inr ‹_›)

/--
theorem `rank_right_mul_adjoin_rank_eq_of_isAlgebraic` / 定理 `rank_right_mul_adjoin_rank_eq_of_isAlgebraic`

English:
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: by
  simpa only [Cardinal.lift_id] using H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic halg

中文:
定理 rank_right_mul_adjoin_rank_eq_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: by
  simpa only [Cardinal.lift_id] using H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic halg

Depends on / 依赖: Cardinal, Cardinal.lift_id, H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic, lift_id, lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic
-/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E := by
  simpa only [Cardinal.lift_id] using H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic halg

/--
theorem `rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left` / 定理 `rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left`

English:
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left
  statement: (H : A.LinearDisjoint L)
  proof: H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

中文:
定理 rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left
  结论: (H : A.LinearDisjoint L)
  证明: H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

Depends on / 依赖: H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic, rank_right_mul_adjoin_rank_eq_of_isAlgebraic
-/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E :=
  H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

/--
theorem `rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right` / 定理 `rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right`

English:
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right
  statement: (H : A.LinearDisjoint L)
  proof: H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

中文:
定理 rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right
  结论: (H : A.LinearDisjoint L)
  证明: H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

Depends on / 依赖: H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic, rank_right_mul_adjoin_rank_eq_of_isAlgebraic
-/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E :=
  H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

end

/--
theorem `of_finrank_coprime` / 定理 `of_finrank_coprime`

English:
theorem of_finrank_coprime
  given: (H : (finrank F A).Coprime (finrank F L))
  statement: A.LinearDisjoint L
  proof: letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
inferInstanceAs Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
letI : Field A.toSubalgebra := inferInstanceAs Field A
Subalgebra.LinearDisjoint.of_finrank_coprime_of_free by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toA

中文:
定理 of_finrank_coprime
  条件: (H : (finrank F A).Coprime (finrank F L))
  结论: A.LinearDisjoint L
  证明: letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
inferInstanceAs Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
letI : Field A.toSubalgebra := inferInstanceAs Field A
Subalgebra.LinearDisjoint.of_finrank_coprime_of_free by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toA

Depends on / 依赖: A.toSubalgebra, AlgEquiv, AlgEquiv.ofInjectiveField, AlgHom, AlgHom.fieldRange, AlgHom.range, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_finrank_coprime_of_free, fieldRange, finrank_eq, ofInjectiveField, of_finrank_coprime_of_free, toAlgHom, toLinearEquiv, toLinearEquiv.finrank_eq, toSubalgebra
-/
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDisjoint L :=
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
inferInstanceAs Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
letI : Field A.toSubalgebra := inferInstanceAs Field A
Subalgebra.LinearDisjoint.of_finrank_coprime_of_free by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H

/--
theorem `isDomain` / 定理 `isDomain`

English:
theorem isDomain
  given: (H : A.LinearDisjoint L)
  statement: IsDomain (A otimes[F] L)
  proof: have : IsDomain (A otimes[F] _) := Subalgebra.LinearDisjoint.isDomain H
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))).toMulEquiv.isDomain

中文:
定理 isDomain
  条件: (H : A.LinearDisjoint L)
  结论: 是整环 (A otimes[F] L)
  证明: have : IsDomain (A otimes[F] _) := Subalgebra.LinearDisjoint.isDomain H
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))).toMulEquiv.isDomain

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, AlgEquiv.refl, Algebra, Algebra.TensorProduct.congr, IsDomain, IsScalarTower, IsScalarTower.toAlgHom, LinearDisjoint, RingHom, RingHom.injective, Subalgebra, Subalgebra.LinearDisjoint.isDomain, TensorProduct, injective, isDomain, ofInjective, otimes, toAlgHom, toMulEquiv
-/
theorem isDomain (H : A.LinearDisjoint L) : IsDomain (A otimes[F] L) :=
  have : IsDomain (A otimes[F] _) := Subalgebra.LinearDisjoint.isDomain H
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))).toMulEquiv.isDomain

/--
theorem `isDomain'` / 定理 `isDomain'`

English:
theorem isDomain'
  statement: {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
  proof: by
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra] at H
  exact H.isDomain_of_injective fa.injective fb.injective

中文:
定理 isDomain'
  结论: {A B : 类型} [域 A] [代数 F A] [域 B] [代数 F B]
  证明: by
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra] at H
  exact H.isDomain_of_injective fa.injective fb.injective

Depends on / 依赖: AlgHom, AlgHom.fieldRange_toSubalgebra, H.isDomain_of_injective, fa.injective, fb.injective, fieldRange_toSubalgebra, injective, isDomain_of_injective, linearDisjoint_iff, simp_rw
-/
theorem isDomain' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
    {fa : A ->ₐ[F] E} {fb : B ->ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRange) :
    IsDomain (A otimes[F] B) := by
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra] at H
  exact H.isDomain_of_injective fa.injective fb.injective

/--
theorem `of_isField` / 定理 `of_isField`

English:
theorem of_isField
  given: (H : IsField (A otimes[F] L))
  statement: A.LinearDisjoint L
  proof: by
  apply Subalgebra.LinearDisjoint.of_isField
  -- need these otherwise the `exact` will stuck at typeclass
  have : SMulCommClass F A A := SMulCommClass.of_commMonoid F A A
  have : SMulCommClass F A.toSubalgebra A.toSubalgebra := ‹SMulCommClass F A A›
  let : Mul (A otimes[F] L) := Algebra.Tenso

中文:
定理 of_isField
  条件: (H : 是域 (A otimes[F] L))
  结论: A.LinearDisjoint L
  证明: by
  apply Subalgebra.LinearDisjoint.of_isField
  -- need these otherwise the `exact` will stuck at typeclass
  have : SMulCommClass F A A := SMulCommClass.of_commMonoid F A A
  have : SMulCommClass F A.toSubalgebra A.toSubalgebra := ‹SMulCommClass F A A›
  let : Mul (A otimes[F] L) := Algebra.Tenso

Depends on / 依赖: LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_isField, of_isField
-/
theorem of_isField (H : IsField (A otimes[F] L)) : A.LinearDisjoint L := by
  apply Subalgebra.LinearDisjoint.of_isField
  -- need these otherwise the `exact` will stuck at typeclass
  have : SMulCommClass F A A := SMulCommClass.of_commMonoid F A A
  have : SMulCommClass F A.toSubalgebra A.toSubalgebra := ‹SMulCommClass F A A›
  let : Mul (A otimes[F] L) := Algebra.TensorProduct.instMul
  let : Mul (A.toSubalgebra otimes[F] (IsScalarTower.toAlgHom F L E).range) :=
    Algebra.TensorProduct.instMul
  exact Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))
.symm.toMulEquiv.isField H

/--
theorem `of_isField'` / 定理 `of_isField'`

English:
theorem of_isField'
  statement: {A : Type v} [Field A] {B : Type w} [Field B]
  proof: by
  rw [linearDisjoint_iff']
  apply Subalgebra.LinearDisjoint.of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa fa.injective)
.symm.toMulEquiv.isField H (AlgEquiv.ofInjective fb fb.injective)

中文:
定理 of_isField'
  结论: {A : 类型v} [域 A] {B : 类型 w} [域 B]
  证明: by
  rw [linearDisjoint_iff']
  apply Subalgebra.LinearDisjoint.of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa fa.injective)
.symm.toMulEquiv.isField H (AlgEquiv.ofInjective fb fb.injective)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Algebra, Algebra.TensorProduct.congr, LinearDisjoint, Subalgebra, Subalgebra.LinearDisjoint.of_isField, TensorProduct, fa.injective, fb.injective, injective, isField, linearDisjoint_iff, ofInjective, of_isField, symm.toMulEquiv.isField, toMulEquiv
-/
theorem of_isField' {A : Type v} [Field A] {B : Type w} [Field B]
    [Algebra F A] [Algebra F B] (H : IsField (A otimes[F] B))
    {K : Type*} [Field K] [Algebra F K] (fa : A ->ₐ[F] K) (fb : B ->ₐ[F] K) :
    fa.fieldRange.LinearDisjoint fb.fieldRange := by
  rw [linearDisjoint_iff']
  apply Subalgebra.LinearDisjoint.of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa fa.injective)
.symm.toMulEquiv.isField H (AlgEquiv.ofInjective fb fb.injective)

variable (F) in
/--
theorem `exists_field_of_isDomain` / 定理 `exists_field_of_isDomain`

English:
theorem exists_field_of_isDomain
  statement: (A : Type v) [Field A] (B : Type w) [Field B]
  proof: have ⟨K, inst1, inst2, fa, fb, _, _, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F A B
      (RingHom.injective _) (RingHom.injective _)
  ⟨K, inst1, inst2, fa, fb, linearDisjoint_iff'.2 H⟩

中文:
定理 存在_field_of_isDomain
  结论: (A : 类型v) [域 A] (B : 类型 w) [域 B]
  证明: have ⟨K, inst1, inst2, fa, fb, _, _, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F A B
      (RingHom.injective _) (RingHom.injective _)
  ⟨K, inst1, inst2, fa, fb, linearDisjoint_iff'.2 H⟩

Depends on / 依赖: LinearDisjoint, RingHom, RingHom.injective, Subalgebra, Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective, exists_field_of_isDomain_of_injective, injective, linearDisjoint_iff
-/
theorem exists_field_of_isDomain (A : Type v) [Field A] (B : Type w) [Field B]
    [Algebra F A] [Algebra F B] [IsDomain (A otimes[F] B)] :
    exists (K : Type (max v w)) (_ : Field K) (_ : Algebra F K) (fa : A ->ₐ[F] K) (fb : B ->ₐ[F] K),
    fa.fieldRange.LinearDisjoint fb.fieldRange :=
  have ⟨K, inst1, inst2, fa, fb, _, _, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F A B
      (RingHom.injective _) (RingHom.injective _)
  ⟨K, inst1, inst2, fa, fb, linearDisjoint_iff'.2 H⟩

variable (F) in
/--
theorem `isField_of_forall` / 定理 `isField_of_forall`

English:
theorem isField_of_forall
  statement: (A : Type v) [Field A] (B : Type w) [Field B]
  proof: by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A otimes[F] B)
  apply not_imp_not.1 (Ring.ne_bot_of_isMaximal_of_not_isField hM)
  let K : Type (max v w) := A otimes[F] B ⧸ M
  let : Field K := Ideal.Quotient.field _
  let i := IsScalarTower.toAlgHom F (A otimes[F] B) K
  let fa := i.comp (Algebra.Ten

中文:
定理 isField_of_对任意
  结论: (A : 类型v) [域 A] (B : 类型 w) [域 B]
  证明: by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A otimes[F] B)
  apply not_imp_not.1 (Ring.ne_bot_of_isMaximal_of_not_isField hM)
  let K : Type (max v w) := A otimes[F] B ⧸ M
  let : Field K := Ideal.Quotient.field _
  let i := IsScalarTower.toAlgHom F (A otimes[F] B) K
  let fa := i.comp (Algebra.Ten

Depends on / 依赖: AlgHom, AlgHom.fieldRange_toSubalgebra, Algebra, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, Ideal.Quotient.field, Ideal.exists_maximal, IsScalarTower, IsScalarTower.toAlgHom, Quotient, Ring.ne_bot_of_isMaximal_of_not_isField, Subalgebra, Subalgebra.linearDisjoi, TensorProduct, exists_maximal, fieldRange_toSubalgebra, i.comp, includeLeft, includeRight, linearDisjoi
-/
theorem isField_of_forall (A : Type v) [Field A] (B : Type w) [Field B]
    [Algebra F A] [Algebra F B]
    (H : forall (K : Type (max v w)) [Field K] [Algebra F K],
      forall (fa : A ->ₐ[F] K) (fb : B ->ₐ[F] K), fa.fieldRange.LinearDisjoint fb.fieldRange) :
    IsField (A otimes[F] B) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A otimes[F] B)
  apply not_imp_not.1 (Ring.ne_bot_of_isMaximal_of_not_isField hM)
  let K : Type (max v w) := A otimes[F] B ⧸ M
  let : Field K := Ideal.Quotient.field _
  let i := IsScalarTower.toAlgHom F (A otimes[F] B) K
  let fa := i.comp (Algebra.TensorProduct.includeLeft : A ->ₐ[F] _)
  let fb := i.comp (Algebra.TensorProduct.includeRight : B ->ₐ[F] _)
  replace H := H K fa fb
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra,
    Subalgebra.linearDisjoint_iff_injective] at H
  have hi : i = (fa.range.mulMap fb.range).comp (Algebra.TensorProduct.congr
      (AlgEquiv.ofInjective fa fa.injective) (AlgEquiv.ofInjective fb fb.injective)) := by
    ext <;> simp [fa, fb]
  replace H : Function.Injective i := by simpa only
    [hi, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, EquivLike.injective_comp, fa, this, K, fb]
  change Function.Injective (Ideal.Quotient.mk M) at H
  rwa [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker] at H

variable (F E) in
/--
theorem `_root_.Algebra.TensorProduct.isField_of_isAlgebraic` / 定理 `_root_.Algebra.TensorProduct.isField_of_isAlgebraic`

English:
theorem _root_.Algebra.TensorProduct.isField_of_isAlgebraic
  proof: have ⟨L, _, _, fa, fb, hfa, hfb, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F E K
      (RingHom.injective _) (RingHom.injective _)
  let f : E otimes[F] K ≃ₐ[F] ↥(fa.fieldRange ⊔ fb.fieldRange) :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa) (AlgEquiv

中文:
定理 _root_.代数.张量积.isField_of_isAlgebraic
  证明: have ⟨L, _, _, fa, fb, hfa, hfb, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F E K
      (RingHom.injective _) (RingHom.injective _)
  let f : E otimes[F] K ≃ₐ[F] ↥(fa.fieldRange ⊔ fb.fieldRange) :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa) (AlgEquiv

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Algebra, Algebra.TensorProduct.congr, LinearDisjoint, RingHom, RingHom.injective, Subalgebra, Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective, Subalgebra.LinearDisjoint.mulMap, Subalgebra.equivOfEq, TensorProduct, equivOfEq, exists_field_of_isDomain_of_injective, fa.fieldRange, fb.fieldRange, fieldRange, injective, isAlgebraic_iff, mulMap
-/
theorem _root_.Algebra.TensorProduct.isField_of_isAlgebraic
    (K : Type*) [Field K] [Algebra F K] [IsDomain (E otimes[F] K)]
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K) : IsField (E otimes[F] K) :=
  have ⟨L, _, _, fa, fb, hfa, hfb, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F E K
      (RingHom.injective _) (RingHom.injective _)
  let f : E otimes[F] K ≃ₐ[F] ↥(fa.fieldRange ⊔ fb.fieldRange) :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)
.trans (Subalgebra.LinearDisjoint.mulMap H)
.trans (Subalgebra.equivOfEq _ _
      (sup_toSubalgebra_of_isAlgebraic fa.fieldRange fb.fieldRange <| by
        rwa [(AlgEquiv.ofInjective fa hfa).isAlgebraic_iff,
          (AlgEquiv.ofInjective fb hfb).isAlgebraic_iff] at halg).symm)
  f.toMulEquiv.isField (Field.toIsField _)

/--
theorem `isField_of_isAlgebraic` / 定理 `isField_of_isAlgebraic`

English:
theorem isField_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: have := H.isDomain
  Algebra.TensorProduct.isField_of_isAlgebraic F A L halg

中文:
定理 isField_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: have := H.isDomain
  Algebra.TensorProduct.isField_of_isAlgebraic F A L halg

Depends on / 依赖: Algebra, Algebra.TensorProduct.isField_of_isAlgebraic, H.isDomain, TensorProduct, isDomain, isField_of_isAlgebraic
-/
theorem isField_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : IsField (A otimes[F] L) :=
  have := H.isDomain
  Algebra.TensorProduct.isField_of_isAlgebraic F A L halg

/--
theorem `isField_of_isAlgebraic'` / 定理 `isField_of_isAlgebraic'`

English:
theorem isField_of_isAlgebraic'
  statement: {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
  proof: have := H.isDomain'
  Algebra.TensorProduct.isField_of_isAlgebraic F A B halg

中文:
定理 isField_of_isAlgebraic'
  结论: {A B : 类型} [域 A] [代数 F A] [域 B] [代数 F B]
  证明: have := H.isDomain'
  Algebra.TensorProduct.isField_of_isAlgebraic F A B halg

Depends on / 依赖: Algebra, Algebra.TensorProduct.isField_of_isAlgebraic, H.isDomain, TensorProduct, isDomain, isField_of_isAlgebraic
-/
theorem isField_of_isAlgebraic' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
    {fa : A ->ₐ[F] E} {fb : B ->ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRange)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) : IsField (A otimes[F] B) :=
  have := H.isDomain'
  Algebra.TensorProduct.isField_of_isAlgebraic F A B halg

/--
theorem `algEquiv_of_isAlgebraic` / 定理 `algEquiv_of_isAlgebraic`

English:
theorem algEquiv_of_isAlgebraic
  statement: (H : A.LinearDisjoint L)
  proof: .of_isField ((Algebra.TensorProduct.congr f1 f2).symm.toMulEquiv.isField
    (H.isField_of_isAlgebraic halg))

中文:
定理 algEquiv_of_isAlgebraic
  结论: (H : A.LinearDisjoint L)
  证明: .of_isField ((Algebra.TensorProduct.congr f1 f2).symm.toMulEquiv.isField
    (H.isField_of_isAlgebraic halg))

Depends on / 依赖: Algebra, Algebra.TensorProduct.congr, H.isField_of_isAlgebraic, TensorProduct, isField, isField_of_isAlgebraic, of_isField, symm.toMulEquiv.isField, toMulEquiv
-/
theorem algEquiv_of_isAlgebraic (H : A.LinearDisjoint L)
    {E' : Type*} [Field E'] [Algebra F E']
    (B : IntermediateField F E')
    (L' : Type*) [Field L'] [Algebra F L'] [Algebra L' E'] [IsScalarTower F L' E']
    (f1 : A ≃ₐ[F] B) (f2 : L ≃ₐ[F] L')
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    B.LinearDisjoint L' :=
  .of_isField ((Algebra.TensorProduct.congr f1 f2).symm.toMulEquiv.isField
    (H.isField_of_isAlgebraic halg))

/--
theorem `trace_algebraMap` / 定理 `trace_algebraMap`

English:
theorem trace_algebraMap
  statement: [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  proof: by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.trace_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

中文:
定理 trace_algebraMap
  结论: [有限维 F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  证明: by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.trace_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

Depends on / 依赖: congr_arg, linearDisjoint_iff, sup_toSubalgebra_of_isAlgebraic_right, toSubalgebra, trace_algebraMap
-/
theorem trace_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
    (x : B) :
    Algebra.trace A E (algebraMap B E x) = algebraMap F A (Algebra.trace F B x) := by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.trace_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

/--
theorem `norm_algebraMap` / 定理 `norm_algebraMap`

English:
theorem norm_algebraMap
  statement: [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  proof: by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.norm_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

中文:
定理 norm_algebraMap
  结论: [有限维 F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
  证明: by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.norm_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

Depends on / 依赖: congr_arg, linearDisjoint_iff, norm_algebraMap, sup_toSubalgebra_of_isAlgebraic_right, toSubalgebra
-/
theorem norm_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
    (x : B) :
    Algebra.norm A (algebraMap B E x) = algebraMap F A (Algebra.norm F x) := by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.norm_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

end LinearDisjoint

end IntermediateField
