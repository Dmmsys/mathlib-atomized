/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Data.Set.Subsingleton

/-!
# Hom orthogonal families.

A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.

We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.

When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.

If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
theorem HomOrthogonal.equiv_of_iso (o : HomOrthogonal s) {f : α → ι} {g : β → ι}
    (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/

@[expose] public section


open Matrix CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/--
Definition of `HomOrthogonal` / `HomOrthogonal` 的定义

English:
definition HomOrthogonal
  signature: {ι : Type*} (s : ι -> C)
  body: Pairwise fun i j => Subsingleton (s i ⟶ s j)

中文:
定义 HomOrthogonal
  签名: {ι : 类型} (s : ι -> C)
  定义体: Pairwise fun i j => Subsingleton (s i ⟶ s j)

Depends on / 依赖: Pairwise, Subsingleton
-/
def HomOrthogonal {ι : Type*} (s : ι -> C) : Prop :=
  Pairwise fun i j => Subsingleton (s i ⟶ s j)

namespace HomOrthogonal

variable {ι : Type*} {s : ι -> C}

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i != j) (f : s i ⟶ s j)
  proof: (o w).elim _ _

中文:
定理 eq_zero
  条件: [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i != j) (f : s i ⟶ s j)
  证明: (o w).elim _ _
-/
theorem eq_zero [HasZeroMorphisms C] (o : HomOrthogonal s) {i j : ι} (w : i != j) (f : s i ⟶ s j) :
    f = 0 :=
  (o w).elim _ _

section

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

open scoped Classical in
/-- Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`. -/
@[simps]
/--
Definition of `matrixDecomposition` / `matrixDecomposition` 的定义

English:
definition matrixDecomposition
  signature: (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β]
  body: eqToHom
        (by
          rcases k with ⟨k, ⟨⟩⟩
          simp) ≫
      biproduct.components z k j ≫
        eqToHom
          (by
            rcases j with ⟨j, ⟨⟩⟩
            simp)
  invFun z :=
    biproduct.matrix fun j k =>
      if h : f j = g k then z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫

中文:
定义 matrixDecomposition
  签名: (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β]
  定义体: eqToHom
        (by
          rcases k with ⟨k, ⟨⟩⟩
          simp) ≫
      biproduct.components z k j ≫
        eqToHom
          (by
            rcases j with ⟨j, ⟨⟩⟩
            simp)
  invFun z :=
    biproduct.matrix fun j k =>
      if h : f j = g k then z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫

Depends on / 依赖: Category, Category.id_comp, biproduct, biproduct.components, biproduct.matrix, biproduct.matrix_, biproduct.matrix_components, components, eqToHom, eqToHom_refl, eq_zero, id_comp, invFun, left_inv, matrix, matrix_components, o.eq_zero, right_inv, split_ifs
-/
noncomputable def matrixDecomposition (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β]
    {f : α -> ι} {g : β -> ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃
      forall i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) where
  toFun z i j k :=
    eqToHom
        (by
          rcases k with ⟨k, ⟨⟩⟩
          simp) ≫
      biproduct.components z k j ≫
        eqToHom
          (by
            rcases j with ⟨j, ⟨⟩⟩
            simp)
  invFun z :=
    biproduct.matrix fun j k =>
      if h : f j = g k then z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫ eqToHom (by simp [h]) else 0
  left_inv z := by
    ext j k
    simp only [biproduct.matrix_π, biproduct.ι_desc]
    split_ifs with h
    · simp
      rfl
    · symm
      apply o.eq_zero h
  right_inv z := by
    ext i ⟨j, w⟩ ⟨k, ⟨⟩⟩
    simp only [eqToHom_refl, biproduct.matrix_components, Category.id_comp]
    split_ifs with h
    · simp
    · exfalso
      exact h w.symm

end

section

variable [Preadditive C] [HasFiniteBiproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `HomOrthogonal.matrixDecomposition` as an additive equivalence. -/
@[simps!]
/--
Definition of `matrixDecompositionAddEquiv` / `matrixDecompositionAddEquiv` 的定义

English:
definition matrixDecompositionAddEquiv
  signature: (o : HomOrthogonal s) {α β : Type} [Finite α]
  body: { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

中文:
定义 matrixDecompositionAddEquiv
  签名: (o : HomOrthogonal s) {α β : Type} [Finite α]
  定义体: { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

Depends on / 依赖: biproduct, biproduct.components, components, map_add, matrixDecomposition, o.matrixDecomposition
-/
noncomputable def matrixDecompositionAddEquiv (o : HomOrthogonal s) {α β : Type} [Finite α]
    [Finite β] {f : α -> ι} {g : β -> ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃+
      forall i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecomposition with
    map_add' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
@[simp]
/--
theorem `matrixDecomposition_id` / 定理 `matrixDecomposition_id`

English:
theorem matrixDecomposition_id
  given: (o : HomOrthogonal s) {α : Type} [Finite α] {f : α -> ι} (i : ι)
  proof: by
  ext ⟨b, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Category.comp_id, Category.id_comp, End.one_def, eqToHom_refl,
    Matrix.one_apply, HomOrthogonal.matrixDecomposition_apply, biproduct.components]
  split_ifs with h
  · cases h
    sim

中文:
定理 matrixDecomposition_id
  条件: (o : HomOrthogonal s) {α : Type} [Finite α] {f : α -> ι} (i : ι)
  证明: by
  ext ⟨b, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Category.comp_id, Category.id_comp, End.one_def, eqToHom_refl,
    Matrix.one_apply, HomOrthogonal.matrixDecomposition_apply, biproduct.components]
  split_ifs with h
  · cases h
    sim

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, End.one_def, HomOrthogonal, HomOrthogonal.matrixDecomposition_apply, Matrix, Matrix.one_apply, Ne.symm, Set.mem_preimage, Set.mem_singleton_iff, Subtype, Subtype.mk.injEq, biproduct, biproduct.components, comp_id, comp_zero, components, convert, eqToHom_refl
-/
theorem matrixDecomposition_id (o : HomOrthogonal s) {α : Type} [Finite α] {f : α -> ι} (i : ι) :
    o.matrixDecomposition (𝟙 (⨁ fun a => s (f a))) i = 1 := by
  ext ⟨b, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Category.comp_id, Category.id_comp, End.one_def, eqToHom_refl,
    Matrix.one_apply, HomOrthogonal.matrixDecomposition_apply, biproduct.components]
  split_ifs with h
  · cases h
    simp
  · simp only [Subtype.mk.injEq] at h
    convert! comp_zero
    simpa using biproduct.ι_π_ne _ (Ne.symm h)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `matrixDecomposition_comp` / 定理 `matrixDecomposition_comp`

English:
theorem matrixDecomposition_comp
  statement: (o : HomOrthogonal s) {α β γ : Type} [Finite α] [Fintype β]
  proof: by
  ext ⟨c, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Matrix.mul_apply, Limits.biproduct.components,
    HomOrthogonal.matrixDecomposition_apply, Category.comp_id, Category.id_comp, Category.assoc,
    End.mul_def, eqToHom_refl, eqToHom_tra

中文:
定理 matrixDecomposition_comp
  结论: (o : HomOrthogonal s) {α β γ : Type} [Finite α] [Fintype β]
  证明: by
  ext ⟨c, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Matrix.mul_apply, Limits.biproduct.components,
    HomOrthogonal.matrixDecomposition_apply, Category.comp_id, Category.id_comp, Category.assoc,
    End.mul_def, eqToHom_refl, eqToHom_tra

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, End.mul_def, Finset, Finset.sum_congr_set, HomOrthogonal, HomOrthogonal.matrixDecomposition_apply, Limits, Limits.biproduct.components, Matrix, Matrix.mul_apply, Preadditive, Preadditive.comp_sum, Preadditive.sum_comp, Set.mem_preimage, Set.mem_singleto, Set.mem_singleton_iff, biproduct
-/
theorem matrixDecomposition_comp (o : HomOrthogonal s) {α β γ : Type} [Finite α] [Fintype β]
    [Finite γ] {f : α -> ι} {g : β -> ι} {h : γ -> ι} (z : (⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b))
    (w : (⨁ fun b => s (g b)) ⟶ ⨁ fun c => s (h c)) (i : ι) :
    o.matrixDecomposition (z ≫ w) i = o.matrixDecomposition w i * o.matrixDecomposition z i := by
  ext ⟨c, ⟨⟩⟩ ⟨a, j_property⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at j_property
  simp only [Matrix.mul_apply, Limits.biproduct.components,
    HomOrthogonal.matrixDecomposition_apply, Category.comp_id, Category.id_comp, Category.assoc,
    End.mul_def, eqToHom_refl, eqToHom_trans_assoc]
  conv_lhs => rw [← Category.id_comp w, ← biproduct.total]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr_set
  · simp
  · intro b nm
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at nm
    simp only [Category.assoc]
    convert! comp_zero
    convert! comp_zero
    convert! comp_zero
    convert! comp_zero
    simp only [o.eq_zero nm]

section

variable {R : Type*} [Semiring R] [Linear R C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `HomOrthogonal.MatrixDecomposition` as an `R`-linear equivalence. -/
@[simps]
/--
Definition of `matrixDecompositionLinearEquiv` / `matrixDecompositionLinearEquiv` 的定义

English:
definition matrixDecompositionLinearEquiv
  signature: (o : HomOrthogonal s) {α β : Type} [Finite α]
  body: { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

中文:
定义 matrixDecompositionLinearEquiv
  签名: (o : HomOrthogonal s) {α β : Type} [Finite α]
  定义体: { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

Depends on / 依赖: biproduct, biproduct.components, components, map_smul, matrixDecompositionAddEquiv, o.matrixDecompositionAddEquiv
-/
noncomputable def matrixDecompositionLinearEquiv (o : HomOrthogonal s) {α β : Type} [Finite α]
    [Finite β] {f : α -> ι} {g : β -> ι} :
    ((⨁ fun a => s (f a)) ⟶ ⨁ fun b => s (g b)) ≃ₗ[R]
      forall i : ι, Matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
  { o.matrixDecompositionAddEquiv with
    map_smul' := fun w z => by
      ext
      dsimp [biproduct.components]
      simp }

end

/-!
The hypothesis that `End (s i)` has invariant basis number is automatically satisfied
if `s i` is simple (as then `End (s i)` is a division ring).
-/


variable [forall i, InvariantBasisNumber (End (s i))]

/--
theorem `equiv_of_iso` / 定理 `equiv_of_iso`

English:
theorem equiv_of_iso
  statement: (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β] {f : α -> ι}
  proof: by
  classical
  refine ⟨Equiv.ofPreimageEquiv ?_, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  intro c
  apply Nonempty.some
  apply Cardinal.eq.1
  cases nonempty_fintype α; cases nonempty_fintype β
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  exact
    Matrix.square_of_invertible (o.matrixDecom

中文:
定理 equiv_of_iso
  结论: (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β] {f : α -> ι}
  证明: by
  classical
  refine ⟨Equiv.ofPreimageEquiv ?_, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  intro c
  apply Nonempty.some
  apply Cardinal.eq.1
  cases nonempty_fintype α; cases nonempty_fintype β
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  exact
    Matrix.square_of_invertible (o.matrixDecom

Depends on / 依赖: Cardinal, Cardinal.eq, Cardinal.mk_fintype, Equiv.ofPreimageEquiv, Equiv.ofPreimageEquiv_map, Matrix, Matrix.square_of_invertible, Nat.cast_inj, Nonempty, Nonempty.some, cast_inj, classical, i.hom, i.inv, matrixDecomposition, matrixDecomposition_comp, mk_fintype, nonempty_fintype, o.matrixDecomposition, o.matrixDecomposition_comp
-/
theorem equiv_of_iso (o : HomOrthogonal s) {α β : Type} [Finite α] [Finite β] {f : α -> ι}
    {g : β -> ι} (i : (⨁ fun a => s (f a)) ≅ ⨁ fun b => s (g b)) :
    exists e : α ≃ β, forall a, g (e a) = f a := by
  classical
  refine ⟨Equiv.ofPreimageEquiv ?_, fun a => Equiv.ofPreimageEquiv_map _ _⟩
  intro c
  apply Nonempty.some
  apply Cardinal.eq.1
  cases nonempty_fintype α; cases nonempty_fintype β
  simp only [Cardinal.mk_fintype, Nat.cast_inj]
  exact
    Matrix.square_of_invertible (o.matrixDecomposition i.inv c) (o.matrixDecomposition i.hom c)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)
      (by
        rw [← o.matrixDecomposition_comp]
        simp)

end

end HomOrthogonal

end CategoryTheory
