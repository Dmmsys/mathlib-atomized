/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Independence in Projective Space

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define the independence of points in projective
space, where the only constructor assumes an independent family of vectors from the
ambient vector space. Similarly for the definition of dependence.

## Results

- A family of elements is dependent if and only if it is not independent.
- Two elements are dependent if and only if they are equal.

## Future Work

- Prove the axioms of a projective geometry are satisfied by the dependence relation.
- Define projective linear subspaces.
-/

public section

open scoped LinearAlgebra.Projectivization

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι -> ℙ K V}

namespace Projectivization

/--
Inductive type `Independent` / 归纳类型 `Independent`

English:
inductive Independent
  parameters: : (ι -> ℙ K V) -> Prop
  constructors (1):
    - mk: (f : ι -> V) (hf : forall i : ι, f i != 0) (hl : LinearIndependent K f) : Independent fun i => mk K (f i) (hf i)

中文:
归纳类型 Independent
  参数: : (ι -> ℙ K V) -> 命题
  构造子 (1 个):
    - mk: (f : ι -> V) (hf : 对任意 i : ι, f i != 0) (hl : LinearIndependent K f) : Independent fun i => mk K (f i) (hf i)
-/
inductive Independent : (ι -> ℙ K V) -> Prop
  | mk (f : ι -> V) (hf : forall i : ι, f i != 0) (hl : LinearIndependent K f) :
    Independent fun i => mk K (f i) (hf i)

/--
theorem `independent_iff` / 定理 `independent_iff`

English:
theorem independent_iff
  statement: Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f)
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh.units_smul a
    ext i
    exact (ha i).symm
  · convert! Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_

中文:
定理 independent_iff
  结论: Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f)
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh.units_smul a
    ext i
    exact (ha i).symm
  · convert! Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_

Depends on / 依赖: Function, Function.comp_apply, Independent, Independent.mk, comp_apply, convert, exists_smul_eq_mk_rep, hh.units_smul, mk_rep, rep_nonzero, units_smul
-/
theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh.units_smul a
    ext i
    exact (ha i).symm
  · convert! Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_nonzero

/--
theorem `independent_iff_iSupIndep` / 定理 `independent_iff_iSupIndep`

English:
theorem independent_iff_iSupIndep
  statement: Independent f ↔ iSupIndep fun i => (f i).submodule
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.co

中文:
定理 independent_iff_iSupIndep
  结论: Independent f ↔ iSupIndep fun i => (f i).submodule
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.co

Depends on / 依赖: Function, Function.comp_apply, Projectivization, Projectivization.submodule, Submodule, Submodule.mem_span_singleton_self, comp_apply, h.linearIndependent, iSupIndep_iff_linearIndependent_of_ne_zero, independent_iff, linearIndependent, mem_span_singleton_self, rep_nonzero, submodule, submodule_eq, submodule_mk
-/
theorem independent_iff_iSupIndep : Independent f ↔ iSupIndep fun i => (f i).submodule := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
    · exact rep_nonzero (f i)

/--
Inductive type `Dependent` / 归纳类型 `Dependent`

English:
inductive Dependent
  parameters: : (ι -> ℙ K V) -> Prop
  constructors (1):
    - mk: (f : ι -> V) (hf : forall i : ι, f i != 0) (h : ¬LinearIndependent K f) : Dependent fun i => mk K (f i) (hf i)

中文:
归纳类型 Dependent
  参数: : (ι -> ℙ K V) -> 命题
  构造子 (1 个):
    - mk: (f : ι -> V) (hf : 对任意 i : ι, f i != 0) (h : ¬LinearIndependent K f) : Dependent fun i => mk K (f i) (hf i)
-/
inductive Dependent : (ι -> ℙ K V) -> Prop
  | mk (f : ι -> V) (hf : forall i : ι, f i != 0) (h : ¬LinearIndependent K f) :
    Dependent fun i => mk K (f i) (hf i)

/--
theorem `dependent_iff` / 定理 `dependent_iff`

English:
theorem dependent_iff
  statement: Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f)
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert! Dependent

中文:
定理 dependent_iff
  结论: Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f)
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert! Dependent

Depends on / 依赖: Dependent, Dependent.mk, Function, Function.comp_apply, Pi.inv_apply, Pi.smul_apply, comp_apply, contrapose, convert, exists_smul_eq_mk_rep, hh1.units_smul, inv_apply, inv_smul_smul, mk_rep, rep_nonzero, smul_apply, units_smul
-/
theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert! Dependent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · exact fun i => rep_nonzero (f i)

/--
theorem `dependent_iff_not_independent` / 定理 `dependent_iff_not_independent`

English:
theorem dependent_iff_not_independent
  statement: Dependent f ↔ ¬Independent f
  proof: by
  rw [dependent_iff]; rw [independent_iff]

中文:
定理 dependent_iff_not_independent
  结论: Dependent f ↔ ¬Independent f
  证明: by
  rw [dependent_iff]; rw [independent_iff]

Depends on / 依赖: dependent_iff, independent_iff
-/
theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff]; rw [independent_iff]

/--
theorem `independent_iff_not_dependent` / 定理 `independent_iff_not_dependent`

English:
theorem independent_iff_not_dependent
  statement: Independent f ↔ ¬Dependent f
  proof: by
  rw [dependent_iff_not_independent]; rw [Classical.not_not]

中文:
定理 independent_iff_not_dependent
  结论: Independent f ↔ ¬Dependent f
  证明: by
  rw [dependent_iff_not_independent]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, dependent_iff_not_independent, not_not
-/
theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent]; rw [Classical.not_not]

/-- Two points in a projective space are dependent if and only if they are equal. -/
@[simp]
/--
theorem `dependent_pair_iff_eq` / 定理 `dependent_pair_iff_eq`

English:
theorem dependent_pair_iff_eq
  given: (u v : ℙ K V)
  statement: Dependent ![u, v] ↔ u = v
  proof: by
  rw [dependent_iff_not_independent]; rw [independent_iff]; rw [linearIndependent_fin2]
  dsimp only [Function.comp_def, Matrix.cons_val]
  simp only [not_and, not_forall, not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_

中文:
定理 dependent_pair_iff_eq
  条件: (u v : ℙ K V)
  结论: Dependent ![u, v] ↔ u = v
  证明: by
  rw [dependent_iff_not_independent]; rw [independent_iff]; rw [linearIndependent_fin2]
  dsimp only [Function.comp_def, Matrix.cons_val]
  simp only [not_and, not_forall, not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_

Depends on / 依赖: Classical, Classical.imp_iff_right_iff, Function, Function.comp_def, Matrix, Matrix.cons_val, Or.inl, comp_def, cons_val, dependent_iff_not_independent, imp_iff_right_iff, independent_iff, linearIndependent_fin2, mk_eq_mk_iff, mk_rep, not_and, not_forall, not_not, rep_nonzero
-/
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v := by
  rw [dependent_iff_not_independent]; rw [independent_iff]; rw [linearIndependent_fin2]
  dsimp only [Function.comp_def, Matrix.cons_val]
  simp only [not_and, not_forall, not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)

/-- Two points in a projective space are independent if and only if the points are not equal. -/
@[simp]
/--
theorem `independent_pair_iff_ne` / 定理 `independent_pair_iff_ne`

English:
theorem independent_pair_iff_ne
  given: (u v : ℙ K V)
  statement: Independent ![u, v] ↔ u != v
  proof: by
  rw [independent_iff_not_dependent]; rw [dependent_pair_iff_eq u v]

中文:
定理 independent_pair_iff_ne
  条件: (u v : ℙ K V)
  结论: Independent ![u, v] ↔ u != v
  证明: by
  rw [independent_iff_not_dependent]; rw [dependent_pair_iff_eq u v]

Depends on / 依赖: dependent_pair_iff_eq, independent_iff_not_dependent
-/
theorem independent_pair_iff_ne (u v : ℙ K V) : Independent ![u, v] ↔ u != v := by
  rw [independent_iff_not_dependent]; rw [dependent_pair_iff_eq u v]

/--
lemma `independent_mk_iff_LinearIndependent` / 引理 `independent_mk_iff_LinearIndependent`

English:
lemma independent_mk_iff_LinearIndependent
  given: {u v : V} (hu : u != 0) (hv : v != 0)
  proof: by
  rw [independent_pair_iff_ne]; rw [ne_eq]; rw [mk_eq_mk_iff' K u v hu hv]; rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h => ⟨hv, fun a ha => h ⟨a, ha⟩⟩, fun ⟨_, h⟩ ⟨a, ha⟩ => h a ha⟩

中文:
引理 independent_mk_iff_LinearIndependent
  条件: {u v : V} (hu : u != 0) (hv : v != 0)
  证明: by
  rw [independent_pair_iff_ne]; rw [ne_eq]; rw [mk_eq_mk_iff' K u v hu hv]; rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h => ⟨hv, fun a ha => h ⟨a, ha⟩⟩, fun ⟨_, h⟩ ⟨a, ha⟩ => h a ha⟩

Depends on / 依赖: Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, cons_val_one, cons_val_zero, independent_pair_iff_ne, linearIndependent_fin2, mk_eq_mk_iff, ne_eq
-/
lemma independent_mk_iff_LinearIndependent {u v : V} (hu : u != 0) (hv : v != 0) :
    Independent ![mk K u hu, mk K v hv] ↔ LinearIndependent K ![u, v] := by
  rw [independent_pair_iff_ne]; rw [ne_eq]; rw [mk_eq_mk_iff' K u v hu hv]; rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h => ⟨hv, fun a ha => h ⟨a, ha⟩⟩, fun ⟨_, h⟩ ⟨a, ha⟩ => h a ha⟩

end Projectivization
