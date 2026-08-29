/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber, Yaël Dillies, Kin Yau James Wong
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Constructions

/-!
# π-systems of cylinders and square cylinders

The instance `MeasurableSpace.pi` on `∀ i, α i`, where each `α i` has a `MeasurableSpace` `m i`,
is defined as `⨆ i, (m i).comap (fun a => a i)`.
That is, a function `g : β → ∀ i, α i` is measurable iff for all `i`, the function `b ↦ g b i`
is measurable.

We define two π-systems generating `MeasurableSpace.pi`, cylinders and square cylinders.

## Main definitions

Given a finite set `s` of indices, a cylinder is the product of a set of `∀ i : s, α i` and of
`univ` on the other indices. A square cylinder is a cylinder for which the set on `∀ i : s, α i` is
a product set.

* `cylinder s S`: cylinder with base set `S : Set (∀ i : s, α i)` where `s` is a `Finset`
* `squareCylinders C` with `C : ∀ i, Set (Set (α i))`: set of all square cylinders such that for
  all `i` in the finset defining the box, the projection to `α i` belongs to `C i`. The main
  application of this is with `C i = {s : Set (α i) | MeasurableSet s}`.
* `measurableCylinders`: set of all cylinders with measurable base sets.
* `cylinderEvents Δ`: The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making
  the projections on the `i`-th coordinate continuous for all `i ∈ Δ`.

## Main statements

* `generateFrom_squareCylinders`: square cylinders formed from measurable sets generate the product
  σ-algebra
* `generateFrom_measurableCylinders`: cylinders formed from measurable sets generate the
  product σ-algebra

-/

@[expose] public section

open Function Set MeasurableSpace

namespace MeasureTheory

variable {ι : Type _} {α : ι -> Type _}

section squareCylinders

/--
Definition of `squareCylinders` / `squareCylinders` 的定义

English:
definition squareCylinders
  signature: (C : forall i, Set (Set (α i)))
  body: {S | exists s : Finset ι, exists t in univ.pi C, S = (s : Set ι).pi t}

中文:
定义 squareCylinders
  签名: (C : 对任意 i, 集合 (集合 (α i)))
  定义体: {S | exists s : Finset ι, exists t in univ.pi C, S = (s : Set ι).pi t}

Depends on / 依赖: Finset, univ.pi
-/
def squareCylinders (C : forall i, Set (Set (α i))) : Set (Set (forall i, α i)) :=
  {S | exists s : Finset ι, exists t in univ.pi C, S = (s : Set ι).pi t}

/--
theorem `squareCylinders_eq_iUnion_image` / 定理 `squareCylinders_eq_iUnion_image`

English:
theorem squareCylinders_eq_iUnion_image
  given: (C : forall i, Set (Set (α i)))
  proof: by
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_univ_pi, mem_ofPred_eq,
    eq_comm (a := f)]

中文:
定理 squareCylinders_eq_iUnion_image
  条件: (C : 对任意 i, 集合 (集合 (α i)))
  证明: by
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_univ_pi, mem_ofPred_eq,
    eq_comm (a := f)]

Depends on / 依赖: eq_comm, mem_iUnion, mem_image, mem_ofPred_eq, mem_univ_pi, squareCylinders
-/
theorem squareCylinders_eq_iUnion_image (C : forall i, Set (Set (α i))) :
    squareCylinders C = ⋃ s : Finset ι, (fun t => (s : Set ι).pi t) '' univ.pi C := by
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_univ_pi, mem_ofPred_eq,
    eq_comm (a := f)]

/--
theorem `isPiSystem_squareCylinders` / 定理 `isPiSystem_squareCylinders`

English:
theorem isPiSystem_squareCylinders
  statement: {C : forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i))
  proof: by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ (fun i => univ)
  let t₂' := s₂.piecewise t₂ (fun i => univ)
  have h1 : forall i in (s₁ : Set ι), t₁ i = t₁' i :=
    fun i hi => (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : foral

中文:
定理 isPiSystem_squareCylinders
  结论: {C : 对任意 i, 集合 (集合 (α i))} (hC : 对任意 i, IsPiSystem (C i))
  证明: by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ (fun i => univ)
  let t₂' := s₂.piecewise t₂ (fun i => univ)
  have h1 : forall i in (s₁ : Set ι), t₁ i = t₁' i :=
    fun i hi => (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : foral

Depends on / 依赖: Finset, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem, classical, hst_nonempty, piecewise, piecewise_eq_of_mem, piecewise_eq_of_notMem
-/
theorem isPiSystem_squareCylinders {C : forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i))
    (hC_univ : forall i, univ in C i) :
    IsPiSystem (squareCylinders C) := by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ (fun i => univ)
  let t₂' := s₂.piecewise t₂ (fun i => univ)
  have h1 : forall i in (s₁ : Set ι), t₁ i = t₁' i :=
    fun i hi => (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : forall i ∉ (s₁ : Set ι), t₁' i = univ :=
    fun i hi => Finset.piecewise_eq_of_notMem _ _ _ hi
  have h2 : forall i in (s₂ : Set ι), t₂ i = t₂' i :=
    fun i hi => (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h2' : forall i ∉ (s₂ : Set ι), t₂' i = univ :=
    fun i hi => Finset.piecewise_eq_of_notMem _ _ _ hi
  rw [Set.pi_congr rfl h1]; rw [Set.pi_congr rfl h2]; rw [← union_pi_inter h1' h2']
  refine ⟨s₁ union s₂, fun i => t₁' i inter t₂' i, ?_, ?_⟩
  · rw [mem_univ_pi]
    intro i
    have : (t₁' i inter t₂' i).Nonempty := by
      obtain ⟨f, hf⟩ := hst_nonempty
      rw [Set.pi_congr rfl h1]; rw [Set.pi_congr rfl h2]; rw [mem_inter_iff]; rw [mem_pi]; rw [mem_pi] at hf
      refine ⟨f i, ⟨?_, ?_⟩⟩
      · by_cases hi₁ : i in s₁
        · exact hf.1 i hi₁
        · rw [h1' i hi₁]
          exact mem_univ _
      · by_cases hi₂ : i in s₂
        · exact hf.2 i hi₂
        · rw [h2' i hi₂]
          exact mem_univ _
    refine hC i _ ?_ _ ?_ this
    · by_cases hi₁ : i in s₁
      · rw [← h1 i hi₁]
        exact h₁ i (mem_univ _)
      · rw [h1' i hi₁]
        exact hC_univ i
    · by_cases hi₂ : i in s₂
      · rw [← h2 i hi₂]
        exact h₂ i (mem_univ _)
      · rw [h2' i hi₂]
        exact hC_univ i
  · rw [Finset.coe_union]

/--
theorem `comap_eval_le_generateFrom_squareCylinders_singleton` / 定理 `comap_eval_le_generateFrom_squareCylinders_singleton`

English:
theorem comap_eval_le_generateFrom_squareCylinders_singleton
  proof: by
  simp only [singleton_pi]
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S => ?_
  simp only [mem_ofPred_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j => if hji : j = i then by convert! t else uni

中文:
定理 comap_eval_le_generateFrom_squareCylinders_singleton
  证明: by
  simp only [singleton_pi]
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S => ?_
  simp only [mem_ofPred_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j => if hji : j = i then by convert! t else uni

Depends on / 依赖: Before, MeasurableSet, MeasurableSet.univ, MeasurableSpace, MeasurableSpace.comap_eq_generateFrom, MeasurableSpace.generateFrom_mono, adaptation_note, and_imp, cast_heq, classical, comap_eq_generateFrom, convert, dif_neg, dif_pos, eq_mpr_eq_cast, forall_exists_index, generateFrom_mono, mem_image, mem_ofPred_eq, mem_univ_pi
-/
theorem comap_eval_le_generateFrom_squareCylinders_singleton
    (α : ι -> Type*) [m : forall i, MeasurableSpace (α i)] (i : ι) :
    MeasurableSpace.comap (Function.eval i) (m i) <=
      MeasurableSpace.generateFrom
        ((fun t => ({i} : Set ι).pi t) '' univ.pi fun i => {s : Set (α i) | MeasurableSet s}) := by
  simp only [singleton_pi]
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S => ?_
  simp only [mem_ofPred_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j => if hji : j = i then by convert! t else univ, fun j => ?_, ?_⟩
  · by_cases hji : j = i
    · simp only [hji, eq_mpr_eq_cast, dif_pos]
      convert! ht
      simp only [cast_heq]
    · simp only [hji, not_false_iff, dif_neg, MeasurableSet.univ]
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp [h]

/--
theorem `generateFrom_squareCylinders` / 定理 `generateFrom_squareCylinders`

English:
theorem generateFrom_squareCylinders
  given: [forall i, MeasurableSpace (α i)]
  proof: by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_ofPred_eq] at h
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => h i)
  · refine iSup_le fun i => ?_
    refine (comap_eval_le_generateFrom_squareCylinders

中文:
定理 generateFrom_squareCylinders
  条件: [对任意 i, 可测空间 (α i)]
  证明: by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_ofPred_eq] at h
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => h i)
  · refine iSup_le fun i => ?_
    refine (comap_eval_le_generateFrom_squareCylinders

Depends on / 依赖: Finset, Finset.coe_singleton, Finset.countable_toSet, MeasurableSet, MeasurableSet.pi, MeasurableSpace, MeasurableSpace.generateFrom_le_iff, MeasurableSpace.generateFrom_mono, coe_singleton, comap_eval_le_generateFrom_squareCylinders_singleton, countable_toSet, generateFrom_le_iff, generateFrom_mono, iSup_le, le_antisymm, mem_ofPred_eq, mem_univ_pi, squareCylinders_eq_iUnion_image, subset_iUnion
-/
theorem generateFrom_squareCylinders [forall i, MeasurableSpace (α i)] :
    MeasurableSpace.generateFrom (squareCylinders fun i => {s : Set (α i) | MeasurableSet s}) =
      MeasurableSpace.pi := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_ofPred_eq] at h
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => h i)
  · refine iSup_le fun i => ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono ?_
    rw [← Finset.coe_singleton]; rw [squareCylinders_eq_iUnion_image]
    exact subset_iUnion
      (fun (s : Finset ι) =>
        (fun t : forall i, Set (α i) => (s : Set ι).pi t) '' univ.pi (fun i => Set.ofPred MeasurableSet))
      ({i} : Finset ι)

end squareCylinders

section cylinder

/--
Definition of `cylinder` / `cylinder` 的定义

English:
definition cylinder
  signature: (s : Finset ι) (S : Set (forall i : s, α i))
  body: s.restrict ⁻¹' S

@[simp]

中文:
定义 cylinder
  签名: (s : 有限集 ι) (S : 集合 (对任意 i : s, α i))
  定义体: s.restrict ⁻¹' S

@[simp]

Depends on / 依赖: restrict, s.restrict
-/
def cylinder (s : Finset ι) (S : Set (forall i : s, α i)) : Set (forall i, α i) :=
  s.restrict ⁻¹' S

@[simp]
/--
theorem `mem_cylinder` / 定理 `mem_cylinder`

English:
theorem mem_cylinder
  given: (s : Finset ι) (S : Set (forall i : s, α i)) (f : forall i, α i)
  proof: mem_preimage

@[simp]

中文:
定理 mem_cylinder
  条件: (s : 有限集 ι) (S : 集合 (对任意 i : s, α i)) (f : 对任意 i, α i)
  证明: mem_preimage

@[simp]

Depends on / 依赖: mem_preimage
-/
theorem mem_cylinder (s : Finset ι) (S : Set (forall i : s, α i)) (f : forall i, α i) :
    f in cylinder s S ↔ s.restrict f in S :=
  mem_preimage

@[simp]
/--
theorem `cylinder_empty` / 定理 `cylinder_empty`

English:
theorem cylinder_empty
  given: (s : Finset ι)
  statement: cylinder s (∅ : Set (forall i : s, α i)) = ∅
  proof: by
  rw [cylinder]; rw [preimage_empty]

@[simp]

中文:
定理 cylinder_empty
  条件: (s : 有限集 ι)
  结论: cylinder s (∅ : 集合 (对任意 i : s, α i)) = ∅
  证明: by
  rw [cylinder]; rw [preimage_empty]

@[simp]

Depends on / 依赖: cylinder, preimage_empty
-/
theorem cylinder_empty (s : Finset ι) : cylinder s (∅ : Set (forall i : s, α i)) = ∅ := by
  rw [cylinder]; rw [preimage_empty]

@[simp]
/--
theorem `cylinder_univ` / 定理 `cylinder_univ`

English:
theorem cylinder_univ
  given: (s : Finset ι)
  statement: cylinder s (univ : Set (forall i : s, α i)) = univ
  proof: by
  rw [cylinder]; rw [preimage_univ]

@[simp]

中文:
定理 cylinder_univ
  条件: (s : 有限集 ι)
  结论: cylinder s (univ : 集合 (对任意 i : s, α i)) = univ
  证明: by
  rw [cylinder]; rw [preimage_univ]

@[simp]

Depends on / 依赖: cylinder, preimage_univ
-/
theorem cylinder_univ (s : Finset ι) : cylinder s (univ : Set (forall i : s, α i)) = univ := by
  rw [cylinder]; rw [preimage_univ]

@[simp]
/--
theorem `cylinder_eq_empty_iff` / 定理 `cylinder_eq_empty_iff`

English:
theorem cylinder_eq_empty_iff
  statement: [h_nonempty : Nonempty (forall i, α i)] (s : Finset ι)
  proof: by
  refine ⟨fun h => ?_, fun h => by (rw [h]; exact cylinder_empty _)⟩
  by_contra hS
  rw [← Ne]; rw [← nonempty_iff_ne_empty] at hS
  let f := hS.some
  have hf : f in S := hS.choose_spec
  classical
  let f' : forall i, α i := fun i => if hi : i in s then f ⟨i, hi⟩ else h_nonempty.some i
  have 

中文:
定理 cylinder_eq_empty_iff
  结论: [h_nonempty : 非空 (对任意 i, α i)] (s : 有限集 ι)
  证明: by
  refine ⟨fun h => ?_, fun h => by (rw [h]; exact cylinder_empty _)⟩
  by_contra hS
  rw [← Ne]; rw [← nonempty_iff_ne_empty] at hS
  let f := hS.some
  have hf : f in S := hS.choose_spec
  classical
  let f' : forall i, α i := fun i => if hi : i in s then f ⟨i, hi⟩ else h_nonempty.some i
  have 

Depends on / 依赖: Finset, Finset.coe_mem, Finset.restrict_def, choose_spec, classical, coe_mem, cylinder, cylinder_empty, dif_pos, hS.choose_spec, hS.some, h_nonempty, h_nonempty.some, mem_cylinder, nonempty_iff_ne_empty, notMem_empty, restrict_def
-/
theorem cylinder_eq_empty_iff [h_nonempty : Nonempty (forall i, α i)] (s : Finset ι)
    (S : Set (forall i : s, α i)) :
    cylinder s S = ∅ ↔ S = ∅ := by
  refine ⟨fun h => ?_, fun h => by (rw [h]; exact cylinder_empty _)⟩
  by_contra hS
  rw [← Ne]; rw [← nonempty_iff_ne_empty] at hS
  let f := hS.some
  have hf : f in S := hS.choose_spec
  classical
  let f' : forall i, α i := fun i => if hi : i in s then f ⟨i, hi⟩ else h_nonempty.some i
  have hf' : f' in cylinder s S := by
    rw [mem_cylinder]
    simpa only [Finset.restrict_def, Finset.coe_mem, dif_pos, f']
  rw [h] at hf'
  exact notMem_empty _ hf'

/--
theorem `inter_cylinder` / 定理 `inter_cylinder`

English:
theorem inter_cylinder
  statement: (s₁ s₂ : Finset ι) (S₁ : Set (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i))
  proof: rfl

中文:
定理 inter_cylinder
  结论: (s₁ s₂ : 有限集 ι) (S₁ : 集合 (对任意 i : s₁, α i)) (S₂ : 集合 (对任意 i : s₂, α i))
  证明: rfl
-/
theorem inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ inter cylinder s₂ S₂ =
      cylinder (s₁ union s₂)
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ inter
          Finset.restrict₂ Finset.subset_union_right ⁻¹' S₂) := rfl

/--
theorem `inter_cylinder_same` / 定理 `inter_cylinder_same`

English:
theorem inter_cylinder_same
  given: (s : Finset ι) (S₁ : Set (forall i : s, α i)) (S₂ : Set (forall i : s, α i))
  proof: rfl

中文:
定理 inter_cylinder_same
  条件: (s : 有限集 ι) (S₁ : 集合 (对任意 i : s, α i)) (S₂ : 集合 (对任意 i : s, α i))
  证明: rfl
-/
theorem inter_cylinder_same (s : Finset ι) (S₁ : Set (forall i : s, α i)) (S₂ : Set (forall i : s, α i)) :
    cylinder s S₁ inter cylinder s S₂ = cylinder s (S₁ inter S₂) := rfl

/--
theorem `union_cylinder` / 定理 `union_cylinder`

English:
theorem union_cylinder
  statement: (s₁ s₂ : Finset ι) (S₁ : Set (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i))
  proof: rfl

中文:
定理 union_cylinder
  结论: (s₁ s₂ : 有限集 ι) (S₁ : 集合 (对任意 i : s₁, α i)) (S₂ : 集合 (对任意 i : s₂, α i))
  证明: rfl
-/
theorem union_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ union cylinder s₂ S₂ =
      cylinder (s₁ union s₂)
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ union
          Finset.restrict₂ Finset.subset_union_right ⁻¹' S₂) := rfl

/--
theorem `union_cylinder_same` / 定理 `union_cylinder_same`

English:
theorem union_cylinder_same
  given: (s : Finset ι) (S₁ : Set (forall i : s, α i)) (S₂ : Set (forall i : s, α i))
  proof: rfl

中文:
定理 union_cylinder_same
  条件: (s : 有限集 ι) (S₁ : 集合 (对任意 i : s, α i)) (S₂ : 集合 (对任意 i : s, α i))
  证明: rfl
-/
theorem union_cylinder_same (s : Finset ι) (S₁ : Set (forall i : s, α i)) (S₂ : Set (forall i : s, α i)) :
    cylinder s S₁ union cylinder s S₂ = cylinder s (S₁ union S₂) := rfl

/--
theorem `compl_cylinder` / 定理 `compl_cylinder`

English:
theorem compl_cylinder
  given: (s : Finset ι) (S : Set (forall i : s, α i))
  proof: by
  ext1 f; simp only [mem_compl_iff, mem_cylinder]

中文:
定理 compl_cylinder
  条件: (s : 有限集 ι) (S : 集合 (对任意 i : s, α i))
  证明: by
  ext1 f; simp only [mem_compl_iff, mem_cylinder]

Depends on / 依赖: mem_compl_iff, mem_cylinder
-/
theorem compl_cylinder (s : Finset ι) (S : Set (forall i : s, α i)) :
    (cylinder s S)ᶜ = cylinder s (Sᶜ) := by
  ext1 f; simp only [mem_compl_iff, mem_cylinder]

/--
theorem `sdiff_cylinder_same` / 定理 `sdiff_cylinder_same`

English:
theorem sdiff_cylinder_same
  given: (s : Finset ι) (S T : Set (forall i : s, α i))
  proof: by
  ext1 f; simp only [mem_sdiff, mem_cylinder]

@[deprecated (since := "2026-06-03")] alias diff_cylinder_same := sdiff_cylinder_same

中文:
定理 sdiff_cylinder_same
  条件: (s : 有限集 ι) (S T : 集合 (对任意 i : s, α i))
  证明: by
  ext1 f; simp only [mem_sdiff, mem_cylinder]

@[deprecated (since := "2026-06-03")] alias diff_cylinder_same := sdiff_cylinder_same

Depends on / 依赖: mem_cylinder, mem_sdiff
-/
theorem sdiff_cylinder_same (s : Finset ι) (S T : Set (forall i : s, α i)) :
    cylinder s S \ cylinder s T = cylinder s (S \ T) := by
  ext1 f; simp only [mem_sdiff, mem_cylinder]

@[deprecated (since := "2026-06-03")] alias diff_cylinder_same := sdiff_cylinder_same

/--
theorem `eq_of_cylinder_eq_of_subset` / 定理 `eq_of_cylinder_eq_of_subset`

English:
theorem eq_of_cylinder_eq_of_subset
  statement: [h_nonempty : Nonempty (forall i, α i)] {I J : Finset ι}
  proof: by
  rw [Set.ext_iff] at h_eq
  simp only [mem_cylinder] at h_eq
  ext1 f
  simp only [mem_preimage]
  classical
  specialize h_eq fun i => if hi : i in I then f ⟨i, hi⟩ else h_nonempty.some i
  have h_mem : forall j : J, ↑j in I := fun j => hJI j.prop
  simpa only [Finset.restrict_def, Finset.coe_m

中文:
定理 eq_of_cylinder_eq_of_subset
  结论: [h_nonempty : 非空 (对任意 i, α i)] {I J : 有限集 ι}
  证明: by
  rw [Set.ext_iff] at h_eq
  simp only [mem_cylinder] at h_eq
  ext1 f
  simp only [mem_preimage]
  classical
  specialize h_eq fun i => if hi : i in I then f ⟨i, hi⟩ else h_nonempty.some i
  have h_mem : forall j : J, ↑j in I := fun j => hJI j.prop
  simpa only [Finset.restrict_def, Finset.coe_m

Depends on / 依赖: Finset, Finset.coe_mem, Finset.restrict_def, Set.ext_iff, classical, coe_mem, dite_true, ext_iff, h_eq, h_mem, h_nonempty, h_nonempty.some, j.prop, mem_cylinder, mem_preimage, restrict_def, specialize
-/
theorem eq_of_cylinder_eq_of_subset [h_nonempty : Nonempty (forall i, α i)] {I J : Finset ι}
    {S : Set (forall i : I, α i)} {T : Set (forall i : J, α i)} (h_eq : cylinder I S = cylinder J T)
    (hJI : J subseteq I) :
    S = Finset.restrict₂ hJI ⁻¹' T := by
  rw [Set.ext_iff] at h_eq
  simp only [mem_cylinder] at h_eq
  ext1 f
  simp only [mem_preimage]
  classical
  specialize h_eq fun i => if hi : i in I then f ⟨i, hi⟩ else h_nonempty.some i
  have h_mem : forall j : J, ↑j in I := fun j => hJI j.prop
  simpa only [Finset.restrict_def, Finset.coe_mem, dite_true, h_mem] using! h_eq

/--
theorem `cylinder_eq_cylinder_union` / 定理 `cylinder_eq_cylinder_union`

English:
theorem cylinder_eq_cylinder_union
  statement: [DecidableEq ι] (I : Finset ι) (S : Set (forall i : I, α i))
  proof: by
  ext1 f; simp only [mem_cylinder, Finset.restrict_def, Finset.restrict₂_def, mem_preimage]

中文:
定理 cylinder_eq_cylinder_union
  结论: [DecidableEq ι] (I : 有限集 ι) (S : 集合 (对任意 i : I, α i))
  证明: by
  ext1 f; simp only [mem_cylinder, Finset.restrict_def, Finset.restrict₂_def, mem_preimage]

Depends on / 依赖: Finset, Finset.restrict, Finset.restrict_def, mem_cylinder, mem_preimage, restrict_def
-/
theorem cylinder_eq_cylinder_union [DecidableEq ι] (I : Finset ι) (S : Set (forall i : I, α i))
    (J : Finset ι) :
    cylinder I S =
      cylinder (I union J) (Finset.restrict₂ Finset.subset_union_left ⁻¹' S) := by
  ext1 f; simp only [mem_cylinder, Finset.restrict_def, Finset.restrict₂_def, mem_preimage]

/--
theorem `disjoint_cylinder_iff` / 定理 `disjoint_cylinder_iff`

English:
theorem disjoint_cylinder_iff
  statement: [Nonempty (forall i, α i)] {s t : Finset ι} {S : Set (forall i : s, α i)}
  proof: by
  simp_rw [Set.disjoint_iff, subset_empty_iff, inter_cylinder, cylinder_eq_empty_iff]

中文:
定理 disjoint_cylinder_iff
  结论: [非空 (对任意 i, α i)] {s t : 有限集 ι} {S : 集合 (对任意 i : s, α i)}
  证明: by
  simp_rw [Set.disjoint_iff, subset_empty_iff, inter_cylinder, cylinder_eq_empty_iff]

Depends on / 依赖: Set.disjoint_iff, cylinder_eq_empty_iff, disjoint_iff, inter_cylinder, simp_rw, subset_empty_iff
-/
theorem disjoint_cylinder_iff [Nonempty (forall i, α i)] {s t : Finset ι} {S : Set (forall i : s, α i)}
    {T : Set (forall i : t, α i)} [DecidableEq ι] :
    Disjoint (cylinder s S) (cylinder t T) ↔
      Disjoint
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S)
        (Finset.restrict₂ Finset.subset_union_right ⁻¹' T) := by
  simp_rw [Set.disjoint_iff, subset_empty_iff, inter_cylinder, cylinder_eq_empty_iff]

/--
theorem `IsClosed.cylinder` / 定理 `IsClosed.cylinder`

English:
theorem IsClosed.cylinder
  statement: [forall i, TopologicalSpace (α i)] (s : Finset ι) {S : Set (forall i : s, α i)}
  proof: hs.preimage (continuous_pi fun _ => continuous_apply _)

中文:
定理 是闭集.cylinder
  结论: [对任意 i, 拓扑空间 (α i)] (s : 有限集 ι) {S : 集合 (对任意 i : s, α i)}
  证明: hs.preimage (continuous_pi fun _ => continuous_apply _)

Depends on / 依赖: continuous_apply, continuous_pi, hs.preimage, preimage
-/
theorem IsClosed.cylinder [forall i, TopologicalSpace (α i)] (s : Finset ι) {S : Set (forall i : s, α i)}
    (hs : IsClosed S) : IsClosed (cylinder s S) :=
  hs.preimage (continuous_pi fun _ => continuous_apply _)

/--
theorem `_root_.MeasurableSet.cylinder` / 定理 `_root_.MeasurableSet.cylinder`

English:
theorem _root_.MeasurableSet.cylinder
  statement: [forall i, MeasurableSpace (α i)] (s : Finset ι)
  proof: measurable_pi_lambda _ (fun _ => measurable_pi_apply _) hS

中文:
定理 _root_.可测集.cylinder
  结论: [对任意 i, 可测空间 (α i)] (s : 有限集 ι)
  证明: measurable_pi_lambda _ (fun _ => measurable_pi_apply _) hS

Depends on / 依赖: measurable_pi_apply, measurable_pi_lambda
-/
theorem _root_.MeasurableSet.cylinder [forall i, MeasurableSpace (α i)] (s : Finset ι)
    {S : Set (forall i : s, α i)} (hS : MeasurableSet S) :
    MeasurableSet (cylinder s S) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _) hS

/--
theorem `dependsOn_cylinder_indicator_const` / 定理 `dependsOn_cylinder_indicator_const`

English:
theorem dependsOn_cylinder_indicator_const
  statement: {M : Type*} [Zero M] {I : Finset ι}
  proof: fun x y hxy => Set.indicator_const_eq_indicator_const (by simp [Finset.restrict_def, hxy])

中文:
定理 dependsOn_cylinder_indicator_const
  结论: {M : 类型} [零 M] {I : 有限集 ι}
  证明: fun x y hxy => Set.indicator_const_eq_indicator_const (by simp [Finset.restrict_def, hxy])

Depends on / 依赖: Finset, Finset.restrict_def, Set.indicator_const_eq_indicator_const, indicator_const_eq_indicator_const, restrict_def
-/
theorem dependsOn_cylinder_indicator_const {M : Type*} [Zero M] {I : Finset ι}
    (S : Set (Π i : I, α i)) (c : M) :
    DependsOn ((cylinder I S).indicator (fun _ => c)) I :=
  fun x y hxy => Set.indicator_const_eq_indicator_const (by simp [Finset.restrict_def, hxy])

end cylinder

section cylinders

/--
Definition of `measurableCylinders` / `measurableCylinders` 的定义

English:
definition measurableCylinders
  signature: (α : ι -> Type*) [forall i, MeasurableSpace (α i)]
  body: ⋃ (s) (S) (_ : MeasurableSet S), {cylinder s S}

中文:
定义 measurableCylinders
  签名: (α : ι -> 类型) [对任意 i, 可测空间 (α i)]
  定义体: ⋃ (s) (S) (_ : MeasurableSet S), {cylinder s S}

Depends on / 依赖: MeasurableSet, cylinder
-/
def measurableCylinders (α : ι -> Type*) [forall i, MeasurableSpace (α i)] : Set (Set (forall i, α i)) :=
  ⋃ (s) (S) (_ : MeasurableSet S), {cylinder s S}

/--
theorem `empty_mem_measurableCylinders` / 定理 `empty_mem_measurableCylinders`

English:
theorem empty_mem_measurableCylinders
  given: (α : ι -> Type*) [forall i, MeasurableSpace (α i)]
  proof: by
  simp_rw [measurableCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, MeasurableSet.empty, (cylinder_empty _).symm⟩

中文:
定理 empty_mem_measurableCylinders
  条件: (α : ι -> 类型) [对任意 i, 可测空间 (α i)]
  证明: by
  simp_rw [measurableCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, MeasurableSet.empty, (cylinder_empty _).symm⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, cylinder_empty, measurableCylinders, mem_iUnion, mem_singleton_iff, simp_rw
-/
theorem empty_mem_measurableCylinders (α : ι -> Type*) [forall i, MeasurableSpace (α i)] :
    ∅ in measurableCylinders α := by
  simp_rw [measurableCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, MeasurableSet.empty, (cylinder_empty _).symm⟩

variable [forall i, MeasurableSpace (α i)] {s t : Set (forall i, α i)}

@[simp]
/--
theorem `mem_measurableCylinders` / 定理 `mem_measurableCylinders`

English:
theorem mem_measurableCylinders
  given: (t : Set (forall i, α i))
  proof: by
  simp_rw [measurableCylinders, mem_iUnion, exists_prop, mem_singleton_iff]

@[measurability]

中文:
定理 mem_measurableCylinders
  条件: (t : 集合 (对任意 i, α i))
  证明: by
  simp_rw [measurableCylinders, mem_iUnion, exists_prop, mem_singleton_iff]

@[measurability]

Depends on / 依赖: exists_prop, measurableCylinders, mem_iUnion, mem_singleton_iff, simp_rw
-/
theorem mem_measurableCylinders (t : Set (forall i, α i)) :
    t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t = cylinder s S := by
  simp_rw [measurableCylinders, mem_iUnion, exists_prop, mem_singleton_iff]

@[measurability]
/--
theorem `_root_.MeasurableSet.of_mem_measurableCylinders` / 定理 `_root_.MeasurableSet.of_mem_measurableCylinders`

English:
theorem _root_.MeasurableSet.of_mem_measurableCylinders
  statement: {s : Set (Π i, α i)}
  proof: by
  obtain ⟨I, t, mt, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact mt.cylinder

中文:
定理 _root_.可测集.of_mem_measurableCylinders
  结论: {s : 集合 (Π i, α i)}
  证明: by
  obtain ⟨I, t, mt, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact mt.cylinder

Depends on / 依赖: cylinder, mem_measurableCylinders, mt.cylinder
-/
theorem _root_.MeasurableSet.of_mem_measurableCylinders {s : Set (Π i, α i)}
    (hs : s in measurableCylinders α) : MeasurableSet s := by
  obtain ⟨I, t, mt, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact mt.cylinder

/--
Definition of `measurableCylinders.finset` / `measurableCylinders.finset` 的定义

English:
definition measurableCylinders.finset
  signature: (ht : t in measurableCylinders α)
  body: ((mem_measurableCylinders t).mp ht).choose

中文:
定义 measurableCylinders.finset
  签名: (ht : t in measurableCylinders α)
  定义体: ((mem_measurableCylinders t).mp ht).choose

Depends on / 依赖: mem_measurableCylinders
-/
noncomputable def measurableCylinders.finset (ht : t in measurableCylinders α) : Finset ι :=
  ((mem_measurableCylinders t).mp ht).choose

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `measurableCylinders.set` / `measurableCylinders.set` 的定义

English:
definition measurableCylinders.set
  signature: (ht : t in measurableCylinders α)
  body: ((mem_measurableCylinders t).mp ht).choose_spec.choose

中文:
定义 measurableCylinders.set
  签名: (ht : t in measurableCylinders α)
  定义体: ((mem_measurableCylinders t).mp ht).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, mem_measurableCylinders
-/
noncomputable def measurableCylinders.set (ht : t in measurableCylinders α) :
    Set (forall i : measurableCylinders.finset ht, α i) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose

/--
theorem `measurableCylinders.measurableSet` / 定理 `measurableCylinders.measurableSet`

English:
theorem measurableCylinders.measurableSet
  given: (ht : t in measurableCylinders α)
  proof: ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.left

中文:
定理 measurableCylinders.measurableSet
  条件: (ht : t in measurableCylinders α)
  证明: ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.left

Depends on / 依赖: choose_spec, choose_spec.choose_spec.left, mem_measurableCylinders
-/
theorem measurableCylinders.measurableSet (ht : t in measurableCylinders α) :
    MeasurableSet (measurableCylinders.set ht) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.left

/--
theorem `measurableCylinders.eq_cylinder` / 定理 `measurableCylinders.eq_cylinder`

English:
theorem measurableCylinders.eq_cylinder
  given: (ht : t in measurableCylinders α)
  proof: ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.right

中文:
定理 measurableCylinders.eq_cylinder
  条件: (ht : t in measurableCylinders α)
  证明: ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.right

Depends on / 依赖: choose_spec, choose_spec.choose_spec.right, mem_measurableCylinders
-/
theorem measurableCylinders.eq_cylinder (ht : t in measurableCylinders α) :
    t = cylinder (measurableCylinders.finset ht) (measurableCylinders.set ht) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.right

/--
theorem `cylinder_mem_measurableCylinders` / 定理 `cylinder_mem_measurableCylinders`

English:
theorem cylinder_mem_measurableCylinders
  statement: (s : Finset ι) (S : Set (forall i : s, α i))
  proof: by
  rw [mem_measurableCylinders]; exact ⟨s, S, hS, rfl⟩

中文:
定理 cylinder_mem_measurableCylinders
  结论: (s : 有限集 ι) (S : 集合 (对任意 i : s, α i))
  证明: by
  rw [mem_measurableCylinders]; exact ⟨s, S, hS, rfl⟩

Depends on / 依赖: mem_measurableCylinders
-/
theorem cylinder_mem_measurableCylinders (s : Finset ι) (S : Set (forall i : s, α i))
    (hS : MeasurableSet S) :
    cylinder s S in measurableCylinders α := by
  rw [mem_measurableCylinders]; exact ⟨s, S, hS, rfl⟩

/--
theorem `inter_mem_measurableCylinders` / 定理 `inter_mem_measurableCylinders`

English:
theorem inter_mem_measurableCylinders
  statement: (hs : s in measurableCylinders α)
  proof: by
  rw [mem_measurableCylinders] at *
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hs
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := ht
  classical
  refine ⟨s₁ union s₂,
    Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ inter
      {f | Finset.restrict₂ Finset.subset_union_right f in S₂}, ?_, ?_⟩
  · refine MeasurableSet.in

中文:
定理 inter_mem_measurableCylinders
  结论: (hs : s in measurableCylinders α)
  证明: by
  rw [mem_measurableCylinders] at *
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hs
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := ht
  classical
  refine ⟨s₁ union s₂,
    Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ inter
      {f | Finset.restrict₂ Finset.subset_union_right f in S₂}, ?_, ?_⟩
  · refine MeasurableSet.in

Depends on / 依赖: Finset, Finset.restrict, Finset.subset_union_left, Finset.subset_union_right, MeasurableSet, MeasurableSet.inter, classical, inter_cylinder, measurable_pi_apply, measurable_pi_lambda, mem_measurableCylinders, subset_union_left, subset_union_right
-/
theorem inter_mem_measurableCylinders (hs : s in measurableCylinders α)
    (ht : t in measurableCylinders α) :
    s inter t in measurableCylinders α := by
  rw [mem_measurableCylinders] at *
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hs
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := ht
  classical
  refine ⟨s₁ union s₂,
    Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ inter
      {f | Finset.restrict₂ Finset.subset_union_right f in S₂}, ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _) hS₁
    · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _) hS₂
  · exact inter_cylinder _ _ _ _

/--
theorem `isPiSystem_measurableCylinders` / 定理 `isPiSystem_measurableCylinders`

English:
theorem isPiSystem_measurableCylinders
  statement: IsPiSystem (measurableCylinders α)
  proof: fun _ hS _ hT _ => inter_mem_measurableCylinders hS hT

中文:
定理 isPiSystem_measurableCylinders
  结论: IsPiSystem (measurableCylinders α)
  证明: fun _ hS _ hT _ => inter_mem_measurableCylinders hS hT

Depends on / 依赖: inter_mem_measurableCylinders
-/
theorem isPiSystem_measurableCylinders : IsPiSystem (measurableCylinders α) :=
  fun _ hS _ hT _ => inter_mem_measurableCylinders hS hT

/--
theorem `compl_mem_measurableCylinders` / 定理 `compl_mem_measurableCylinders`

English:
theorem compl_mem_measurableCylinders
  given: (hs : s in measurableCylinders α)
  proof: by
  rw [mem_measurableCylinders] at hs ⊢
  obtain ⟨s, S, hS, rfl⟩ := hs
  refine ⟨s, Sᶜ, hS.compl, ?_⟩
  rw [compl_cylinder]

中文:
定理 compl_mem_measurableCylinders
  条件: (hs : s in measurableCylinders α)
  证明: by
  rw [mem_measurableCylinders] at hs ⊢
  obtain ⟨s, S, hS, rfl⟩ := hs
  refine ⟨s, Sᶜ, hS.compl, ?_⟩
  rw [compl_cylinder]

Depends on / 依赖: compl_cylinder, hS.compl, mem_measurableCylinders
-/
theorem compl_mem_measurableCylinders (hs : s in measurableCylinders α) :
    sᶜ in measurableCylinders α := by
  rw [mem_measurableCylinders] at hs ⊢
  obtain ⟨s, S, hS, rfl⟩ := hs
  refine ⟨s, Sᶜ, hS.compl, ?_⟩
  rw [compl_cylinder]

/--
theorem `univ_mem_measurableCylinders` / 定理 `univ_mem_measurableCylinders`

English:
theorem univ_mem_measurableCylinders
  given: (α : ι -> Type*) [forall i, MeasurableSpace (α i)]
  proof: by
  rw [← compl_empty]; exact compl_mem_measurableCylinders (empty_mem_measurableCylinders α)

中文:
定理 univ_mem_measurableCylinders
  条件: (α : ι -> 类型) [对任意 i, 可测空间 (α i)]
  证明: by
  rw [← compl_empty]; exact compl_mem_measurableCylinders (empty_mem_measurableCylinders α)

Depends on / 依赖: compl_empty, compl_mem_measurableCylinders, empty_mem_measurableCylinders
-/
theorem univ_mem_measurableCylinders (α : ι -> Type*) [forall i, MeasurableSpace (α i)] :
    Set.univ in measurableCylinders α := by
  rw [← compl_empty]; exact compl_mem_measurableCylinders (empty_mem_measurableCylinders α)

/--
theorem `union_mem_measurableCylinders` / 定理 `union_mem_measurableCylinders`

English:
theorem union_mem_measurableCylinders
  statement: (hs : s in measurableCylinders α)
  proof: by
  rw [union_eq_compl_compl_inter_compl]
  exact compl_mem_measurableCylinders (inter_mem_measurableCylinders
    (compl_mem_measurableCylinders hs) (compl_mem_measurableCylinders ht))

中文:
定理 union_mem_measurableCylinders
  结论: (hs : s in measurableCylinders α)
  证明: by
  rw [union_eq_compl_compl_inter_compl]
  exact compl_mem_measurableCylinders (inter_mem_measurableCylinders
    (compl_mem_measurableCylinders hs) (compl_mem_measurableCylinders ht))

Depends on / 依赖: compl_mem_measurableCylinders, inter_mem_measurableCylinders, union_eq_compl_compl_inter_compl
-/
theorem union_mem_measurableCylinders (hs : s in measurableCylinders α)
    (ht : t in measurableCylinders α) :
    s union t in measurableCylinders α := by
  rw [union_eq_compl_compl_inter_compl]
  exact compl_mem_measurableCylinders (inter_mem_measurableCylinders
    (compl_mem_measurableCylinders hs) (compl_mem_measurableCylinders ht))

/--
theorem `sdiff_mem_measurableCylinders` / 定理 `sdiff_mem_measurableCylinders`

English:
theorem sdiff_mem_measurableCylinders
  statement: (hs : s in measurableCylinders α)
  proof: by
  rw [sdiff_eq_compl_inter]
  exact inter_mem_measurableCylinders (compl_mem_measurableCylinders ht) hs

@[deprecated (since := "2026-06-03")]
alias diff_mem_measurableCylinders := sdiff_mem_measurableCylinders

中文:
定理 sdiff_mem_measurableCylinders
  结论: (hs : s in measurableCylinders α)
  证明: by
  rw [sdiff_eq_compl_inter]
  exact inter_mem_measurableCylinders (compl_mem_measurableCylinders ht) hs

@[deprecated (since := "2026-06-03")]
alias diff_mem_measurableCylinders := sdiff_mem_measurableCylinders

Depends on / 依赖: compl_mem_measurableCylinders, inter_mem_measurableCylinders, sdiff_eq_compl_inter
-/
theorem sdiff_mem_measurableCylinders (hs : s in measurableCylinders α)
    (ht : t in measurableCylinders α) :
    s \ t in measurableCylinders α := by
  rw [sdiff_eq_compl_inter]
  exact inter_mem_measurableCylinders (compl_mem_measurableCylinders ht) hs

@[deprecated (since := "2026-06-03")]
alias diff_mem_measurableCylinders := sdiff_mem_measurableCylinders

/--
theorem `generateFrom_measurableCylinders` / 定理 `generateFrom_measurableCylinders`

English:
theorem generateFrom_measurableCylinders
  proof: by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le (fun S hS => ?_)
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders _).mp hS
    exact hSm.cylinder
  · refine iSup_le fun i => ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine Measurab

中文:
定理 generateFrom_measurableCylinders
  证明: by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le (fun S hS => ?_)
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders _).mp hS
    exact hSm.cylinder
  · refine iSup_le fun i => ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine Measurab

Depends on / 依赖: MeasurableSpace, MeasurableSpace.generateFrom_le, MeasurableSpace.generateFrom_mono, and_imp, comap_eval_le_generateFrom_squareCylinders_singleton, cylinder, forall_exists_index, forall_true_left, generateFrom_le, generateFrom_mono, hSm.cylinder, iSup_le, le_antisymm, mem_image, mem_measurableCylinders, mem_ofPred_eq, mem_pi, mem_univ, singleton_pi
-/
theorem generateFrom_measurableCylinders :
    MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpace.pi := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le (fun S hS => ?_)
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders _).mp hS
    exact hSm.cylinder
  · refine iSup_le fun i => ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono (fun x => ?_)
    simp only [singleton_pi, mem_image, mem_pi, mem_univ, mem_ofPred_eq,
      forall_true_left, mem_measurableCylinders, forall_exists_index, and_imp]
    rintro t ht rfl
    refine ⟨{i}, {f | f ⟨i, Finset.mem_singleton_self i⟩ in t i}, measurable_pi_apply _ (ht i), ?_⟩
    ext1 x
    simp only [mem_preimage, Function.eval, mem_cylinder, mem_ofPred_eq, Finset.restrict]

/--
theorem `measurableCylinders_nat` / 定理 `measurableCylinders_nat`

English:
theorem measurableCylinders_nat
  given: {X : Nat -> Type*} [forall n, MeasurableSpace (X n)]
  proof: by
  ext s
  simp only [mem_measurableCylinders, exists_prop, mem_iUnion]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ => ⟨Finset.Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, Finset.restrict₂ t.subset_Iic_sup_id ⁻¹' S,
    Finset.measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← pr

中文:
定理 measurableCylinders_nat
  条件: {X : 自然数 -> 类型} [对任意 n, 可测空间 (X n)]
  证明: by
  ext s
  simp only [mem_measurableCylinders, exists_prop, mem_iUnion]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ => ⟨Finset.Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, Finset.restrict₂ t.subset_Iic_sup_id ⁻¹' S,
    Finset.measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← pr

Depends on / 依赖: Finset, Finset.Iic, Finset.measurable_restrict, Finset.restrict, cylinder, exists_prop, mem_iUnion, mem_measurableCylinders, mem_singleton, preimage_comp, s_eq, subset_Iic_sup_id, t.subset_Iic_sup_id, t.sup
-/
theorem measurableCylinders_nat {X : Nat -> Type*} [forall n, MeasurableSpace (X n)] :
    measurableCylinders X = ⋃ (a) (S) (_ : MeasurableSet S), {cylinder (Finset.Iic a) S} := by
  ext s
  simp only [mem_measurableCylinders, exists_prop, mem_iUnion]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ => ⟨Finset.Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, Finset.restrict₂ t.subset_Iic_sup_id ⁻¹' S,
    Finset.measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← preimage_comp]; rw [Finset.restrict₂_comp_restrict]
  exact mem_singleton _

end cylinders

/-! ### Cylinder events as a sigma-algebra -/

section cylinderEvents

variable {α ι : Type*} {X : ι -> Type*} {mα : MeasurableSpace α} [m : forall i, MeasurableSpace (X i)]
  {Δ Δ₁ Δ₂ : Set ι} {i : ι}

/-- The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making the projections
on the `i`-th coordinate measurable for all `i ∈ Δ`. -/
@[instance_reducible]
/--
Definition of `cylinderEvents` / `cylinderEvents` 的定义

English:
definition cylinderEvents
  signature: (Δ : Set ι)
  body: ⨆ i in Δ, (m i).comap fun σ => σ i

中文:
定义 cylinderEvents
  签名: (Δ : 集合 ι)
  定义体: ⨆ i in Δ, (m i).comap fun σ => σ i
-/
def cylinderEvents (Δ : Set ι) : MeasurableSpace (forall i, X i) := ⨆ i in Δ, (m i).comap fun σ => σ i

/--
lemma `cylinderEvents_univ` / 引理 `cylinderEvents_univ`

English:
lemma cylinderEvents_univ
  statement: cylinderEvents (X := X) univ = MeasurableSpace.pi
  proof: by
  simp [cylinderEvents, MeasurableSpace.pi]

@[gcongr]

中文:
引理 cylinderEvents_univ
  结论: cylinderEvents (X := X) univ = 可测空间.pi
  证明: by
  simp [cylinderEvents, MeasurableSpace.pi]

@[gcongr]
-/
@[simp] lemma cylinderEvents_univ : cylinderEvents (X := X) univ = MeasurableSpace.pi := by
  simp [cylinderEvents, MeasurableSpace.pi]

@[gcongr]
/--
lemma `cylinderEvents_mono` / 引理 `cylinderEvents_mono`

English:
lemma cylinderEvents_mono
  given: (h : Δ₁ subseteq Δ₂)
  statement: cylinderEvents (X := X) Δ₁ <= cylinderEvents Δ₂
  proof: biSup_mono h

中文:
引理 cylinderEvents_mono
  条件: (h : Δ₁ subseteq Δ₂)
  结论: cylinderEvents (X := X) Δ₁ <= cylinderEvents Δ₂
  证明: biSup_mono h

Depends on / 依赖: cylinderEvents
-/
lemma cylinderEvents_mono (h : Δ₁ subseteq Δ₂) : cylinderEvents (X := X) Δ₁ <= cylinderEvents Δ₂ :=
  biSup_mono h

/--
lemma `cylinderEvents_le_pi` / 引理 `cylinderEvents_le_pi`

English:
lemma cylinderEvents_le_pi
  statement: cylinderEvents (X := X) Δ <= MeasurableSpace.pi
  proof: by
  simpa using cylinderEvents_mono (subset_univ _)

中文:
引理 cylinderEvents_le_pi
  结论: cylinderEvents (X := X) Δ <= 可测空间.pi
  证明: by
  simpa using cylinderEvents_mono (subset_univ _)

Depends on / 依赖: MeasurableSpace, MeasurableSpace.pi, cylinderEvents_mono, subset_univ
-/
lemma cylinderEvents_le_pi : cylinderEvents (X := X) Δ <= MeasurableSpace.pi := by
  simpa using cylinderEvents_mono (subset_univ _)

/--
lemma `measurable_cylinderEvents_iff` / 引理 `measurable_cylinderEvents_iff`

English:
lemma measurable_cylinderEvents_iff
  given: {g : α -> forall i, X i}
  proof: by
  simp_rw [measurable_iff_comap_le, cylinderEvents, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]

中文:
引理 measurable_cylinderEvents_iff
  条件: {g : α -> 对任意 i, X i}
  证明: by
  simp_rw [measurable_iff_comap_le, cylinderEvents, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]

Depends on / 依赖: Function, Function.comp_def, MeasurableSpace, MeasurableSpace.comap_comp, MeasurableSpace.comap_iSup, comap_comp, comap_iSup, comp_def, cylinderEvents, iSup_le_iff, measurable_iff_comap_le, simp_rw
-/
lemma measurable_cylinderEvents_iff {g : α -> forall i, X i} :
    @Measurable _ _ _ (cylinderEvents Δ) g ↔ forall ⦃i⦄, i in Δ -> Measurable fun a => g a i := by
  simp_rw [measurable_iff_comap_le, cylinderEvents, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
/--
lemma `measurable_cylinderEvent_apply` / 引理 `measurable_cylinderEvent_apply`

English:
lemma measurable_cylinderEvent_apply
  given: (hi : i in Δ)
  proof: measurable_cylinderEvents_iff.1 measurable_id hi

中文:
引理 measurable_cylinderEvent_apply
  条件: (hi : i in Δ)
  证明: measurable_cylinderEvents_iff.1 measurable_id hi

Depends on / 依赖: measurable_cylinderEvents_iff, measurable_id
-/
lemma measurable_cylinderEvent_apply (hi : i in Δ) :
    Measurable[cylinderEvents Δ] fun f : forall i, X i => f i :=
  measurable_cylinderEvents_iff.1 measurable_id hi

/--
lemma `Measurable.eval_cylinderEvents` / 引理 `Measurable.eval_cylinderEvents`

English:
lemma Measurable.eval_cylinderEvents
  statement: {g : α -> forall i, X i} (hi : i in Δ)
  proof: (measurable_cylinderEvent_apply hi).comp hg

@[fun_prop]

中文:
引理 可测.eval_cylinderEvents
  结论: {g : α -> 对任意 i, X i} (hi : i in Δ)
  证明: (measurable_cylinderEvent_apply hi).comp hg

@[fun_prop]

Depends on / 依赖: measurable_cylinderEvent_apply
-/
lemma Measurable.eval_cylinderEvents {g : α -> forall i, X i} (hi : i in Δ)
    (hg : @Measurable _ _ _ (cylinderEvents Δ) g) : Measurable fun a => g a i :=
  (measurable_cylinderEvent_apply hi).comp hg

@[fun_prop]
/--
lemma `measurable_cylinderEvents_lambda` / 引理 `measurable_cylinderEvents_lambda`

English:
lemma measurable_cylinderEvents_lambda
  given: (f : α -> forall i, X i) (hf : forall i, Measurable fun a => f a i)
  proof: measurable_pi_iff.mpr hf

中文:
引理 measurable_cylinderEvents_lambda
  条件: (f : α -> 对任意 i, X i) (hf : 对任意 i, 可测 fun a => f a i)
  证明: measurable_pi_iff.mpr hf

Depends on / 依赖: measurable_pi_iff, measurable_pi_iff.mpr
-/
lemma measurable_cylinderEvents_lambda (f : α -> forall i, X i) (hf : forall i, Measurable fun a => f a i) :
    Measurable f :=
  measurable_pi_iff.mpr hf

/--
lemma `measurable_update_cylinderEvents'` / 引理 `measurable_update_cylinderEvents'`

English:
lemma measurable_update_cylinderEvents'
  given: [DecidableEq ι]
  proof: by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_cylinderEvents_iff.1 measurable_fst hj

中文:
引理 measurable_update_cylinderEvents'
  条件: [DecidableEq ι]
  证明: by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_cylinderEvents_iff.1 measurable_fst hj

Depends on / 依赖: measurable_cylinderEvents_iff, measurable_fst, measurable_snd, split_ifs, update
-/
lemma measurable_update_cylinderEvents' [DecidableEq ι] :
    @Measurable _ _ (.prod (cylinderEvents Δ) (m i)) (cylinderEvents Δ)
      (fun p : (forall i, X i) × X i => update p.1 i p.2) := by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_cylinderEvents_iff.1 measurable_fst hj

/--
lemma `measurable_uniqueElim_cylinderEvents` / 引理 `measurable_uniqueElim_cylinderEvents`

English:
lemma measurable_uniqueElim_cylinderEvents
  given: [Unique ι]
  proof: by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

中文:
引理 measurable_uniqueElim_cylinderEvents
  条件: [唯一 ι]
  证明: by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff, measurable_id, measurable_pi_iff, simp_rw, uniqueElim_default
-/
lemma measurable_uniqueElim_cylinderEvents [Unique ι] :
    Measurable (uniqueElim : X (default : ι) -> forall i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

/-- The function `update f a : X a → Π a, X a` is always measurable.
This doesn't require `f` to be measurable.
This should not be confused with the statement that `update f a x` is measurable. -/
@[fun_prop]
/--
lemma `measurable_update_cylinderEvents` / 引理 `measurable_update_cylinderEvents`

English:
lemma measurable_update_cylinderEvents
  given: (f : forall a : ι, X a) {a : ι} [DecidableEq ι]
  proof: measurable_update_cylinderEvents'.comp measurable_prodMk_left

中文:
引理 measurable_update_cylinderEvents
  条件: (f : 对任意 a : ι, X a) {a : ι} [DecidableEq ι]
  证明: measurable_update_cylinderEvents'.comp measurable_prodMk_left

Depends on / 依赖: measurable_prodMk_left, measurable_update_cylinderEvents
-/
lemma measurable_update_cylinderEvents (f : forall a : ι, X a) {a : ι} [DecidableEq ι] :
    @Measurable _ _ _ (cylinderEvents Δ) (update f a) :=
  measurable_update_cylinderEvents'.comp measurable_prodMk_left

/--
lemma `measurable_update_cylinderEvents_left` / 引理 `measurable_update_cylinderEvents_left`

English:
lemma measurable_update_cylinderEvents_left
  given: {a : ι} [DecidableEq ι] {x : X a}
  proof: measurable_update_cylinderEvents'.comp measurable_prodMk_right

中文:
引理 measurable_update_cylinderEvents_left
  条件: {a : ι} [DecidableEq ι] {x : X a}
  证明: measurable_update_cylinderEvents'.comp measurable_prodMk_right

Depends on / 依赖: measurable_prodMk_right, measurable_update_cylinderEvents
-/
lemma measurable_update_cylinderEvents_left {a : ι} [DecidableEq ι] {x : X a} :
    @Measurable _ _ (cylinderEvents Δ) (cylinderEvents Δ) (update · a x) :=
  measurable_update_cylinderEvents'.comp measurable_prodMk_right

/--
lemma `measurable_restrict_cylinderEvents` / 引理 `measurable_restrict_cylinderEvents`

English:
lemma measurable_restrict_cylinderEvents
  given: (Δ : Set ι)
  proof: by
  rw [@measurable_pi_iff]; exact fun i => measurable_cylinderEvent_apply i.2

中文:
引理 measurable_restrict_cylinderEvents
  条件: (Δ : 集合 ι)
  证明: by
  rw [@measurable_pi_iff]; exact fun i => measurable_cylinderEvent_apply i.2

Depends on / 依赖: domRestrict, measurable_cylinderEvent_apply, measurable_pi_iff
-/
lemma measurable_restrict_cylinderEvents (Δ : Set ι) :
    Measurable[cylinderEvents (X := X) Δ] (domRestrict Δ) := by
  rw [@measurable_pi_iff]; exact fun i => measurable_cylinderEvent_apply i.2

end cylinderEvents

/--
lemma `MeasurableSet.eq_preimage_restrict_countable` / 引理 `MeasurableSet.eq_preimage_restrict_countable`

English:
lemma MeasurableSet.eq_preimage_restrict_countable
  proof: by
  refine induction_on_inter generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
    ⟨∅, ∅, by simp⟩ ?_ ?_ ?_ s hs
  · rintro - ⟨I, t, -, rfl⟩
    exact ⟨I, univ.pi (fun i => t i), I.countable_toSet, by ext; simp⟩
  · rintro - - ⟨I, t, h

中文:
引理 可测集.eq_preimage_restrict_countable
  证明: by
  refine induction_on_inter generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
    ⟨∅, ∅, by simp⟩ ?_ ?_ ?_ s hs
  · rintro - ⟨I, t, -, rfl⟩
    exact ⟨I, univ.pi (fun i => t i), I.countable_toSet, by ext; simp⟩
  · rintro - - ⟨I, t, h

Depends on / 依赖: I.countable_toSet, countable_iUnion, countable_toSet, domRestrict, generateFrom_squareCylinders, generateFrom_squareCylinders.symm, induction_on_inter, isPiSystem_measurableSet, isPiSystem_squareCylinders, mem_iUnion, mem_preimage, preimage_iU, univ.pi
-/
lemma MeasurableSet.eq_preimage_restrict_countable
    [forall i, MeasurableSpace (α i)] {s : Set (Π i, α i)} (hs : MeasurableSet s) :
    exists I : Set ι, exists t, I.Countable ∧ s = I.domRestrict ⁻¹' t := by
  refine induction_on_inter generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
    ⟨∅, ∅, by simp⟩ ?_ ?_ ?_ s hs
  · rintro - ⟨I, t, -, rfl⟩
    exact ⟨I, univ.pi (fun i => t i), I.countable_toSet, by ext; simp⟩
  · rintro - - ⟨I, t, hI, rfl⟩
    exact ⟨I, tᶜ, hI, by simp⟩
  intro f df mf hf
  choose! I t hI hf using hf
  refine ⟨⋃ n, I n, ⋃ n, (⋃ k, I k).domRestrict '' (f n), countable_iUnion hI, ?_⟩
  ext x
  simp only [hf, mem_iUnion, mem_preimage, preimage_iUnion, mem_image]
  refine ⟨fun ⟨i, hi⟩ => ⟨i, x, hi, rfl⟩, fun ⟨n, x', hn, hx⟩ => ⟨n, ?_⟩⟩
  have (x : Π i, α i) : (I n).domRestrict x =
      (fun (x : Π (i : ⋃ k, I k), α i) (i : I n) => x ⟨i.1, subset_iUnion I n i.2⟩)
      ((⋃ k, I k).domRestrict x) := rfl
  rwa [this, ← hx, ← this]

end MeasureTheory
