/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Congruence
public import Mathlib.Topology.MetricSpace.Dilation
public import Mathlib.Tactic.FinCases

/-!
# Similarities

This file defines `Similar`, i.e., the equivalence between indexed sets of points in a metric space
where all corresponding pairwise distances have the same ratio. The motivating example is
triangles in the plane.

## Implementation notes

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation
Let `P₁` and `P₂` be metric spaces, let `ι` be an index set, and let `v₁ : ι → P₁` and
`v₂ : ι → P₂` be indexed families of points.

* `(v₁ ∼ v₂ : Prop)` represents that `(v₁ : ι → P₁)` and `(v₂ : ι → P₂)` are similar.
-/

@[expose] public section

open scoped NNReal

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι -> P₁} {v₂ : ι -> P₂} {v₃ : ι -> P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]

/--
Definition of `Similar` / `Similar` 的定义

English:
definition Similar
  signature: (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  body: exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similar] infixl:25 " ∼ " => Similar

中文:
定义 Similar
  签名: (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  定义体: exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similar] infixl:25 " ∼ " => Similar
-/
def Similar (v₁ : ι -> P₁) (v₂ : ι -> P₂) : Prop :=
  exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similar] infixl:25 " ∼ " => Similar

/--
lemma `similar_iff_exists_edist_eq` / 引理 `similar_iff_exists_edist_eq`

English:
lemma similar_iff_exists_edist_eq
  proof: Iff.rfl

中文:
引理 similar_iff_存在_edist_eq
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma similar_iff_exists_edist_eq :
    Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) :=
  Iff.rfl

/--
lemma `similar_iff_exists_pairwise_edist_eq` / 引理 `similar_iff_exists_pairwise_edist_eq`

English:
lemma similar_iff_exists_pairwise_edist_eq
  proof: by
  rw [similar_iff_exists_edist_eq]
  refine ⟨?_, ?_⟩ <;> rintro ⟨r, hr, h⟩ <;> refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  · exact fun _ => h i₁ i₂
  · by_cases hi : i₁ = i₂
    · simp [hi]
    · exact h hi

中文:
引理 similar_iff_存在_pairwise_edist_eq
  证明: by
  rw [similar_iff_exists_edist_eq]
  refine ⟨?_, ?_⟩ <;> rintro ⟨r, hr, h⟩ <;> refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  · exact fun _ => h i₁ i₂
  · by_cases hi : i₁ = i₂
    · simp [hi]
    · exact h hi

Depends on / 依赖: similar_iff_exists_edist_eq
-/
lemma similar_iff_exists_pairwise_edist_eq :
    Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧ Pairwise fun i₁ i₂ => (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_edist_eq]
  refine ⟨?_, ?_⟩ <;> rintro ⟨r, hr, h⟩ <;> refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  · exact fun _ => h i₁ i₂
  · by_cases hi : i₁ = i₂
    · simp [hi]
    · exact h hi

/--
lemma `Congruent.similar` / 引理 `Congruent.similar`

English:
lemma Congruent.similar
  given: {v₁ : ι -> P₁} {v₂ : ι -> P₂} (h : Congruent v₁ v₂)
  statement: Similar v₁ v₂
  proof: ⟨1, one_ne_zero, fun i₁ i₂ => by simpa using h i₁ i₂⟩

中文:
引理 Congruent.similar
  条件: {v₁ : ι -> P₁} {v₂ : ι -> P₂} (h : Congruent v₁ v₂)
  结论: Similar v₁ v₂
  证明: ⟨1, one_ne_zero, fun i₁ i₂ => by simpa using h i₁ i₂⟩

Depends on / 依赖: one_ne_zero
-/
lemma Congruent.similar {v₁ : ι -> P₁} {v₂ : ι -> P₂} (h : Congruent v₁ v₂) : Similar v₁ v₂ :=
  ⟨1, one_ne_zero, fun i₁ i₂ => by simpa using h i₁ i₂⟩

namespace Similar

/-- A similarity scales extended distance. Forward direction of `similar_iff_exists_edist_eq`. -/
alias ⟨exists_edist_eq, _⟩ := similar_iff_exists_edist_eq

/-- Similarity follows from scaled extended distance. Backward direction of
`similar_iff_exists_edist_eq`. -/
alias ⟨_, of_exists_edist_eq⟩ := similar_iff_exists_edist_eq

/-- A similarity pairwise scales extended distance. Forward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨exists_pairwise_edist_eq, _⟩ := similar_iff_exists_pairwise_edist_eq

/-- Similarity follows from pairwise scaled extended distance. Backward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨_, of_exists_pairwise_edist_eq⟩ := similar_iff_exists_pairwise_edist_eq

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (v₁ : ι -> P₁)
  statement: v₁ ∼ v₁
  proof: ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩

中文:
引理 refl
  条件: (v₁ : ι -> P₁)
  结论: v₁ ∼ v₁
  证明: ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩
-/
@[refl] protected lemma refl (v₁ : ι -> P₁) : v₁ ∼ v₁ :=
  ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (h : v₁ ∼ v₂)
  statement: v₂ ∼ v₁
  proof: by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr]; rw [← ENNReal.div_eq_inv_mul]; rw [ENNReal.eq_div_iff _ ENNReal.coe_ne_top]; rw [h]
  norm_cast

中文:
引理 symm
  条件: (h : v₁ ∼ v₂)
  结论: v₂ ∼ v₁
  证明: by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr]; rw [← ENNReal.div_eq_inv_mul]; rw [ENNReal.eq_div_iff _ ENNReal.coe_ne_top]; rw [h]
  norm_cast
-/
@[symm] protected lemma symm (h : v₁ ∼ v₂) : v₂ ∼ v₁ := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr]; rw [← ENNReal.div_eq_inv_mul]; rw [ENNReal.eq_div_iff _ ENNReal.coe_ne_top]; rw [h]
  norm_cast

/--
lemma `_root_.similar_comm` / 引理 `_root_.similar_comm`

English:
lemma _root_.similar_comm
  statement: v₁ ∼ v₂ ↔ v₂ ∼ v₁
  proof: ⟨Similar.symm, Similar.symm⟩

中文:
引理 _root_.similar_comm
  结论: v₁ ∼ v₂ ↔ v₂ ∼ v₁
  证明: ⟨Similar.symm, Similar.symm⟩

Depends on / 依赖: Similar, Similar.symm
-/
lemma _root_.similar_comm : v₁ ∼ v₂ ↔ v₂ ∼ v₁ := ⟨Similar.symm, Similar.symm⟩

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃)
  statement: v₁ ∼ v₃
  proof: by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul]; rw [mul_assoc]; rw [h₁]; rw [h₂]

中文:
引理 trans
  条件: (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃)
  结论: v₁ ∼ v₃
  证明: by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul]; rw [mul_assoc]; rw [h₁]; rw [h₂]
-/
@[trans] protected lemma trans (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃) : v₁ ∼ v₃ := by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul]; rw [mul_assoc]; rw [h₁]; rw [h₂]

/--
lemma `index_map` / 引理 `index_map`

English:
lemma index_map
  given: (h : v₁ ∼ v₂) (f : ι' -> ι)
  statement: (v₁ ∘ f) ∼ (v₂ ∘ f)
  proof: by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h

中文:
引理 index_map
  条件: (h : v₁ ∼ v₂) (f : ι' -> ι)
  结论: (v₁ ∘ f) ∼ (v₂ ∘ f)
  证明: by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h
-/
lemma index_map (h : v₁ ∼ v₂) (f : ι' -> ι) : (v₁ ∘ f) ∼ (v₂ ∘ f) := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h

/-- Change between equivalent index sets ι and ι'. -/
@[simp]
/--
lemma `index_equiv` / 引理 `index_equiv`

English:
lemma index_equiv
  given: (f : ι' ≃ ι) (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  proof: by
  refine ⟨fun h => ?_, fun h => Similar.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

中文:
引理 index_equiv
  条件: (f : ι' ≃ ι) (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  证明: by
  refine ⟨fun h => ?_, fun h => Similar.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

Depends on / 依赖: Similar, Similar.index_map, f.right_inv, f.symm, index_map, right_inv
-/
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι -> P₁) (v₂ : ι -> P₂) :
    v₁ ∘ f ∼ v₂ ∘ f ↔ v₁ ∼ v₂ := by
  refine ⟨fun h => ?_, fun h => Similar.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

/-- Families with at most a single point are always similar. -/
@[nontriviality, simp]
/--
lemma `of_subsingleton_index` / 引理 `of_subsingleton_index`

English:
lemma of_subsingleton_index
  given: [Subsingleton ι]
  statement: v₁ ∼ v₂
  proof: Congruent.of_subsingleton_index.similar

中文:
引理 of_subsingleton_index
  条件: [子单例 ι]
  结论: v₁ ∼ v₂
  证明: Congruent.of_subsingleton_index.similar

Depends on / 依赖: Congruent, Congruent.of_subsingleton_index.similar, of_subsingleton_index, similar
-/
lemma of_subsingleton_index [Subsingleton ι] : v₁ ∼ v₂ :=
  Congruent.of_subsingleton_index.similar

/-! Similarity is preserved under dilations. -/

section Dilation
variable {F}

/--
lemma `comp_left` / 引理 `comp_left`

English:
lemma comp_left
  given: [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) (h : v₁ ∼ v₂)
  proof: .trans ⟨Dilation.ratio f, Dilation.ratio_ne_zero f, fun _ _ => Dilation.edist_eq f _ _⟩ h

中文:
引理 comp_left
  条件: [函数状 F P₁ P₃] [Dilation类 F P₁ P₃] (f : F) (h : v₁ ∼ v₂)
  证明: .trans ⟨Dilation.ratio f, Dilation.ratio_ne_zero f, fun _ _ => Dilation.edist_eq f _ _⟩ h

Depends on / 依赖: Dilation, Dilation.edist_eq, Dilation.ratio, Dilation.ratio_ne_zero, edist_eq, ratio_ne_zero
-/
lemma comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) (h : v₁ ∼ v₂) :
    f ∘ v₁ ∼ v₂ :=
  .trans ⟨Dilation.ratio f, Dilation.ratio_ne_zero f, fun _ _ => Dilation.edist_eq f _ _⟩ h

/--
lemma `comp_right` / 引理 `comp_right`

English:
lemma comp_right
  given: [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) (h : v₁ ∼ v₂)
  statement: v₁ ∼ f ∘ v₂
  proof: .symm (h.symm.comp_left f)

@[simp]

中文:
引理 comp_right
  条件: [函数状 F P₂ P₃] [Dilation类 F P₂ P₃] (f : F) (h : v₁ ∼ v₂)
  结论: v₁ ∼ f ∘ v₂
  证明: .symm (h.symm.comp_left f)

@[simp]

Depends on / 依赖: comp_left, h.symm.comp_left
-/
lemma comp_right [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂ :=
  .symm (h.symm.comp_left f)

@[simp]
/--
lemma `comp_left_iff` / 引理 `comp_left_iff`

English:
lemma comp_left_iff
  given: [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F)
  statement: f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂
  proof: ⟨.trans .comp_right f (.refl _), .comp_left f⟩

@[simp]

中文:
引理 comp_left_iff
  条件: [函数状 F P₁ P₃] [Dilation类 F P₁ P₃] (f : F)
  结论: f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂
  证明: ⟨.trans .comp_right f (.refl _), .comp_left f⟩

@[simp]

Depends on / 依赖: comp_left, comp_right
-/
lemma comp_left_iff [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂ :=
⟨.trans .comp_right f (.refl _), .comp_left f⟩

@[simp]
/--
lemma `comp_right_iff` / 引理 `comp_right_iff`

English:
lemma comp_right_iff
  given: [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F)
  statement: v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂
  proof: by
  rw [similar_comm]; rw [comp_left_iff]; rw [similar_comm]

中文:
引理 comp_right_iff
  条件: [函数状 F P₂ P₃] [Dilation类 F P₂ P₃] (f : F)
  结论: v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂
  证明: by
  rw [similar_comm]; rw [comp_left_iff]; rw [similar_comm]

Depends on / 依赖: comp_left_iff, similar_comm
-/
lemma comp_right_iff [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂ := by
  rw [similar_comm]; rw [comp_left_iff]; rw [similar_comm]

end Dilation

/-! Similarity is preserved under isometries.

While these are trivial consequences of the dilation results, they avoid ending up with a
`toDilation` in the expression, and so are easier to apply to plain functions.
If `Dilation` were a predicate like `Isometry` then these would not be needed.
-/

section Isometry

/--
lemma `comp_isometry_left` / 引理 `comp_isometry_left`

English:
lemma comp_isometry_left
  given: {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ ∼ v₂)
  statement: f ∘ v₁ ∼ v₂
  proof: comp_left hf.toDilation h

中文:
引理 comp_isometry_left
  条件: {f : P₁ -> P₃} (hf : 等距 f) (h : v₁ ∼ v₂)
  结论: f ∘ v₁ ∼ v₂
  证明: comp_left hf.toDilation h

Depends on / 依赖: comp_left, hf.toDilation, toDilation
-/
lemma comp_isometry_left {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : f ∘ v₁ ∼ v₂ :=
  comp_left hf.toDilation h

/--
lemma `comp_isometry_right` / 引理 `comp_isometry_right`

English:
lemma comp_isometry_right
  given: {f : P₂ -> P₃} (hf : Isometry f) (h : v₁ ∼ v₂)
  statement: v₁ ∼ f ∘ v₂
  proof: comp_right hf.toDilation h

@[simp]

中文:
引理 comp_isometry_right
  条件: {f : P₂ -> P₃} (hf : 等距 f) (h : v₁ ∼ v₂)
  结论: v₁ ∼ f ∘ v₂
  证明: comp_right hf.toDilation h

@[simp]

Depends on / 依赖: comp_right, hf.toDilation, toDilation
-/
lemma comp_isometry_right {f : P₂ -> P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂ :=
  comp_right hf.toDilation h

@[simp]
/--
lemma `comp_isometry_left_iff` / 引理 `comp_isometry_left_iff`

English:
lemma comp_isometry_left_iff
  given: {f : P₁ -> P₃} (hf : Isometry f)
  statement: f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂
  proof: comp_left_iff hf.toDilation

@[simp]

中文:
引理 comp_isometry_left_iff
  条件: {f : P₁ -> P₃} (hf : 等距 f)
  结论: f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂
  证明: comp_left_iff hf.toDilation

@[simp]

Depends on / 依赖: comp_left_iff, hf.toDilation, toDilation
-/
lemma comp_isometry_left_iff {f : P₁ -> P₃} (hf : Isometry f) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂ :=
  comp_left_iff hf.toDilation

@[simp]
/--
lemma `comp_isometry_right_iff` / 引理 `comp_isometry_right_iff`

English:
lemma comp_isometry_right_iff
  given: {f : P₂ -> P₃} (hf : Isometry f)
  statement: v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂
  proof: comp_right_iff hf.toDilation

中文:
引理 comp_isometry_right_iff
  条件: {f : P₂ -> P₃} (hf : 等距 f)
  结论: v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂
  证明: comp_right_iff hf.toDilation

Depends on / 依赖: comp_right_iff, hf.toDilation, toDilation
-/
lemma comp_isometry_right_iff {f : P₂ -> P₃} (hf : Isometry f) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂ :=
  comp_right_iff hf.toDilation

end Isometry

section Triangle

variable {a b c : P₁} {a' b' c' : P₂}

/--
theorem `comm_left` / 定理 `comm_left`

English:
theorem comm_left
  given: (h : ![a, b, c] ∼ ![a', b', c'])
  proof: by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

中文:
定理 comm_left
  条件: (h : ![a, b, c] ∼ ![a', b', c'])
  证明: by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

Depends on / 依赖: Equiv.swap, Equiv.swap_apply_of_ne_of_ne, fin_cases, index_equiv, swap_apply_of_ne_of_ne
-/
theorem comm_left (h : ![a, b, c] ∼ ![a', b', c']) :
    ![b, a, c] ∼ ![b', a', c'] := by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

/--
theorem `comm_right` / 定理 `comm_right`

English:
theorem comm_right
  given: (h : ![a, b, c] ∼ ![a', b', c'])
  proof: by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

中文:
定理 comm_right
  条件: (h : ![a, b, c] ∼ ![a', b', c'])
  证明: by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

Depends on / 依赖: Equiv.swap, Equiv.swap_apply_of_ne_of_ne, fin_cases, index_equiv, swap_apply_of_ne_of_ne
-/
theorem comm_right (h : ![a, b, c] ∼ ![a', b', c']) :
    ![a, c, b] ∼ ![a', c', b'] := by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

/--
theorem `reverse_of_three` / 定理 `reverse_of_three`

English:
theorem reverse_of_three
  given: (h : ![a, b, c] ∼ ![a', b', c'])
  proof: h.comm_left.comm_right.comm_left

中文:
定理 reverse_of_three
  条件: (h : ![a, b, c] ∼ ![a', b', c'])
  证明: h.comm_left.comm_right.comm_left

Depends on / 依赖: comm_left, comm_right, h.comm_left.comm_right.comm_left
-/
theorem reverse_of_three (h : ![a, b, c] ∼ ![a', b', c']) :
    ![c, b, a] ∼ ![c', b', a'] :=
  h.comm_left.comm_right.comm_left

end Triangle

end Similar

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/--
lemma `similar_iff_exists_nndist_eq` / 引理 `similar_iff_exists_nndist_eq`

English:
lemma similar_iff_exists_nndist_eq
  proof: exists_congr fun _ => and_congr Iff.rfl forall₂_congr
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

中文:
引理 similar_iff_存在_nndist_eq
  证明: exists_congr fun _ => and_congr Iff.rfl forall₂_congr
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

Depends on / 依赖: Iff.rfl, and_congr, edist_nndist, exists_congr
-/
lemma similar_iff_exists_nndist_eq :
    Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) :=
exists_congr fun _ => and_congr Iff.rfl forall₂_congr
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

/--
lemma `similar_iff_exists_pairwise_nndist_eq` / 引理 `similar_iff_exists_pairwise_nndist_eq`

English:
lemma similar_iff_exists_pairwise_nndist_eq
  proof: by
  simp_rw [similar_iff_exists_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

中文:
引理 similar_iff_存在_pairwise_nndist_eq
  证明: by
  simp_rw [similar_iff_exists_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

Depends on / 依赖: Iff.rfl, edist_nndist, similar_iff_exists_pairwise_edist_eq, simp_rw
-/
lemma similar_iff_exists_pairwise_nndist_eq :
    Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧ Pairwise fun i₁ i₂ => (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/--
lemma `similar_iff_exists_dist_eq` / 引理 `similar_iff_exists_dist_eq`

English:
lemma similar_iff_exists_dist_eq
  proof: similar_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

中文:
引理 similar_iff_存在_dist_eq
  证明: similar_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

Depends on / 依赖: Iff.rfl, and_congr, dist_nndist, exists_congr, similar_iff_exists_nndist_eq, similar_iff_exists_nndist_eq.trans
-/
lemma similar_iff_exists_dist_eq :
    Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) :=
  similar_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

/--
lemma `similar_iff_exists_pairwise_dist_eq` / 引理 `similar_iff_exists_pairwise_dist_eq`

English:
lemma similar_iff_exists_pairwise_dist_eq
  proof: by
  simp_rw [similar_iff_exists_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

中文:
引理 similar_iff_存在_pairwise_dist_eq
  证明: by
  simp_rw [similar_iff_exists_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

Depends on / 依赖: Iff.rfl, dist_nndist, similar_iff_exists_pairwise_nndist_eq, simp_rw
-/
lemma similar_iff_exists_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧ Pairwise fun i₁ i₂ => (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

/--
lemma `similar_iff_exists_pos_dist_eq` / 引理 `similar_iff_exists_pos_dist_eq`

English:
lemma similar_iff_exists_pos_dist_eq
  statement: Similar v₁ v₂ ↔
  proof: by
  rw [similar_iff_exists_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

中文:
引理 similar_iff_存在_pos_dist_eq
  结论: Similar v₁ v₂ ↔
  证明: by
  rw [similar_iff_exists_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

Depends on / 依赖: NNReal, NNReal.coe_mk, NNReal.coe_pos, NNReal.exists, coe_mk, coe_pos, pos_iff_ne_zero, similar_iff_exists_dist_eq, simp_rw
-/
lemma similar_iff_exists_pos_dist_eq : Similar v₁ v₂ ↔
    (exists r : Real, 0 < r ∧ forall (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

/--
lemma `similar_iff_exists_pos_pairwise_dist_eq` / 引理 `similar_iff_exists_pos_pairwise_dist_eq`

English:
lemma similar_iff_exists_pos_pairwise_dist_eq
  proof: by
  simp_rw [similar_iff_exists_pairwise_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

中文:
引理 similar_iff_存在_pos_pairwise_dist_eq
  证明: by
  simp_rw [similar_iff_exists_pairwise_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

Depends on / 依赖: NNReal, NNReal.coe_mk, NNReal.coe_pos, NNReal.exists, coe_mk, coe_pos, pos_iff_ne_zero, similar_iff_exists_pairwise_dist_eq, simp_rw
-/
lemma similar_iff_exists_pos_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (exists r : Real, 0 < r ∧ Pairwise fun i₁ i₂ => (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

namespace Similar

/-- A similarity scales non-negative distance. Forward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨exists_nndist_eq, _⟩ := similar_iff_exists_nndist_eq

/-- Similarity follows from scaled non-negative distance. Backward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨_, of_exists_nndist_eq⟩ := similar_iff_exists_nndist_eq

/-- A similarity scales distance. Forward direction of `similar_iff_exists_dist_eq`. -/
alias ⟨exists_dist_eq, _⟩ := similar_iff_exists_dist_eq

/-- Similarity follows from scaled distance. Backward direction of
`similar_iff_exists_dist_eq`. -/
alias ⟨_, of_exists_dist_eq⟩ := similar_iff_exists_dist_eq

/-- A similarity pairwise scales non-negative distance. Forward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨exists_pairwise_nndist_eq, _⟩ := similar_iff_exists_pairwise_nndist_eq

/-- Similarity follows from pairwise scaled non-negative distance. Backward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨_, of_exists_pairwise_nndist_eq⟩ := similar_iff_exists_pairwise_nndist_eq

/-- A similarity pairwise scales distance. Forward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨exists_pairwise_dist_eq, _⟩ := similar_iff_exists_pairwise_dist_eq

/-- Similarity follows from pairwise scaled distance. Backward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pairwise_dist_eq⟩ := similar_iff_exists_pairwise_dist_eq

/-- Scales distance with positive ratio. Forward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨exists_pos_dist_eq, _⟩ := similar_iff_exists_pos_dist_eq

/-- Similarity from scaled positive distance. Backward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨_, of_exists_pos_dist_eq⟩ := similar_iff_exists_pos_dist_eq

/-- Scales pairwise distance with positive ratio. Forward of
`similar_iff_exists_pos_pairwise_dist_eq`. -/
alias ⟨exists_pos_pairwise_dist_eq, _⟩ := similar_iff_exists_pos_pairwise_dist_eq

/-- Similarity from scaled pairwise positive distance. Backward of
`similar_iff_exists_pos_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pos_pairwise_dist_eq⟩ := similar_iff_exists_pos_pairwise_dist_eq

end Similar

section Triangle

variable {a b c : P₁} {a' b' c' : P₂}

/--
theorem `similar_of_dist_mul_eq_dist_mul_eq` / 定理 `similar_of_dist_mul_eq_dist_mul_eq`

English:
theorem similar_of_dist_mul_eq_dist_mul_eq
  statement: (h_ne : dist a b != 0) (h_ne' : dist a' b' != 0)
  proof: by
  set r : Real := (dist a b / dist a' b') with hr
  have hr_pos : 0 < r := by positivity
  apply Similar.of_exists_pos_pairwise_dist_eq
  use r
  refine ⟨hr_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

alias similar_of_side_side := similar_of_dist_mul_eq_dist_mul_eq

中文:
定理 similar_of_dist_mul_eq_dist_mul_eq
  结论: (h_ne : dist a b != 0) (h_ne' : dist a' b' != 0)
  证明: by
  set r : Real := (dist a b / dist a' b') with hr
  have hr_pos : 0 < r := by positivity
  apply Similar.of_exists_pos_pairwise_dist_eq
  use r
  refine ⟨hr_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

alias similar_of_side_side := similar_of_dist_mul_eq_dist_mul_eq

Depends on / 依赖: Similar, Similar.of_exists_pos_pairwise_dist_eq, all_goals, dist_comm, dist_self, fin_cases, hr_pos, mul_zero, of_exists_pos_pairwise_dist_eq
-/
theorem similar_of_dist_mul_eq_dist_mul_eq (h_ne : dist a b != 0) (h_ne' : dist a' b' != 0)
    (heq1 : dist a b * dist b' c' = dist b c * dist a' b')
    (heq2 : dist a b * dist c' a' = dist c a * dist a' b') :
    Similar ![a, b, c] ![a', b', c'] := by
  set r : Real := (dist a b / dist a' b') with hr
  have hr_pos : 0 < r := by positivity
  apply Similar.of_exists_pos_pairwise_dist_eq
  use r
  refine ⟨hr_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

alias similar_of_side_side := similar_of_dist_mul_eq_dist_mul_eq

end Triangle

end PseudoMetricSpace
