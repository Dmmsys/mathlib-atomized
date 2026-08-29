/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Dilation

/-!
# Congruences

This file defines `Congruent`, i.e., the equivalence between indexed families of points in a metric
space where all corresponding pairwise distances are the same. The motivating example are
triangles in the plane.

## Implementation notes

After considering two possible approaches to defining congruence — either based on equal pairwise
distances or the existence of an isometric equivalence — we have opted for the broader concept of
equal pairwise distances. This notion is commonly employed in the literature across various metric
spaces that lack an isometric equivalence.

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation

* `v₁ ≅ v₂`: for `Congruent v₁ v₂`.
-/

@[expose] public section

variable {ι ι' : Type*} {P₁ P₂ P₃ P₄ : Type*} {v₁ : ι -> P₁} {v₂ : ι -> P₂} {v₃ : ι -> P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂]
variable [PseudoEMetricSpace P₃] [PseudoEMetricSpace P₄]

/--
Definition of `Congruent` / `Congruent` 的定义

English:
definition Congruent
  signature: (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  body: forall i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)

@[inherit_doc]
scoped[Congruent] infixl:25 " ≅ " => Congruent

中文:
定义 Congruent
  签名: (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  定义体: forall i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)

@[inherit_doc]
scoped[Congruent] infixl:25 " ≅ " => Congruent
-/
def Congruent (v₁ : ι -> P₁) (v₂ : ι -> P₂) : Prop :=
  forall i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)

@[inherit_doc]
scoped[Congruent] infixl:25 " ≅ " => Congruent

/--
lemma `congruent_iff_edist_eq` / 引理 `congruent_iff_edist_eq`

English:
lemma congruent_iff_edist_eq
  proof: Iff.rfl

中文:
引理 congruent_iff_edist_eq
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma congruent_iff_edist_eq :
    Congruent v₁ v₂ ↔ forall i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) :=
  Iff.rfl

/--
lemma `congruent_iff_pairwise_edist_eq` / 引理 `congruent_iff_pairwise_edist_eq`

English:
lemma congruent_iff_pairwise_edist_eq
  proof: by
  refine ⟨fun h => fun _ _ _ => h _ _, fun h => fun i₁ i₂ => ?_⟩
  by_cases hi : i₁ = i₂
  · simp [hi]
  · exact h hi

中文:
引理 congruent_iff_pairwise_edist_eq
  证明: by
  refine ⟨fun h => fun _ _ _ => h _ _, fun h => fun i₁ i₂ => ?_⟩
  by_cases hi : i₁ = i₂
  · simp [hi]
  · exact h hi
-/
lemma congruent_iff_pairwise_edist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ => edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) := by
  refine ⟨fun h => fun _ _ _ => h _ _, fun h => fun i₁ i₂ => ?_⟩
  by_cases hi : i₁ = i₂
  · simp [hi]
  · exact h hi

namespace Congruent

/-- A congruence preserves extended distance. Forward direction of `congruent_iff_edist_eq`. -/
alias ⟨edist_eq, _⟩ := congruent_iff_edist_eq

/-- Congruence follows from preserved extended distance. Backward direction of
`congruent_iff_edist_eq`. -/
alias ⟨_, of_edist_eq⟩ := congruent_iff_edist_eq

/-- A congruence pairwise preserves extended distance. Forward direction of
`congruent_iff_pairwise_edist_eq`. -/
alias ⟨pairwise_edist_eq, _⟩ := congruent_iff_pairwise_edist_eq

/-- Congruence follows from pairwise preserved extended distance. Backward direction of
`congruent_iff_pairwise_edist_eq`. -/
alias ⟨_, of_pairwise_edist_eq⟩ := congruent_iff_pairwise_edist_eq

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (v₁ : ι -> P₁)
  statement: v₁ ≅ v₁
  proof: fun _ _ => rfl

中文:
引理 refl
  条件: (v₁ : ι -> P₁)
  结论: v₁ ≅ v₁
  证明: fun _ _ => rfl
-/
@[refl] protected lemma refl (v₁ : ι -> P₁) : v₁ ≅ v₁ := fun _ _ => rfl

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (h : v₁ ≅ v₂)
  statement: v₂ ≅ v₁
  proof: fun i₁ i₂ => (h i₁ i₂).symm

中文:
引理 symm
  条件: (h : v₁ ≅ v₂)
  结论: v₂ ≅ v₁
  证明: fun i₁ i₂ => (h i₁ i₂).symm
-/
@[symm] protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := fun i₁ i₂ => (h i₁ i₂).symm

/--
lemma `_root_.congruent_comm` / 引理 `_root_.congruent_comm`

English:
lemma _root_.congruent_comm
  statement: v₁ ≅ v₂ ↔ v₂ ≅ v₁
  proof: ⟨Congruent.symm, Congruent.symm⟩

中文:
引理 _root_.congruent_comm
  结论: v₁ ≅ v₂ ↔ v₂ ≅ v₁
  证明: ⟨Congruent.symm, Congruent.symm⟩

Depends on / 依赖: Congruent, Congruent.symm
-/
lemma _root_.congruent_comm : v₁ ≅ v₂ ↔ v₂ ≅ v₁ :=
  ⟨Congruent.symm, Congruent.symm⟩

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃)
  statement: v₁ ≅ v₃
  proof: fun i₁ i₂ => (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)

中文:
引理 trans
  条件: (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃)
  结论: v₁ ≅ v₃
  证明: fun i₁ i₂ => (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)
-/
@[trans] protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
  fun i₁ i₂ => (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)

/--
lemma `index_map` / 引理 `index_map`

English:
lemma index_map
  given: (h : v₁ ≅ v₂) (f : ι' -> ι)
  statement: (v₁ ∘ f) ≅ (v₂ ∘ f)
  proof: fun i₁ i₂ => edist_eq h (f i₁) (f i₂)

中文:
引理 index_map
  条件: (h : v₁ ≅ v₂) (f : ι' -> ι)
  结论: (v₁ ∘ f) ≅ (v₂ ∘ f)
  证明: fun i₁ i₂ => edist_eq h (f i₁) (f i₂)

Depends on / 依赖: edist_eq
-/
lemma index_map (h : v₁ ≅ v₂) (f : ι' -> ι) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
  fun i₁ i₂ => edist_eq h (f i₁) (f i₂)

/--
lemma `index_equiv` / 引理 `index_equiv`

English:
lemma index_equiv
  given: {E : Type*} [EquivLike E ι' ι] (f : E) (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  proof: by
  refine ⟨fun h i₁ i₂ => ?_, fun h => index_map h f⟩
  simpa [(EquivLike.toEquiv f).right_inv i₁, (EquivLike.toEquiv f).right_inv i₂]
    using edist_eq h ((EquivLike.toEquiv f).symm i₁) ((EquivLike.toEquiv f).symm i₂)

中文:
引理 index_equiv
  条件: {E : 类型} [等价状 E ι' ι] (f : E) (v₁ : ι -> P₁) (v₂ : ι -> P₂)
  证明: by
  refine ⟨fun h i₁ i₂ => ?_, fun h => index_map h f⟩
  simpa [(EquivLike.toEquiv f).right_inv i₁, (EquivLike.toEquiv f).right_inv i₂]
    using edist_eq h ((EquivLike.toEquiv f).symm i₁) ((EquivLike.toEquiv f).symm i₂)
-/
@[simp] lemma index_equiv {E : Type*} [EquivLike E ι' ι] (f : E) (v₁ : ι -> P₁) (v₂ : ι -> P₂) :
    v₁ ∘ f ≅ v₂ ∘ f ↔ v₁ ≅ v₂ := by
  refine ⟨fun h i₁ i₂ => ?_, fun h => index_map h f⟩
  simpa [(EquivLike.toEquiv f).right_inv i₁, (EquivLike.toEquiv f).right_inv i₂]
    using edist_eq h ((EquivLike.toEquiv f).symm i₁) ((EquivLike.toEquiv f).symm i₂)

/-- Families with at most a single point are always congruent. -/
@[nontriviality, simp]
/--
lemma `of_subsingleton_index` / 引理 `of_subsingleton_index`

English:
lemma of_subsingleton_index
  given: [Subsingleton ι]
  statement: v₁ ≅ v₂
  proof: fun i j => by simp [Subsingleton.elim i j]

中文:
引理 of_subsingleton_index
  条件: [子单例 ι]
  结论: v₁ ≅ v₂
  证明: fun i j => by simp [Subsingleton.elim i j]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma of_subsingleton_index [Subsingleton ι] : v₁ ≅ v₂ :=
  fun i j => by simp [Subsingleton.elim i j]

/--
lemma `comp_left` / 引理 `comp_left`

English:
lemma comp_left
  given: {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ ≅ v₂)
  statement: f ∘ v₁ ≅ v₂
  proof: .trans (fun _ _ => hf _ _) h

中文:
引理 comp_left
  条件: {f : P₁ -> P₃} (hf : 等距 f) (h : v₁ ≅ v₂)
  结论: f ∘ v₁ ≅ v₂
  证明: .trans (fun _ _ => hf _ _) h
-/
lemma comp_left {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : f ∘ v₁ ≅ v₂ :=
  .trans (fun _ _ => hf _ _) h

/--
lemma `comp_right` / 引理 `comp_right`

English:
lemma comp_right
  given: {f : P₂ -> P₃} (hf : Isometry f) (h : v₁ ≅ v₂)
  statement: v₁ ≅ f ∘ v₂
  proof: .trans h (.symm <| fun _ _ => hf _ _)

@[simp]

中文:
引理 comp_right
  条件: {f : P₂ -> P₃} (hf : 等距 f) (h : v₁ ≅ v₂)
  结论: v₁ ≅ f ∘ v₂
  证明: .trans h (.symm <| fun _ _ => hf _ _)

@[simp]
-/
lemma comp_right {f : P₂ -> P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : v₁ ≅ f ∘ v₂ :=
  .trans h (.symm <| fun _ _ => hf _ _)

@[simp]
/--
lemma `comp_left_iff` / 引理 `comp_left_iff`

English:
lemma comp_left_iff
  given: {f : P₁ -> P₃} (hf : Isometry f)
  statement: f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂
  proof: ⟨.trans .comp_right hf (.refl _), .comp_left hf⟩

@[simp]

中文:
引理 comp_left_iff
  条件: {f : P₁ -> P₃} (hf : 等距 f)
  结论: f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂
  证明: ⟨.trans .comp_right hf (.refl _), .comp_left hf⟩

@[simp]

Depends on / 依赖: comp_left, comp_right
-/
lemma comp_left_iff {f : P₁ -> P₃} (hf : Isometry f) : f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂ :=
⟨.trans .comp_right hf (.refl _), .comp_left hf⟩

@[simp]
/--
lemma `comp_right_iff` / 引理 `comp_right_iff`

English:
lemma comp_right_iff
  given: {f : P₂ -> P₃} (hf : Isometry f)
  statement: v₁ ≅ f ∘ v₂ ↔ v₁ ≅ v₂
  proof: by
  rw [congruent_comm]; rw [comp_left_iff hf]; rw [congruent_comm]

中文:
引理 comp_right_iff
  条件: {f : P₂ -> P₃} (hf : 等距 f)
  结论: v₁ ≅ f ∘ v₂ ↔ v₁ ≅ v₂
  证明: by
  rw [congruent_comm]; rw [comp_left_iff hf]; rw [congruent_comm]

Depends on / 依赖: comp_left_iff, congruent_comm
-/
lemma comp_right_iff {f : P₂ -> P₃} (hf : Isometry f) : v₁ ≅ f ∘ v₂ ↔ v₁ ≅ v₂ := by
  rw [congruent_comm]; rw [comp_left_iff hf]; rw [congruent_comm]

/--
lemma `comp_dilation` / 引理 `comp_dilation`

English:
lemma comp_dilation
  statement: {F₁ F₂}
  proof: fun i j => by simp [hf, h i j]

中文:
引理 comp_dilation
  结论: {F₁ F₂}
  证明: fun i j => by simp [hf, h i j]
-/
lemma comp_dilation {F₁ F₂}
    [FunLike F₁ P₁ P₃] [DilationClass F₁ P₁ P₃] [FunLike F₂ P₂ P₄] [DilationClass F₂ P₂ P₄]
    {f₁ : F₁} {f₂ : F₂} (h : v₁ ≅ v₂) (hf : Dilation.ratio f₁ = Dilation.ratio f₂) :
    f₁ ∘ v₁ ≅ f₂ ∘ v₂ :=
  fun i j => by simp [hf, h i j]

end Congruent

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/--
lemma `congruent_iff_nndist_eq` / 引理 `congruent_iff_nndist_eq`

English:
lemma congruent_iff_nndist_eq
  proof: forall₂_congr (fun _ _ => by rw [edist_nndist, edist_nndist]; norm_cast)

中文:
引理 congruent_iff_nndist_eq
  证明: forall₂_congr (fun _ _ => by rw [edist_nndist, edist_nndist]; norm_cast)

Depends on / 依赖: edist_nndist
-/
lemma congruent_iff_nndist_eq :
    Congruent v₁ v₂ ↔ forall i₁ i₂, nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) :=
  forall₂_congr (fun _ _ => by rw [edist_nndist, edist_nndist]; norm_cast)

/--
lemma `congruent_iff_pairwise_nndist_eq` / 引理 `congruent_iff_pairwise_nndist_eq`

English:
lemma congruent_iff_pairwise_nndist_eq
  proof: by
  simp_rw [congruent_iff_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

中文:
引理 congruent_iff_pairwise_nndist_eq
  证明: by
  simp_rw [congruent_iff_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

Depends on / 依赖: Iff.rfl, congruent_iff_pairwise_edist_eq, edist_nndist, simp_rw
-/
lemma congruent_iff_pairwise_nndist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ => nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) := by
  simp_rw [congruent_iff_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/--
lemma `congruent_iff_dist_eq` / 引理 `congruent_iff_dist_eq`

English:
lemma congruent_iff_dist_eq
  proof: congruent_iff_nndist_eq.trans
    (forall₂_congr (fun _ _ => by rw [dist_nndist, dist_nndist]; norm_cast))

中文:
引理 congruent_iff_dist_eq
  证明: congruent_iff_nndist_eq.trans
    (forall₂_congr (fun _ _ => by rw [dist_nndist, dist_nndist]; norm_cast))

Depends on / 依赖: congruent_iff_nndist_eq, congruent_iff_nndist_eq.trans, dist_nndist
-/
lemma congruent_iff_dist_eq :
    Congruent v₁ v₂ ↔ forall i₁ i₂, dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) :=
  congruent_iff_nndist_eq.trans
    (forall₂_congr (fun _ _ => by rw [dist_nndist, dist_nndist]; norm_cast))

/--
lemma `congruent_iff_pairwise_dist_eq` / 引理 `congruent_iff_pairwise_dist_eq`

English:
lemma congruent_iff_pairwise_dist_eq
  proof: by
  simp_rw [congruent_iff_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

中文:
引理 congruent_iff_pairwise_dist_eq
  证明: by
  simp_rw [congruent_iff_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

Depends on / 依赖: Iff.rfl, congruent_iff_pairwise_nndist_eq, dist_nndist, simp_rw
-/
lemma congruent_iff_pairwise_dist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ => dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) := by
  simp_rw [congruent_iff_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

namespace Congruent

/-- A congruence preserves non-negative distance. Forward direction of `congruent_iff_nndist_eq`. -/
alias ⟨nndist_eq, _⟩ := congruent_iff_nndist_eq

/-- Congruence follows from preserved non-negative distance. Backward direction of
`congruent_iff_nndist_eq`. -/
alias ⟨_, of_nndist_eq⟩ := congruent_iff_nndist_eq

/-- A congruence preserves distance. Forward direction of `congruent_iff_dist_eq`. -/
alias ⟨dist_eq, _⟩ := congruent_iff_dist_eq

/-- Congruence follows from preserved distance. Backward direction of `congruent_iff_dist_eq`. -/
alias ⟨_, of_dist_eq⟩ := congruent_iff_dist_eq

/-- A congruence pairwise preserves non-negative distance. Forward direction of
`congruent_iff_pairwise_nndist_eq`. -/
alias ⟨pairwise_nndist_eq, _⟩ := congruent_iff_pairwise_nndist_eq

/-- Congruence follows from pairwise preserved non-negative distance. Backward direction of
`congruent_iff_pairwise_nndist_eq`. -/
alias ⟨_, of_pairwise_nndist_eq⟩ := congruent_iff_pairwise_nndist_eq

/-- A congruence pairwise preserves distance. Forward direction of
`congruent_iff_pairwise_dist_eq`. -/
alias ⟨pairwise_dist_eq, _⟩ := congruent_iff_pairwise_dist_eq

/-- Congruence follows from pairwise preserved distance. Backward direction of
`congruent_iff_pairwise_dist_eq`. -/
alias ⟨_, of_pairwise_dist_eq⟩ := congruent_iff_pairwise_dist_eq

end Congruent

end PseudoMetricSpace
