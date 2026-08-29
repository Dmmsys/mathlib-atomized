/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Degenerate simplices

Given a simplicial set `X` and `n : ℕ`, we define the sets `X.degenerate n`
and `X.nonDegenerate n` of degenerate or non-degenerate simplices of dimension `n`.

Any simplex `x : X _⦋n⦌` can be written in a unique way as `X.map f.op y`
for an epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌` and a non-degenerate `m`-simplex `y`
(see lemmas `exists_nonDegenerate`, `unique_nonDegenerate_dim`,
`unique_nonDegenerate_simplex` and `unique_nonDegenerate_map`).

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

/--
Definition of `degenerate` / `degenerate` 的定义

English:
definition degenerate
  signature: (n : Nat)
  body: Set.ofPred (fun x => exists (m : Nat) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x in Set.range (X.map f.op))

中文:
定义 degenerate
  签名: (n : 自然数)
  定义体: Set.ofPred (fun x => exists (m : Nat) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x in Set.range (X.map f.op))

Depends on / 依赖: Set.ofPred, Set.range, X.map, f.op, ofPred
-/
def degenerate (n : Nat) : Set (X _⦋n⦌) :=
  Set.ofPred (fun x => exists (m : Nat) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x in Set.range (X.map f.op))

/--
Definition of `nonDegenerate` / `nonDegenerate` 的定义

English:
definition nonDegenerate
  signature: (n : Nat)
  body: (X.degenerate n)ᶜ

@[simp]

中文:
定义 nonDegenerate
  签名: (n : 自然数)
  定义体: (X.degenerate n)ᶜ

@[simp]

Depends on / 依赖: X.degenerate, degenerate
-/
def nonDegenerate (n : Nat) : Set (X _⦋n⦌) := (X.degenerate n)ᶜ

@[simp]
/--
lemma `degenerate_zero` / 引理 `degenerate_zero`

English:
lemma degenerate_zero
  statement: X.degenerate 0 = ∅
  proof: by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]

中文:
引理 degenerate_zero
  结论: X.degenerate 0 = ∅
  证明: by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]

Depends on / 依赖: Set.mem_empty_iff_false, iff_false, mem_empty_iff_false
-/
lemma degenerate_zero : X.degenerate 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
/--
lemma `nondegenerate_zero` / 引理 `nondegenerate_zero`

English:
lemma nondegenerate_zero
  statement: X.nonDegenerate 0 = Set.univ
  proof: by
  simp [nonDegenerate]

中文:
引理 nondegenerate_zero
  结论: X.nonDegenerate 0 = 集合.univ
  证明: by
  simp [nonDegenerate]

Depends on / 依赖: nonDegenerate
-/
lemma nondegenerate_zero : X.nonDegenerate 0 = Set.univ := by
  simp [nonDegenerate]

variable {n : Nat}

/--
lemma `mem_nonDegenerate_iff_notMem_degenerate` / 引理 `mem_nonDegenerate_iff_notMem_degenerate`

English:
lemma mem_nonDegenerate_iff_notMem_degenerate
  given: (x : X _⦋n⦌)
  proof: Iff.rfl

中文:
引理 mem_nonDegenerate_iff_notMem_degenerate
  条件: (x : X _⦋n⦌)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_nonDegenerate_iff_notMem_degenerate (x : X _⦋n⦌) :
    x in X.nonDegenerate n ↔ x ∉ X.degenerate n := Iff.rfl

/--
lemma `mem_degenerate_iff_notMem_nonDegenerate` / 引理 `mem_degenerate_iff_notMem_nonDegenerate`

English:
lemma mem_degenerate_iff_notMem_nonDegenerate
  given: (x : X _⦋n⦌)
  proof: by
  simp [nonDegenerate]

中文:
引理 mem_degenerate_iff_notMem_nonDegenerate
  条件: (x : X _⦋n⦌)
  证明: by
  simp [nonDegenerate]

Depends on / 依赖: nonDegenerate
-/
lemma mem_degenerate_iff_notMem_nonDegenerate (x : X _⦋n⦌) :
    x in X.degenerate n ↔ x ∉ X.nonDegenerate n := by
  simp [nonDegenerate]

/--
lemma `σ_mem_degenerate` / 引理 `σ_mem_degenerate`

English:
lemma σ_mem_degenerate
  given: (i : Fin (n + 1)) (x : X _⦋n⦌)
  proof: ⟨n, by lia, SimplexCategory.σ i, Set.mem_range_self x⟩

中文:
引理 σ_mem_degenerate
  条件: (i : 有限集 (n + 1)) (x : X _⦋n⦌)
  证明: ⟨n, by lia, SimplexCategory.σ i, Set.mem_range_self x⟩

Depends on / 依赖: Set.mem_range_self, SimplexCategory, mem_range_self
-/
lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _⦋n⦌) :
    X.σ i x in X.degenerate (n + 1) :=
  ⟨n, by lia, SimplexCategory.σ i, Set.mem_range_self x⟩

/--
lemma `mem_degenerate_iff` / 引理 `mem_degenerate_iff`

English:
lemma mem_degenerate_iff
  given: (x : X _⦋n⦌)
  proof: by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f]; rw [op_comp] at hy
    have : _ <= m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by lia, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

中文:
引理 mem_degenerate_iff
  条件: (x : X _⦋n⦌)
  证明: by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f]; rw [op_comp] at hy
    have : _ <= m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by lia, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

Depends on / 依赖: SimplexCategory, SimplexCategory.len_le_of_mono, factorThruImage, image.fac, len_le_of_mono, op_comp
-/
lemma mem_degenerate_iff (x : X _⦋n⦌) :
    x in X.degenerate n ↔ exists (m : Nat) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f),
        x in Set.range (X.map f.op) := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f]; rw [op_comp] at hy
    have : _ <= m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by lia, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `opObjEquiv_mem_degenerate_iff` / 引理 `opObjEquiv_mem_degenerate_iff`

English:
lemma opObjEquiv_mem_degenerate_iff
  given: (x : X.op _⦋n⦌)
  proof: by
  simp only [mem_degenerate_iff]
  refine exists_congr (fun m => exists_congr (fun _ => ?_))
  constructor
  · obtain ⟨x, rfl⟩ := opObjEquiv.symm.surjective x
    rintro ⟨f, _, y, rfl⟩
    exact ⟨SimplexCategory.rev.map f, inferInstance, opObjEquiv.symm y, by simp [op_map]⟩
  · rintro ⟨f, _, y, r

中文:
引理 opObjEquiv_mem_degenerate_iff
  条件: (x : X.op _⦋n⦌)
  证明: by
  simp only [mem_degenerate_iff]
  refine exists_congr (fun m => exists_congr (fun _ => ?_))
  constructor
  · obtain ⟨x, rfl⟩ := opObjEquiv.symm.surjective x
    rintro ⟨f, _, y, rfl⟩
    exact ⟨SimplexCategory.rev.map f, inferInstance, opObjEquiv.symm y, by simp [op_map]⟩
  · rintro ⟨f, _, y, r

Depends on / 依赖: SimplexCategory, SimplexCategory.rev.map, exists_congr, mem_degenerate_iff, opObjEquiv, opObjEquiv.symm, opObjEquiv.symm.surjective, op_map, surjective
-/
lemma opObjEquiv_mem_degenerate_iff (x : X.op _⦋n⦌) :
    opObjEquiv x in X.degenerate n ↔ x in X.op.degenerate n := by
  simp only [mem_degenerate_iff]
  refine exists_congr (fun m => exists_congr (fun _ => ?_))
  constructor
  · obtain ⟨x, rfl⟩ := opObjEquiv.symm.surjective x
    rintro ⟨f, _, y, rfl⟩
    exact ⟨SimplexCategory.rev.map f, inferInstance, opObjEquiv.symm y, by simp [op_map]⟩
  · rintro ⟨f, _, y, rfl⟩
    exact ⟨SimplexCategory.rev.map f, inferInstance, opObjEquiv y, by simp [op_map]⟩

/--
lemma `opObjEquiv_mem_nonDegenerate_iff` / 引理 `opObjEquiv_mem_nonDegenerate_iff`

English:
lemma opObjEquiv_mem_nonDegenerate_iff
  given: (x : X.op _⦋n⦌)
  proof: by
  simp only [mem_nonDegenerate_iff_notMem_degenerate,
    opObjEquiv_mem_degenerate_iff]

中文:
引理 opObjEquiv_mem_nonDegenerate_iff
  条件: (x : X.op _⦋n⦌)
  证明: by
  simp only [mem_nonDegenerate_iff_notMem_degenerate,
    opObjEquiv_mem_degenerate_iff]

Depends on / 依赖: mem_nonDegenerate_iff_notMem_degenerate, opObjEquiv_mem_degenerate_iff
-/
lemma opObjEquiv_mem_nonDegenerate_iff (x : X.op _⦋n⦌) :
    opObjEquiv x in X.nonDegenerate n ↔ x in X.op.nonDegenerate n := by
  simp only [mem_nonDegenerate_iff_notMem_degenerate,
    opObjEquiv_mem_degenerate_iff]

/--
lemma `degenerate_eq_iUnion_range_σ` / 引理 `degenerate_eq_iUnion_range_σ`

English:
lemma degenerate_eq_iUnion_range_σ
  proof: by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf => by
      rw [← SimplexCategory.mono_iff_injective] at hf
      have := SimplexCategory.le_of_mono f
      

中文:
引理 degenerate_eq_iUnion_range_σ
  证明: by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf => by
      rw [← SimplexCategory.mono_iff_injective] at hf
      have := SimplexCategory.le_of_mono f
      

Depends on / 依赖: Set.mem_iUnion, Set.mem_range, SimplexCategory, SimplexCategory.eq_, SimplexCategory.le_of_mono, SimplexCategory.mono_iff_injective, le_of_mono, mem_degenerate_iff, mem_iUnion, mem_range, mono_iff_injective
-/
lemma degenerate_eq_iUnion_range_σ :
    X.degenerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf => by
      rw [← SimplexCategory.mono_iff_injective] at hf
      have := SimplexCategory.le_of_mono f
      lia)
    aesop
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate

/--
lemma `exists_nonDegenerate` / 引理 `exists_nonDegenerate`

English:
lemma exists_nonDegenerate
  given: (x : X _⦋n⦌)
  proof: by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x in X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerat

中文:
引理 存在_nonDegenerate
  条件: (x : X _⦋n⦌)
  证明: by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x in X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerat

Depends on / 依赖: Set.mem_iUnion, Set.mem_range, SimplexCategory, X.nonDegenerate, mem_degenerate_iff_notMem_nonDegenerate, mem_iUnion, mem_range, nonDegenerate
-/
lemma exists_nonDegenerate (x : X _⦋n⦌) :
    exists (m : Nat) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y := by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x in X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩

/--
lemma `isIso_of_nonDegenerate` / 引理 `isIso_of_nonDegenerate`

English:
lemma isIso_of_nonDegenerate
  statement: (x : X.nonDegenerate n)
  proof: by
  obtain ⟨x, hx⟩ := x
  induction m using SimplexCategory.rec with | _ m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra hf
  refine hx ⟨_, not_le.1 (fun h => hf ?_), f, y, hy⟩
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm h (SimplexCategory.len_le_of_epi f)

中文:
引理 isIso_of_nonDegenerate
  结论: (x : X.nonDegenerate n)
  证明: by
  obtain ⟨x, hx⟩ := x
  induction m using SimplexCategory.rec with | _ m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra hf
  refine hx ⟨_, not_le.1 (fun h => hf ?_), f, y, hy⟩
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm h (SimplexCategory.len_le_of_epi f)

Depends on / 依赖: SimplexCategory, SimplexCategory.isIso_iff_of_epi, SimplexCategory.len_le_of_epi, SimplexCategory.rec, isIso_iff_of_epi, le_antisymm, len_le_of_epi, mem_nonDegenerate_iff_notMem_degenerate, not_le
-/
lemma isIso_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction m using SimplexCategory.rec with | _ m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra hf
  refine hx ⟨_, not_le.1 (fun h => hf ?_), f, y, hy⟩
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm h (SimplexCategory.len_le_of_epi f)

/--
lemma `mono_of_nonDegenerate` / 引理 `mono_of_nonDegenerate`

English:
lemma mono_of_nonDegenerate
  statement: (x : X.nonDegenerate n)
  proof: by
  have := X.isIso_of_nonDegenerate x (factorThruImage f) (y := X.map (image.ι f).op y) (by
      rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [image.fac f]; rw [hy])
  rw [← image.fac f]
  infer_instance

中文:
引理 mono_of_nonDegenerate
  结论: (x : X.nonDegenerate n)
  证明: by
  have := X.isIso_of_nonDegenerate x (factorThruImage f) (y := X.map (image.ι f).op y) (by
      rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [image.fac f]; rw [hy])
  rw [← image.fac f]
  infer_instance

Depends on / 依赖: Functor, Functor.map_comp, X.isIso_of_nonDegenerate, X.map, comp_apply, factorThruImage, image.fac, infer_instance, isIso_of_nonDegenerate, map_comp, op_comp
-/
lemma mono_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m)
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    Mono f := by
  have := X.isIso_of_nonDegenerate x (factorThruImage f) (y := X.map (image.ι f).op y) (by
      rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [image.fac f]; rw [hy])
  rw [← image.fac f]
  infer_instance

namespace unique_nonDegenerate

/-!
Auxiliary definitions and lemmas for the lemmas
`unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` and
`unique_nonDegenerate_map` which assert the uniqueness of the
decomposition obtained in the lemma `exists_nonDegenerate`.
-/

section

variable {X} {x : X _⦋n⦌}
  {m₁ m₂ : Nat} {f₁ : ⦋n⦌ ⟶ ⦋m₁⦌} (hf₁ : SplitEpi f₁)
  (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
  (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) (y₂ : X _⦋m₂⦌) (hy₂ : x = X.map f₂.op y₂)

/--
Definition of `g` / `g` 的定义

English:
definition g
  body: hf₁.section_ ≫ f₂

中文:
定义 g
  定义体: hf₁.section_ ≫ f₂
-/
private def g := hf₁.section_ ≫ f₂

variable {f₂ y₁ y₂}

include hf₁ hy₁ hy₂

/--
lemma `map_g_op_y₂` / 引理 `map_g_op_y₂`

English:
lemma map_g_op_y₂
  statement: X.map (g hf₁ f₂).op y₂ = y₁
  proof: by
  dsimp [g]
  rw [Functor.map_comp]; rw [comp_apply]; rw [← hy₂]; rw [hy₁]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [SplitEpi.id]; rw [op_id]; rw [CategoryTheory.Functor.map_id]; rw [id_apply]

中文:
引理 map_g_op_y₂
  结论: X.map (g hf₁ f₂).op y₂ = y₁
  证明: by
  dsimp [g]
  rw [Functor.map_comp]; rw [comp_apply]; rw [← hy₂]; rw [hy₁]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [SplitEpi.id]; rw [op_id]; rw [CategoryTheory.Functor.map_id]; rw [id_apply]
-/
private lemma map_g_op_y₂ : X.map (g hf₁ f₂).op y₂ = y₁ := by
  dsimp [g]
  rw [Functor.map_comp]; rw [comp_apply]; rw [← hy₂]; rw [hy₁]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [SplitEpi.id]; rw [op_id]; rw [CategoryTheory.Functor.map_id]; rw [id_apply]

/--
lemma `isIso_factorThruImage_g` / 引理 `isIso_factorThruImage_g`

English:
lemma isIso_factorThruImage_g
  proof: by
  have := map_g_op_y₂ hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply] at this
  exact X.isIso_of_nonDegenerate y₁ (factorThruImage (g hf₁ f₂)) _ this

中文:
引理 isIso_factorThruImage_g
  证明: by
  have := map_g_op_y₂ hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply] at this
  exact X.isIso_of_nonDegenerate y₁ (factorThruImage (g hf₁ f₂)) _ this
-/
private lemma isIso_factorThruImage_g :
    IsIso (factorThruImage (g hf₁ f₂)) := by
  have := map_g_op_y₂ hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply] at this
  exact X.isIso_of_nonDegenerate y₁ (factorThruImage (g hf₁ f₂)) _ this

/--
lemma `mono_g` / 引理 `mono_g`

English:
lemma mono_g
  statement: Mono (g hf₁ f₂)
  proof: by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]
  infer_instance

中文:
引理 mono_g
  结论: 单态射 (g hf₁ f₂)
  证明: by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]
  infer_instance
-/
private lemma mono_g : Mono (g hf₁ f₂) := by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]
  infer_instance

/--
lemma `le` / 引理 `le`

English:
lemma le
  statement: m₁ <= m₂
  proof: have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  SimplexCategory.len_le_of_mono
    (factorThruImage (g hf₁ f₂) ≫ image.ι _)

中文:
引理 le
  结论: m₁ <= m₂
  证明: have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  SimplexCategory.len_le_of_mono
    (factorThruImage (g hf₁ f₂) ≫ image.ι _)
-/
private lemma le : m₁ <= m₂ :=
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  SimplexCategory.len_le_of_mono
    (factorThruImage (g hf₁ f₂) ≫ image.ι _)

end

variable {X} in
/--
lemma `g_eq_id` / 引理 `g_eq_id`

English:
lemma g_eq_id
  statement: {x : X _⦋n⦌} {m : Nat} {f₁ : ⦋n⦌ ⟶ ⦋m⦌}
  proof: by
  have := mono_g hf₁ hy₁ hy₂
  apply SimplexCategory.eq_id_of_mono

中文:
引理 g_eq_id
  结论: {x : X _⦋n⦌} {m : 自然数} {f₁ : ⦋n⦌ ⟶ ⦋m⦌}
  证明: by
  have := mono_g hf₁ hy₁ hy₂
  apply SimplexCategory.eq_id_of_mono

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, PathConnectedSpace, RCLike, infer_instance, rclike
-/
private lemma g_eq_id {x : X _⦋n⦌} {m : Nat} {f₁ : ⦋n⦌ ⟶ ⦋m⦌}
    {y₁ : X.nonDegenerate m} (hy₁ : x = X.map f₁.op y₁)
    {f₂ : ⦋n⦌ ⟶ ⦋m⦌} {y₂ : X _⦋m⦌} (hy₂ : x = X.map f₂.op y₂) (hf₁ : SplitEpi f₁) :
    g hf₁ f₂ = 𝟙 _ := by
  have := mono_g hf₁ hy₁ hy₂
  apply SimplexCategory.eq_id_of_mono

end unique_nonDegenerate

section

open unique_nonDegenerate


/--
lemma `unique_nonDegenerate_dim` / 引理 `unique_nonDegenerate_dim`

English:
lemma unique_nonDegenerate_dim
  statement: (x : X _⦋n⦌) {m₁ m₂ : Nat}
  proof: by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  obtain ⟨⟨hf₂⟩⟩ := isSplitEpi_of_epi f₂
  exact le_antisymm (le hf₁ hy₁ hy₂) (le hf₂ hy₂ hy₁)

中文:
引理 unique_nonDegenerate_dim
  结论: (x : X _⦋n⦌) {m₁ m₂ : 自然数}
  证明: by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  obtain ⟨⟨hf₂⟩⟩ := isSplitEpi_of_epi f₂
  exact le_antisymm (le hf₁ hy₁ hy₂) (le hf₂ hy₂ hy₁)

Depends on / 依赖: isSplitEpi_of_epi, le_antisymm
-/
lemma unique_nonDegenerate_dim (x : X _⦋n⦌) {m₁ m₂ : Nat}
    (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi f₁] (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi f₂] (y₂ : X.nonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) :
    m₁ = m₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  obtain ⟨⟨hf₂⟩⟩ := isSplitEpi_of_epi f₂
  exact le_antisymm (le hf₁ hy₁ hy₂) (le hf₂ hy₂ hy₁)

/--
lemma `unique_nonDegenerate_simplex` / 引理 `unique_nonDegenerate_simplex`

English:
lemma unique_nonDegenerate_simplex
  statement: (x : X _⦋n⦌) {m : Nat}
  proof: by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  ext
  simpa [g_eq_id hy₁ hy₂ hf₁] using (map_g_op_y₂ hf₁ hy₁ hy₂).symm

中文:
引理 unique_nonDegenerate_simplex
  结论: (x : X _⦋n⦌) {m : 自然数}
  证明: by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  ext
  simpa [g_eq_id hy₁ hy₂ hf₁] using (map_g_op_y₂ hf₁ hy₁ hy₂).symm

Depends on / 依赖: g_eq_id, isSplitEpi_of_epi
-/
lemma unique_nonDegenerate_simplex (x : X _⦋n⦌) {m : Nat}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    y₁ = y₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  ext
  simpa [g_eq_id hy₁ hy₂ hf₁] using (map_g_op_y₂ hf₁ hy₁ hy₂).symm

/--
lemma `unique_nonDegenerate_map` / 引理 `unique_nonDegenerate_map`

English:
lemma unique_nonDegenerate_map
  statement: (x : X _⦋n⦌) {m : Nat}
  proof: by
  ext x : 3
  suffices exists (hf₁ : SplitEpi f₁), hf₁.section_.toOrderHom (f₁.toOrderHom x) = x by
    obtain ⟨hf₁, hf₁'⟩ := this
    dsimp at hf₁'
    simpa [g, hf₁'] using (SimplexCategory.congr_toOrderHom_apply (g_eq_id hy₁ hy₂ hf₁)
      (f₁.toOrderHom x)).symm
  obtain ⟨⟨hf⟩⟩ := isSplitEpi_

中文:
引理 unique_nonDegenerate_map
  结论: (x : X _⦋n⦌) {m : 自然数}
  证明: by
  ext x : 3
  suffices exists (hf₁ : SplitEpi f₁), hf₁.section_.toOrderHom (f₁.toOrderHom x) = x by
    obtain ⟨hf₁, hf₁'⟩ := this
    dsimp at hf₁'
    simpa [g, hf₁'] using (SimplexCategory.congr_toOrderHom_apply (g_eq_id hy₁ hy₂ hf₁)
      (f₁.toOrderHom x)).symm
  obtain ⟨⟨hf⟩⟩ := isSplitEpi_

Depends on / 依赖: SimplexC, SimplexCategory, SimplexCategory.congr_toOrderHom_apply, SplitEpi, congr_toOrderHom_apply, g_eq_id, hf.section_.toOrderHom, isSplitEpi_of_epi, section_, section_.toOrderHom, split_ifs, toOrderHom
-/
lemma unique_nonDegenerate_map (x : X _⦋n⦌) {m : Nat}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    f₁ = f₂ := by
  ext x : 3
  suffices exists (hf₁ : SplitEpi f₁), hf₁.section_.toOrderHom (f₁.toOrderHom x) = x by
    obtain ⟨hf₁, hf₁'⟩ := this
    dsimp at hf₁'
    simpa [g, hf₁'] using (SimplexCategory.congr_toOrderHom_apply (g_eq_id hy₁ hy₂ hf₁)
      (f₁.toOrderHom x)).symm
  obtain ⟨⟨hf⟩⟩ := isSplitEpi_of_epi f₁
  let α (y : Fin (m + 1)) : Fin (n + 1) :=
    if y = f₁.toOrderHom x then x else hf.section_.toOrderHom y
  have hα₁ (y : Fin (m + 1)) : f₁.toOrderHom (α y) = y := by
    dsimp [α]
    split_ifs with hy
    · rw [hy]
    · apply SimplexCategory.congr_toOrderHom_apply hf.id
  have hα₂ : Monotone α := by
    rintro y₁ y₂ h
    by_contra! h'
    suffices y₂ <= y₁ by simp [show y₁ = y₂ by lia] at h'
    simpa only [hα₁] using f₁.toOrderHom.monotone h'.le
  exact ⟨{ section_ := SimplexCategory.Hom.mk ⟨α, hα₂⟩, id := by ext : 3; apply hα₁ },
    by simp [α]⟩

end

namespace Subcomplex

variable {X} (A : X.Subcomplex)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_degenerate_iff` / 引理 `mem_degenerate_iff`

English:
lemma mem_degenerate_iff
  given: {n : Nat} (x : A.obj (op ⦋n⦌))
  proof: by
  rw [SSet.mem_degenerate_iff]; rw [SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, _, y, rfl⟩
    exact ⟨m, hm, f, inferInstance, y.val, rfl⟩
  · obtain ⟨x, hx⟩ := x
    rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    refine ⟨m, hm, f, inferInstance, ⟨y, ?_⟩, rfl⟩
    have := isSplitEpi_of_epi f

中文:
引理 mem_degenerate_iff
  条件: {n : 自然数} (x : A.obj (op ⦋n⦌))
  证明: by
  rw [SSet.mem_degenerate_iff]; rw [SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, _, y, rfl⟩
    exact ⟨m, hm, f, inferInstance, y.val, rfl⟩
  · obtain ⟨x, hx⟩ := x
    rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    refine ⟨m, hm, f, inferInstance, ⟨y, ?_⟩, rfl⟩
    have := isSplitEpi_of_epi f

Depends on / 依赖: A.map, Functor, Functor.map_comp, SSet.mem_degenerate_iff, Set.mem_preimage, comp_apply, isSplitEpi_of_epi, map_comp, mem_degenerate_iff, mem_preimage, op_comp, section_, y.val
-/
lemma mem_degenerate_iff {n : Nat} (x : A.obj (op ⦋n⦌)) :
    dsimp% x in degenerate A n ↔ x.val in X.degenerate n := by
  rw [SSet.mem_degenerate_iff]; rw [SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, _, y, rfl⟩
    exact ⟨m, hm, f, inferInstance, y.val, rfl⟩
  · obtain ⟨x, hx⟩ := x
    rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    refine ⟨m, hm, f, inferInstance, ⟨y, ?_⟩, rfl⟩
    have := isSplitEpi_of_epi f
    simpa [Set.mem_preimage, ← op_comp, ← comp_apply, ← Functor.map_comp] using
      A.map (section_ f).op hx

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_nonDegenerate_iff` / 引理 `mem_nonDegenerate_iff`

English:
lemma mem_nonDegenerate_iff
  given: {n : Nat} (x : A.obj (op ⦋n⦌))
  proof: by
  rw [mem_nonDegenerate_iff_notMem_degenerate]; rw [mem_nonDegenerate_iff_notMem_degenerate]; rw [mem_degenerate_iff]

中文:
引理 mem_nonDegenerate_iff
  条件: {n : 自然数} (x : A.obj (op ⦋n⦌))
  证明: by
  rw [mem_nonDegenerate_iff_notMem_degenerate]; rw [mem_nonDegenerate_iff_notMem_degenerate]; rw [mem_degenerate_iff]

Depends on / 依赖: mem_degenerate_iff, mem_nonDegenerate_iff_notMem_degenerate
-/
lemma mem_nonDegenerate_iff {n : Nat} (x : A.obj (op ⦋n⦌)) :
    dsimp% x in nonDegenerate A n ↔ x.val in X.nonDegenerate n := by
  rw [mem_nonDegenerate_iff_notMem_degenerate]; rw [mem_nonDegenerate_iff_notMem_degenerate]; rw [mem_degenerate_iff]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `le_iff_contains_nonDegenerate` / 引理 `le_iff_contains_nonDegenerate`

English:
lemma le_iff_contains_nonDegenerate
  given: (B : X.Subcomplex)
  proof: by
  constructor
  · aesop
  · rintro h ⟨n⟩ x hx
    induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, f, _, ⟨a, ha⟩, ha'⟩ := exists_nonDegenerate A ⟨x, hx⟩
    simp only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
      Subfunctor.toFunctor_map] at ha'
    subst ha'
    rw [mem_non

中文:
引理 le_iff_contains_nonDegenerate
  条件: (B : X.子复形)
  证明: by
  constructor
  · aesop
  · rintro h ⟨n⟩ x hx
    induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, f, _, ⟨a, ha⟩, ha'⟩ := exists_nonDegenerate A ⟨x, hx⟩
    simp only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
      Subfunctor.toFunctor_map] at ha'
    subst ha'
    rw [mem_non

Depends on / 依赖: B.map, SimplexCategory, SimplexCategory.rec, Subfunctor, Subfunctor.toFunctor_map, Subfunctor.toFunctor_obj, Subtype, Subtype.ext_iff, a.prop, exists_nonDegenerate, ext_iff, f.op, mem_nonDegenerate_iff, toFunctor_map, toFunctor_obj
-/
lemma le_iff_contains_nonDegenerate (B : X.Subcomplex) :
    A <= B ↔ forall (n : Nat) (x : X.nonDegenerate n), x.val in A.obj _ -> x.val in B.obj _ := by
  constructor
  · aesop
  · rintro h ⟨n⟩ x hx
    induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, f, _, ⟨a, ha⟩, ha'⟩ := exists_nonDegenerate A ⟨x, hx⟩
    simp only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
      Subfunctor.toFunctor_map] at ha'
    subst ha'
    rw [mem_nonDegenerate_iff] at ha
    exact B.map f.op (h _ ⟨_, ha⟩ a.prop)

/--
lemma `eq_top_iff_contains_nonDegenerate` / 引理 `eq_top_iff_contains_nonDegenerate`

English:
lemma eq_top_iff_contains_nonDegenerate
  proof: by
  simpa using! le_iff_contains_nonDegenerate ⊤ A

中文:
引理 eq_top_iff_contains_nonDegenerate
  证明: by
  simpa using! le_iff_contains_nonDegenerate ⊤ A

Depends on / 依赖: le_iff_contains_nonDegenerate
-/
lemma eq_top_iff_contains_nonDegenerate :
    A = ⊤ ↔ forall (n : Nat), X.nonDegenerate n subseteq A.obj _ := by
  simpa using! le_iff_contains_nonDegenerate ⊤ A

set_option backward.isDefEq.respectTransparency false in
/--
lemma `degenerate_eq_top_iff` / 引理 `degenerate_eq_top_iff`

English:
lemma degenerate_eq_top_iff
  given: (n : Nat)
  proof: by
  constructor
  · intro h
    ext x
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    simp [← A.mem_degenerate_iff ⟨x, hx⟩, h, Set.top_eq_univ, Set.mem_univ]
  · intro h
    simp only [Set.inf_eq_inter, Set.inter_eq_right] at h
    ext x
    simpa [A.mem_

中文:
引理 degenerate_eq_top_iff
  条件: (n : 自然数)
  证明: by
  constructor
  · intro h
    ext x
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    simp [← A.mem_degenerate_iff ⟨x, hx⟩, h, Set.top_eq_univ, Set.mem_univ]
  · intro h
    simp only [Set.inf_eq_inter, Set.inter_eq_right] at h
    ext x
    simpa [A.mem_

Depends on / 依赖: A.mem_degenerate_iff, Set.inf_eq_inter, Set.inter_eq_right, Set.mem_inter_iff, Set.mem_univ, Set.top_eq_univ, and_iff_right_iff_imp, inf_eq_inter, inter_eq_right, mem_degenerate_iff, mem_inter_iff, mem_univ, top_eq_univ, x.prop
-/
lemma degenerate_eq_top_iff (n : Nat) :
    degenerate A n = ⊤ ↔ (X.degenerate n ⊓ A.obj _) = A.obj _ := by
  constructor
  · intro h
    ext x
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    simp [← A.mem_degenerate_iff ⟨x, hx⟩, h, Set.top_eq_univ, Set.mem_univ]
  · intro h
    simp only [Set.inf_eq_inter, Set.inter_eq_right] at h
    ext x
    simpa [A.mem_degenerate_iff] using h x.prop

variable (X) in
/--
lemma `iSup_ofSimplex_nonDegenerate_eq_top` / 引理 `iSup_ofSimplex_nonDegenerate_eq_top`

English:
lemma iSup_ofSimplex_nonDegenerate_eq_top
  proof: by
  rw [eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop]
  exact ⟨n, x, hx, mem_ofSimplex_obj x⟩

中文:
引理 iSup_ofSimplex_nonDegenerate_eq_top
  证明: by
  rw [eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop]
  exact ⟨n, x, hx, mem_ofSimplex_obj x⟩

Depends on / 依赖: Set.mem_iUnion, Sigma.exists, Subfunctor, Subfunctor.iSup_obj, Subtype, Subtype.exists, eq_top_iff_contains_nonDegenerate, exists_prop, iSup_obj, mem_iUnion, mem_ofSimplex_obj
-/
lemma iSup_ofSimplex_nonDegenerate_eq_top :
    ⨆ (x : Σ (p : Nat), X.nonDegenerate p), ofSimplex x.2.val = ⊤ := by
  rw [eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop]
  exact ⟨n, x, hx, mem_ofSimplex_obj x⟩

end Subcomplex

section

variable {X} {Y : SSet.{u}}

/--
lemma `degenerate_app_apply` / 引理 `degenerate_app_apply`

English:
lemma degenerate_app_apply
  given: {n : Nat} {x : X _⦋n⦌} (hx : x in X.degenerate n) (f : X ⟶ Y)
  proof: by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, g, f.app _ y, by rw [NatTrans.naturality_apply]⟩

中文:
引理 degenerate_app_apply
  条件: {n : 自然数} {x : X _⦋n⦌} (hx : x in X.degenerate n) (f : X ⟶ Y)
  证明: by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, g, f.app _ y, by rw [NatTrans.naturality_apply]⟩

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, f.app, naturality_apply
-/
lemma degenerate_app_apply {n : Nat} {x : X _⦋n⦌} (hx : x in X.degenerate n) (f : X ⟶ Y) :
    f.app _ x in Y.degenerate n := by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, g, f.app _ y, by rw [NatTrans.naturality_apply]⟩

/--
lemma `degenerate_le_preimage` / 引理 `degenerate_le_preimage`

English:
lemma degenerate_le_preimage
  given: (f : X ⟶ Y) (n : Nat)
  proof: fun _ hx => degenerate_app_apply hx f

中文:
引理 degenerate_le_preimage
  条件: (f : X ⟶ Y) (n : 自然数)
  证明: fun _ hx => degenerate_app_apply hx f

Depends on / 依赖: degenerate_app_apply
-/
lemma degenerate_le_preimage (f : X ⟶ Y) (n : Nat) :
    X.degenerate n subseteq (f.app _) ⁻¹' (Y.degenerate n) :=
  fun _ hx => degenerate_app_apply hx f

/--
lemma `image_degenerate_le` / 引理 `image_degenerate_le`

English:
lemma image_degenerate_le
  given: (f : X ⟶ Y) (n : Nat)
  proof: by
  simpa using degenerate_le_preimage f n

中文:
引理 image_degenerate_le
  条件: (f : X ⟶ Y) (n : 自然数)
  证明: by
  simpa using degenerate_le_preimage f n

Depends on / 依赖: degenerate_le_preimage
-/
lemma image_degenerate_le (f : X ⟶ Y) (n : Nat) :
    (f.app _) '' (X.degenerate n) subseteq Y.degenerate n := by
  simpa using degenerate_le_preimage f n

/--
lemma `degenerate_iff_of_isIso` / 引理 `degenerate_iff_of_isIso`

English:
lemma degenerate_iff_of_isIso
  given: (f : X ⟶ Y) [IsIso f] {n : Nat} (x : X _⦋n⦌)
  proof: by
  constructor
  · intro hy
    simpa [← comp_apply, ← NatTrans.comp_app] using degenerate_app_apply hy (inv f)
  · exact fun hx => degenerate_app_apply hx f

中文:
引理 degenerate_iff_of_isIso
  条件: (f : X ⟶ Y) [是同构 f] {n : 自然数} (x : X _⦋n⦌)
  证明: by
  constructor
  · intro hy
    simpa [← comp_apply, ← NatTrans.comp_app] using degenerate_app_apply hy (inv f)
  · exact fun hx => degenerate_app_apply hx f

Depends on / 依赖: NatTrans, NatTrans.comp_app, comp_app, comp_apply, degenerate_app_apply
-/
lemma degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : Nat} (x : X _⦋n⦌) :
    f.app _ x in Y.degenerate n ↔ x in X.degenerate n := by
  constructor
  · intro hy
    simpa [← comp_apply, ← NatTrans.comp_app] using degenerate_app_apply hy (inv f)
  · exact fun hx => degenerate_app_apply hx f

/--
lemma `nonDegenerate_iff_of_isIso` / 引理 `nonDegenerate_iff_of_isIso`

English:
lemma nonDegenerate_iff_of_isIso
  given: (f : X ⟶ Y) [IsIso f] {n : Nat} (x : X _⦋n⦌)
  proof: by
  simp [mem_nonDegenerate_iff_notMem_degenerate,
    degenerate_iff_of_isIso]

中文:
引理 nonDegenerate_iff_of_isIso
  条件: (f : X ⟶ Y) [是同构 f] {n : 自然数} (x : X _⦋n⦌)
  证明: by
  simp [mem_nonDegenerate_iff_notMem_degenerate,
    degenerate_iff_of_isIso]

Depends on / 依赖: degenerate_iff_of_isIso, mem_nonDegenerate_iff_notMem_degenerate
-/
lemma nonDegenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : Nat} (x : X _⦋n⦌) :
    f.app _ x in Y.nonDegenerate n ↔ x in X.nonDegenerate n := by
  simp [mem_nonDegenerate_iff_notMem_degenerate,
    degenerate_iff_of_isIso]

attribute [local simp] nonDegenerate_iff_of_isIso in
/-- The bijection on nondegenerate simplices induced by an isomorphism
of simplicial sets. -/
@[simps]
/--
Definition of `nonDegenerateEquivOfIso` / `nonDegenerateEquivOfIso` 的定义

English:
definition nonDegenerateEquivOfIso
  signature: (e : X ≅ Y) {n : Nat}
  body: fun ⟨x, hx⟩ => ⟨e.hom.app _ x, by aesop⟩
  invFun := fun ⟨y, hy⟩ => ⟨e.inv.app _ y, by aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

中文:
定义 nonDegenerateEquivOfIso
  签名: (e : X ≅ Y) {n : 自然数}
  定义体: fun ⟨x, hx⟩ => ⟨e.hom.app _ x, by aesop⟩
  invFun := fun ⟨y, hy⟩ => ⟨e.inv.app _ y, by aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

Depends on / 依赖: e.hom.app
-/
def nonDegenerateEquivOfIso (e : X ≅ Y) {n : Nat} :
    X.nonDegenerate n ≃ Y.nonDegenerate n where
  toFun := fun ⟨x, hx⟩ => ⟨e.hom.app _ x, by aesop⟩
  invFun := fun ⟨y, hy⟩ => ⟨e.inv.app _ y, by aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

end

set_option backward.isDefEq.respectTransparency false in
variable {X} in
/--
lemma `degenerate_iff_of_mono` / 引理 `degenerate_iff_of_mono`

English:
lemma degenerate_iff_of_mono
  given: {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌)
  proof: by
  rw [← degenerate_iff_of_isIso (Subcomplex.toRange f) x]; rw [Subcomplex.mem_degenerate_iff]
  simp

中文:
引理 degenerate_iff_of_mono
  条件: {Y : SSet.{u}} (f : X ⟶ Y) [单态射 f] (x : X _⦋n⦌)
  证明: by
  rw [← degenerate_iff_of_isIso (Subcomplex.toRange f) x]; rw [Subcomplex.mem_degenerate_iff]
  simp

Depends on / 依赖: Subcomplex, Subcomplex.mem_degenerate_iff, Subcomplex.toRange, degenerate_iff_of_isIso, mem_degenerate_iff, toRange
-/
lemma degenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x in Y.degenerate n ↔ x in X.degenerate n := by
  rw [← degenerate_iff_of_isIso (Subcomplex.toRange f) x]; rw [Subcomplex.mem_degenerate_iff]
  simp

variable {X} in
/--
lemma `nonDegenerate_iff_of_mono` / 引理 `nonDegenerate_iff_of_mono`

English:
lemma nonDegenerate_iff_of_mono
  given: {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌)
  proof: by
  simp [mem_nonDegenerate_iff_notMem_degenerate, degenerate_iff_of_mono]

中文:
引理 nonDegenerate_iff_of_mono
  条件: {Y : SSet.{u}} (f : X ⟶ Y) [单态射 f] (x : X _⦋n⦌)
  证明: by
  simp [mem_nonDegenerate_iff_notMem_degenerate, degenerate_iff_of_mono]

Depends on / 依赖: degenerate_iff_of_mono, mem_nonDegenerate_iff_notMem_degenerate
-/
lemma nonDegenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x in Y.nonDegenerate n ↔ x in X.nonDegenerate n := by
  simp [mem_nonDegenerate_iff_notMem_degenerate, degenerate_iff_of_mono]

end SSet
