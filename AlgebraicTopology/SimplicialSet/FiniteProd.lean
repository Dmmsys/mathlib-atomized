/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# A binary product of finite simplicial sets is finite

If `X₁` and `X₂` are respectively of dimensions `≤ d₁` and `≤ d₂`,
then `X₁ ⊗ X₂` has dimension `≤ d₁ + d₂`.

We also show that if `X₁` and `X₂` are finite, then `X₁ ⊗ X₂` is also finite.

-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Simplicial Opposite

namespace SSet

variable {X₁ X₂ X₃ X₄ : SSet.{u}}

set_option backward.isDefEq.respectTransparency.types false in
variable (X₁ X₂) in
/--
lemma `iSup_subcomplexOfSimplex_prod_eq_top` / 引理 `iSup_subcomplexOfSimplex_prod_eq_top`

English:
lemma iSup_subcomplexOfSimplex_prod_eq_top
  proof: by
  ext m ⟨x₁, x₂⟩
  simp only [Subfunctor.iSup_obj, Subcomplex.prod_obj, Set.mem_iUnion, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  have hx₁ : x₁ in (⊤ : X₁.Subcomplex).obj _ := by simp
  have hx₂ : x₂ in (⊤ : X₂.Subcomplex).obj _ := by simp
  simp only [← N.iSup_subcomplex_eq_top, Subfunctor.iSup_obj, Set.mem_iUnion] at hx₁ hx₂
  obtain ⟨s₁, hs₁⟩ := hx₁
  obtain ⟨s₂, hs₂⟩ := hx₂
  exact ⟨s₁, s₂, hs₁, hs₂⟩

中文:
引理 iSup_subcomplexOfSimplex_prod_eq_top
  证明: by
  ext m ⟨x₁, x₂⟩
  simp only [Subfunctor.iSup_obj, Subcomplex.prod_obj, Set.mem_iUnion, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  have hx₁ : x₁ in (⊤ : X₁.Subcomplex).obj _ := by simp
  have hx₂ : x₂ in (⊤ : X₂.Subcomplex).obj _ := by simp
  simp only [← N.iSup_subcomplex_eq_top, Subfunctor.iSup_obj, Set.mem_iUnion] at hx₁ hx₂
  obtain ⟨s₁, hs₁⟩ := hx₁
  obtain ⟨s₂, hs₂⟩ := hx₂
  exact ⟨s₁, s₂, hs₁, hs₂⟩

Depends on / 依赖: N.iSup_subcomplex_eq_top, Set.mem_iUnion, Set.mem_univ, Set.top_eq_univ, Subcomplex, Subcomplex.prod_obj, Subfunctor, Subfunctor.iSup_obj, Subfunctor.top_obj, iSup_obj, iSup_subcomplex_eq_top, iff_true, mem_iUnion, mem_univ, prod_obj, top_eq_univ, top_obj
-/
lemma iSup_subcomplexOfSimplex_prod_eq_top :
    ⨆ (x₁ : X₁.N) (x₂ : X₂.N),
      (Subcomplex.ofSimplex x₁.simplex).prod (Subcomplex.ofSimplex x₂.simplex) = ⊤ := by
  ext m ⟨x₁, x₂⟩
  simp only [Subfunctor.iSup_obj, Subcomplex.prod_obj, Set.mem_iUnion, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  have hx₁ : x₁ in (⊤ : X₁.Subcomplex).obj _ := by simp
  have hx₂ : x₂ in (⊤ : X₂.Subcomplex).obj _ := by simp
  simp only [← N.iSup_subcomplex_eq_top, Subfunctor.iSup_obj, Set.mem_iUnion] at hx₁ hx₂
  obtain ⟨s₁, hs₁⟩ := hx₁
  obtain ⟨s₂, hs₂⟩ := hx₂
  exact ⟨s₁, s₂, hs₁, hs₂⟩

/--
lemma `Subcomplex.ofSimplexProd_eq_range` / 引理 `Subcomplex.ofSimplexProd_eq_range`

English:
lemma Subcomplex.ofSimplexProd_eq_range
  given: {p q : Nat} (x₁ : X₁ _⦋p⦌) (x₂ : X₂ _⦋q⦌)
  proof: by
  simp [Subcomplex.range_tensorHom, Subcomplex.range_eq_ofSimplex]

中文:
引理 子复形.ofSimplexProd_eq_range
  条件: {p q : 自然数} (x₁ : X₁ _⦋p⦌) (x₂ : X₂ _⦋q⦌)
  证明: by
  simp [Subcomplex.range_tensorHom, Subcomplex.range_eq_ofSimplex]

Depends on / 依赖: Subcomplex, Subcomplex.range_eq_ofSimplex, Subcomplex.range_tensorHom, range_eq_ofSimplex, range_tensorHom
-/
lemma Subcomplex.ofSimplexProd_eq_range {p q : Nat} (x₁ : X₁ _⦋p⦌) (x₂ : X₂ _⦋q⦌) :
    (Subcomplex.ofSimplex x₁).prod (Subcomplex.ofSimplex x₂) =
      Subcomplex.range (yonedaEquiv.symm x₁ otimesₘ yonedaEquiv.symm x₂) := by
  simp [Subcomplex.range_tensorHom, Subcomplex.range_eq_ofSimplex]

variable (X₁ X₂) in
/--
lemma `hasDimensionLT_prod` / 引理 `hasDimensionLT_prod`

English:
lemma hasDimensionLT_prod
  proof: by
  rw [← hasDimensionLT_subcomplex_top_iff]; rw [← iSup_subcomplexOfSimplex_prod_eq_top]
  simp only [Subcomplex.ofSimplexProd_eq_range, hasDimensionLT_iSup_iff]
  intro x₁ x₂
  have := X₁.dim_lt_of_nonDegenerate ⟨_, x₁.nonDegenerate⟩ d₁
  have := X₂.dim_lt_of_nonDegenerate ⟨_, x₂.nonDegenerate⟩ d₂
  have := (Δ[x₁.dim] otimes Δ[x₂.dim]).hasDimensionLT_of_le (x₁.dim + x₂.dim + 1) n
  infer_instance

中文:
引理 hasDimensionLT_prod
  证明: by
  rw [← hasDimensionLT_subcomplex_top_iff]; rw [← iSup_subcomplexOfSimplex_prod_eq_top]
  simp only [Subcomplex.ofSimplexProd_eq_range, hasDimensionLT_iSup_iff]
  intro x₁ x₂
  have := X₁.dim_lt_of_nonDegenerate ⟨_, x₁.nonDegenerate⟩ d₁
  have := X₂.dim_lt_of_nonDegenerate ⟨_, x₂.nonDegenerate⟩ d₂
  have := (Δ[x₁.dim] otimes Δ[x₂.dim]).hasDimensionLT_of_le (x₁.dim + x₂.dim + 1) n
  infer_instance

Depends on / 依赖: HasDimensionLT, Subcomplex, Subcomplex.ofSimplexProd_eq_range, dim_lt_of_nonDegenerate, hasDimensionLT_iSup_iff, hasDimensionLT_of_le, hasDimensionLT_subcomplex_top_iff, iSup_subcomplexOfSimplex_prod_eq_top, infer_instance, nonDegenerate, ofSimplexProd_eq_range, otimes
-/
lemma hasDimensionLT_prod
    (d₁ d₂ : Nat) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂]
    (n : Nat) (hn : d₁ + d₂ <= n + 1 := by lia) :
    (X₁ otimes X₂).HasDimensionLT n := by
  rw [← hasDimensionLT_subcomplex_top_iff]; rw [← iSup_subcomplexOfSimplex_prod_eq_top]
  simp only [Subcomplex.ofSimplexProd_eq_range, hasDimensionLT_iSup_iff]
  intro x₁ x₂
  have := X₁.dim_lt_of_nonDegenerate ⟨_, x₁.nonDegenerate⟩ d₁
  have := X₂.dim_lt_of_nonDegenerate ⟨_, x₂.nonDegenerate⟩ d₂
  have := (Δ[x₁.dim] otimes Δ[x₂.dim]).hasDimensionLT_of_le (x₁.dim + x₂.dim + 1) n
  infer_instance

variable (X₁ X₂) in
/--
lemma `hasDimensionLE_prod` / 引理 `hasDimensionLE_prod`

English:
lemma hasDimensionLE_prod
  proof: hasDimensionLT_prod X₁ X₂ (d₁ + 1) (d₂ + 1) (n + 1)

中文:
引理 hasDimensionLE_prod
  证明: hasDimensionLT_prod X₁ X₂ (d₁ + 1) (d₂ + 1) (n + 1)

Depends on / 依赖: HasDimensionLE, hasDimensionLT_prod, otimes
-/
lemma hasDimensionLE_prod
    (d₁ d₂ : Nat) [X₁.HasDimensionLE d₁] [X₂.HasDimensionLE d₂]
    (n : Nat) (hn : d₁ + d₂ <= n := by lia) :
    (X₁ otimes X₂).HasDimensionLE n :=
  hasDimensionLT_prod X₁ X₂ (d₁ + 1) (d₂ + 1) (n + 1)

instance (d₁ d₂ : Nat) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂] :
    (X₁ otimes X₂).HasDimensionLT (d₁ + d₂) :=
  hasDimensionLT_prod _ _ d₁ d₂ (d₁ + d₂)

instance (d₁ d₂ : Nat) [X₁.HasDimensionLE d₁] [X₂.HasDimensionLE d₂] :
    (X₁ otimes X₂).HasDimensionLE (d₁ + d₂) :=
  hasDimensionLE_prod _ _ d₁ d₂ (d₁ + d₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X₁.Finite]
  signature: [X₂.Finite]
  body: by
  obtain ⟨d₁, _⟩ := X₁.hasDimensionLT_of_finite
  obtain ⟨d₂, _⟩ := X₂.hasDimensionLT_of_finite
  exact finite_of_hasDimensionLT _ (d₁ + d₂) (fun _ _ => inferInstance)

中文:
实例 [X₁.有限]
  签名: [X₂.有限]
  定义体: by
  obtain ⟨d₁, _⟩ := X₁.hasDimensionLT_of_finite
  obtain ⟨d₂, _⟩ := X₂.hasDimensionLT_of_finite
  exact finite_of_hasDimensionLT _ (d₁ + d₂) (fun _ _ => inferInstance)

Depends on / 依赖: finite_of_hasDimensionLT, hasDimensionLT_of_finite
-/
instance [X₁.Finite] [X₂.Finite] : (X₁ otimes X₂).Finite := by
  obtain ⟨d₁, _⟩ := X₁.hasDimensionLT_of_finite
  obtain ⟨d₂, _⟩ := X₂.hasDimensionLT_of_finite
  exact finite_of_hasDimensionLT _ (d₁ + d₂) (fun _ _ => inferInstance)

open CartesianMonoidalCategory in
/--
lemma `finite_of_isPullback` / 引理 `finite_of_isPullback`

English:
lemma finite_of_isPullback
  statement: {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
  proof: have : Mono (lift t l) :=
    ⟨fun _ _ h => sq.hom_ext (by simpa using h =≫ fst _ _) (by simpa using h =≫ snd _ _)⟩
  finite_of_mono (lift t l)

中文:
引理 finite_of_isPullback
  结论: {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
  证明: have : Mono (lift t l) :=
    ⟨fun _ _ h => sq.hom_ext (by simpa using h =≫ fst _ _) (by simpa using h =≫ snd _ _)⟩
  finite_of_mono (lift t l)

Depends on / 依赖: finite_of_mono, hom_ext, sq.hom_ext
-/
lemma finite_of_isPullback {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPullback t l r b) [X₂.Finite] [X₃.Finite] : X₁.Finite :=
  have : Mono (lift t l) :=
    ⟨fun _ _ h => sq.hom_ext (by simpa using h =≫ fst _ _) (by simpa using h =≫ snd _ _)⟩
  finite_of_mono (lift t l)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X₂.Finite]
  signature: [X₃.Finite] (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄)
  body: finite_of_isPullback (IsPullback.of_hasPullback r b)

中文:
实例 [X₂.有限]
  签名: [X₃.有限] (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄)
  定义体: finite_of_isPullback (IsPullback.of_hasPullback r b)

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, finite_of_isPullback, of_hasPullback
-/
instance [X₂.Finite] [X₃.Finite] (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) :
    (pullback r b).Finite :=
  finite_of_isPullback (IsPullback.of_hasPullback r b)

end SSet
