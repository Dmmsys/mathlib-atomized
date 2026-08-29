/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span

/-!
# Hahn-Banach extension theorem

In this file, we prove the analytic Hahn-Banach theorem for normed vector spaces. For any continuous
linear functional on a subspace, we can extend it to the entire space without changing
its norm. For Hahn-Banach theorems for locally convex spaces, see
`Mathlib.Analysis.LocallyConvex.HahnBanach`.

We prove
* `exists_extension_norm_eq`: Hahn-Banach theorem for continuous linear functionals on normed spaces
  over `ℝ` or `ℂ`.

In order to state and prove the corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `RCLike 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ‖x‖` (where the norm has to be interpreted as an element
of `𝕜`).
-/

public section


universe u v

section RCLike

open RCLike

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] {E : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Hahn-Banach theorem** for continuous linear functions over `𝕜`
satisfying `IsRCLikeNormedField 𝕜`. -/
@[wikidata Q866116]
/--
theorem `exists_extension_norm_eq` / 定理 `exists_extension_norm_eq`

English:
theorem exists_extension_norm_eq
  given: (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p)
  proof: by
  obtain ⟨g, hg, hl⟩ := by
    refine Module.Dual.exists_continuous_extension_of_le_seminorm p f
      (show Continuous (‖f‖₊ • (normSeminorm 𝕜 E)) from ?_) fun x => f.le_opNorm x
    exact continuous_norm.const_smul ‖f‖₊
  refine ⟨g, hg, le_antisymm (g.opNorm_le_bound (norm_nonneg f) hl) ?_⟩
  e

中文:
定理 exists_extension_norm_eq
  条件: (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p)
  证明: by
  obtain ⟨g, hg, hl⟩ := by
    refine Module.Dual.exists_continuous_extension_of_le_seminorm p f
      (show Continuous (‖f‖₊ • (normSeminorm 𝕜 E)) from ?_) fun x => f.le_opNorm x
    exact continuous_norm.const_smul ‖f‖₊
  refine ⟨g, hg, le_antisymm (g.opNorm_le_bound (norm_nonneg f) hl) ?_⟩
  e

Depends on / 依赖: Continuous, Module, Module.Dual.exists_continuous_extension_of_le_seminorm, const_smul, continuous_norm, continuous_norm.const_smul, exists_continuous_extension_of_le_seminorm, f.le_opNorm, f.opNorm_le_bound, g.le_opNorm, g.opNorm_le_bound, le_antisymm, le_opNorm, normSeminorm, norm_nonneg, opNorm_le_bound
-/
theorem exists_extension_norm_eq (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    exists g : StrongDual 𝕜 E, (forall x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  obtain ⟨g, hg, hl⟩ := by
    refine Module.Dual.exists_continuous_extension_of_le_seminorm p f
      (show Continuous (‖f‖₊ • (normSeminorm 𝕜 E)) from ?_) fun x => f.le_opNorm x
    exact continuous_norm.const_smul ‖f‖₊
  refine ⟨g, hg, le_antisymm (g.opNorm_le_bound (norm_nonneg f) hl) ?_⟩
  exact f.opNorm_le_bound (norm_nonneg _) fun x => by simpa [hg x] using g.le_opNorm x

end RCLike

section DualVector

variable (𝕜 : Type v) [RCLike 𝕜]

open ContinuousLinearEquiv Submodule

section Seminormed

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `exists_dual_vector` / 定理 `exists_dual_vector`

English:
theorem exists_dual_vector
  given: (x : E) (h : ‖x‖ != 0)
  statement: exists g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖
  proof: by
  have hhomothety := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (ne_zero_of_norm_ne_zero h)
  let coord : span 𝕜 {x} ->L[𝕜] 𝕜 := (ofHomothety _ _ (by positivity) hhomothety).symm
  obtain ⟨g, hg⟩ := exists_extension_norm_eq (span 𝕜 {x}) ((‖x‖ : 𝕜) • coord)
  have hval : g x = ‖x‖ := by
    

中文:
定理 exists_dual_vector
  条件: (x : E) (h : ‖x‖ != 0)
  结论: 存在 g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖
  证明: by
  have hhomothety := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (ne_zero_of_norm_ne_zero h)
  let coord : span 𝕜 {x} ->L[𝕜] 𝕜 := (ofHomothety _ _ (by positivity) hhomothety).symm
  obtain ⟨g, hg⟩ := exists_extension_norm_eq (span 𝕜 {x}) ((‖x‖ : 𝕜) • coord)
  have hval : g x = ‖x‖ := by
    

Depends on / 依赖: LinearEquiv, LinearEquiv.coord_self, LinearEquiv.toSpanNonzeroSingleton_homothety, Submodule, Submodule.coe_mk, algebraMap_smul, coe_mk, coord_self, exists_extension_norm_eq, hg.left, hhomothety, ne_zero_of_norm_ne_zero, ofHomothety, toSpanNonzeroSingleton_homothety
-/
theorem exists_dual_vector (x : E) (h : ‖x‖ != 0) : exists g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  have hhomothety := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (ne_zero_of_norm_ne_zero h)
  let coord : span 𝕜 {x} ->L[𝕜] 𝕜 := (ofHomothety _ _ (by positivity) hhomothety).symm
  obtain ⟨g, hg⟩ := exists_extension_norm_eq (span 𝕜 {x}) ((‖x‖ : 𝕜) • coord)
  have hval : g x = ‖x‖ := by
    have hgx : g x = g (⟨x, by simp⟩ : span 𝕜 {x}) := by rw [Submodule.coe_mk]
    have hcx : coord ⟨x, _⟩ = 1 := LinearEquiv.coord_self 𝕜 E x (ne_zero_of_norm_ne_zero h)
    simp [-algebraMap_smul, hgx, ↓hg.left, hcx]
  refine ⟨g, le_antisymm ?_ ?_, hval⟩
  · simp only [hg.right, norm_smul, norm_algebraMap', norm_norm]
    grw [coord.opNorm_le_bound (by positivity)
      (fun y => (homothety_inverse _ (by positivity) _ hhomothety y).le), mul_inv_cancel₀ h]
  · have hle := g.le_opNorm x
    simp only [hval, norm_algebraMap', norm_norm] at hle
    exact one_le_of_le_mul_right₀ (by positivity) hle

/--
theorem `exists_dual_vector''` / 定理 `exists_dual_vector''`

English:
theorem exists_dual_vector''
  given: (x : E)
  statement: exists g : StrongDual 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖x‖
  proof: by
  by_cases hx : ‖x‖ = 0
  · exact ⟨0, by simp, by simp [hx]⟩
  · obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 x hx
    exact ⟨g, hg.left.le, hg.right⟩

中文:
定理 exists_dual_vector''
  条件: (x : E)
  结论: 存在 g : StrongDual 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖x‖
  证明: by
  by_cases hx : ‖x‖ = 0
  · exact ⟨0, by simp, by simp [hx]⟩
  · obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 x hx
    exact ⟨g, hg.left.le, hg.right⟩

Depends on / 依赖: exists_dual_vector, hg.left.le, hg.right
-/
theorem exists_dual_vector'' (x : E) : exists g : StrongDual 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · exact ⟨0, by simp, by simp [hx]⟩
  · obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 x hx
    exact ⟨g, hg.left.le, hg.right⟩

end Seminormed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `exists_dual_vector'` / 定理 `exists_dual_vector'`

English:
theorem exists_dual_vector'
  given: [Nontrivial E] (x : E)
  statement: exists g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖
  proof: by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_norm_ne_zero E
    obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 y hy
    exact ⟨g, hg.left, by simp [hx]⟩
  · exact exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)

中文:
定理 exists_dual_vector'
  条件: [Nontrivial E] (x : E)
  结论: 存在 g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖
  证明: by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_norm_ne_zero E
    obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 y hy
    exact ⟨g, hg.left, by simp [hx]⟩
  · exact exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)

Depends on / 依赖: exists_dual_vector, exists_norm_ne_zero, hg.left, norm_ne_zero_iff, norm_ne_zero_iff.mpr
-/
theorem exists_dual_vector' [Nontrivial E] (x : E) : exists g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_norm_ne_zero E
    obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 y hy
    exact ⟨g, hg.left, by simp [hx]⟩
  · exact exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)

end DualVector
