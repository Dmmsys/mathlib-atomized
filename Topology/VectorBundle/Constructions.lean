/-
Copyright (c) 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Standard constructions on vector bundles

This file contains several standard constructions on vector bundles:

* `Bundle.Trivial.vectorBundle 𝕜 B F`: the trivial vector bundle with scalar field `𝕜` and model
  fiber `F` over the base `B`

* `VectorBundle.prod`: for vector bundles `E₁` and `E₂` with scalar field `𝕜` over a common base,
  a vector bundle structure on their direct sum `E₁ ×ᵇ E₂` (the notation stands for
  `fun x ↦ E₁ x × E₂ x`).

* `VectorBundle.pullback`: for a vector bundle `E` over `B`, a vector bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags
Vector bundle, direct sum, pullback
-/

public section

noncomputable section

open Bundle Set FiberBundle

/-! ### The trivial vector bundle -/

namespace Bundle.Trivial

variable (𝕜 : Type*) (B : Type*) (F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace B]

/--
Instance `trivialization.isLinear` / 实例 `trivialization.isLinear`

English:
instance trivialization.isLinear
  signature: : (trivialization B F).IsLinear 𝕜 where
  body: ⟨fun _ _ => rfl, fun _ _ => rfl⟩

中文:
实例 trivialization.isLinear
  签名: : (trivialization B F).IsLinear 𝕜 where
  定义体: ⟨fun _ _ => rfl, fun _ _ => rfl⟩
-/
instance trivialization.isLinear : (trivialization B F).IsLinear 𝕜 where
  linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable {𝕜} in
/--
theorem `trivialization.coordChangeL` / 定理 `trivialization.coordChangeL`

English:
theorem trivialization.coordChangeL
  given: (b : B)
  proof: by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]

中文:
定理 trivialization.coordChangeL
  条件: (b : B)
  证明: by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]

Depends on / 依赖: Trivialization, Trivialization.coordChangeL_apply, coordChangeL_apply, exacts, mem_univ
-/
theorem trivialization.coordChangeL (b : B) :
    (trivialization B F).coordChangeL 𝕜 (trivialization B F) b =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]

/--
Instance `vectorBundle` / 实例 `vectorBundle`

English:
instance vectorBundle
  signature: : VectorBundle 𝕜 F (Bundle.Trivial B F) where
  body: by
    rw [eq_trivialization B F e]
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain rfl := eq_trivialization B F e
    obtain rfl := eq_trivialization B F e'
    simp only [trivialization.coordChangeL]
    exact continuous_const.continuousOn

中文:
实例 vectorBundle
  签名: : VectorBundle 𝕜 F (Bundle.Trivial B F) where
  定义体: by
    rw [eq_trivialization B F e]
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain rfl := eq_trivialization B F e
    obtain rfl := eq_trivialization B F e'
    simp only [trivialization.coordChangeL]
    exact continuous_const.continuousOn

Depends on / 依赖: continuousOn, continuousOn_coordChange, continuous_const, continuous_const.continuousOn, coordChangeL, eq_trivialization, infer_instance, trivialization, trivialization.coordChangeL
-/
instance vectorBundle : VectorBundle 𝕜 F (Bundle.Trivial B F) where
  trivialization_linear' e he := by
    rw [eq_trivialization B F e]
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain rfl := eq_trivialization B F e
    obtain rfl := eq_trivialization B F e'
    simp only [trivialization.coordChangeL]
    exact continuous_const.continuousOn

/--
lemma `linearMapAt_trivialization` / 引理 `linearMapAt_trivialization`

English:
lemma linearMapAt_trivialization
  given: (x : B)
  proof: by
  ext v
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  rfl

中文:
引理 linearMapAt_trivialization
  条件: (x : B)
  证明: by
  ext v
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  rfl
-/
@[simp] lemma linearMapAt_trivialization (x : B) :
    (trivialization B F).linearMapAt 𝕜 x = LinearMap.id := by
  ext v
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  rfl

/--
lemma `continuousLinearMapAt_trivialization` / 引理 `continuousLinearMapAt_trivialization`

English:
lemma continuousLinearMapAt_trivialization
  given: (x : B)
  proof: by
  ext; simp

中文:
引理 continuousLinearMapAt_trivialization
  条件: (x : B)
  证明: by
  ext; simp
-/
@[simp] lemma continuousLinearMapAt_trivialization (x : B) :
    (trivialization B F).continuousLinearMapAt 𝕜 x = ContinuousLinearMap.id 𝕜 F := by
  ext; simp

/--
lemma `symmₗ_trivialization` / 引理 `symmₗ_trivialization`

English:
lemma symmₗ_trivialization
  given: (x : B)
  proof: by
  ext; simp [trivialization_symm_apply B F]

中文:
引理 symmₗ_trivialization
  条件: (x : B)
  证明: by
  ext; simp [trivialization_symm_apply B F]
-/
@[simp] lemma symmₗ_trivialization (x : B) :
    (trivialization B F).symmₗ 𝕜 x = LinearMap.id := by
  ext; simp [trivialization_symm_apply B F]

/--
lemma `symmL_trivialization` / 引理 `symmL_trivialization`

English:
lemma symmL_trivialization
  given: (x : B)
  proof: by
  ext; simp [trivialization_symm_apply B F]

中文:
引理 symmL_trivialization
  条件: (x : B)
  证明: by
  ext; simp [trivialization_symm_apply B F]
-/
@[simp] lemma symmL_trivialization (x : B) :
    (trivialization B F).symmL 𝕜 x = ContinuousLinearMap.id 𝕜 F := by
  ext; simp [trivialization_symm_apply B F]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `continuousLinearEquivAt_trivialization` / 引理 `continuousLinearEquivAt_trivialization`

English:
lemma continuousLinearEquivAt_trivialization
  given: (x : B)
  proof: by
  ext; simp

中文:
引理 continuousLinearEquivAt_trivialization
  条件: (x : B)
  证明: by
  ext; simp
-/
@[simp] lemma continuousLinearEquivAt_trivialization (x : B) :
    (trivialization B F).continuousLinearEquivAt 𝕜 x (mem_univ _) =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext; simp

end Bundle.Trivial

/-! ### Direct sum of two vector bundles -/

section

variable (𝕜 : Type*) {B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] (F₁ : Type*)
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B -> Type*) [TopologicalSpace (TotalSpace F₁ E₁)]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B -> Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Bundle.Trivialization

variable {F₁ E₁ F₂ E₂}
variable [forall x, AddCommMonoid (E₁ x)] [forall x, Module 𝕜 (E₁ x)]
  [forall x, AddCommMonoid (E₂ x)] [forall x, Module 𝕜 (E₂ x)] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

/--
Instance `prod.isLinear` / 实例 `prod.isLinear`

English:
instance prod.isLinear
  signature: [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜]
  body: fun _ ⟨h₁, h₂⟩ =>
    (((e₁.linear 𝕜 h₁).mk' _).prodMap ((e₂.linear 𝕜 h₂).mk' _)).isLinear

@[simp]

中文:
实例 prod.isLinear
  签名: [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜]
  定义体: fun _ ⟨h₁, h₂⟩ =>
    (((e₁.linear 𝕜 h₁).mk' _).prodMap ((e₂.linear 𝕜 h₂).mk' _)).isLinear

@[simp]
-/
instance prod.isLinear [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] : (e₁.prod e₂).IsLinear 𝕜 where
  linear := fun _ ⟨h₁, h₂⟩ =>
    (((e₁.linear 𝕜 h₁).mk' _).prodMap ((e₂.linear 𝕜 h₂).mk' _)).isLinear

@[simp]
/--
theorem `coordChangeL_prod` / 定理 `coordChangeL_prod`

English:
theorem coordChangeL_prod
  statement: [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] ⦃b⦄
  proof: by
  rw [ContinuousLinearMap.ext_iff]; rw [ContinuousLinearMap.coe_prodMap']
  rintro ⟨v₁, v₂⟩
  change
    (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
  rw [e₁.coordChangeL_apply e₁']; rw [e₂.coordChangeL_apply e₂']; rw [(e₁

中文:
定理 coordChangeL_prod
  结论: [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] ⦃b⦄
  证明: by
  rw [ContinuousLinearMap.ext_iff]; rw [ContinuousLinearMap.coe_prodMap']
  rintro ⟨v₁, v₂⟩
  change
    (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
  rw [e₁.coordChangeL_apply e₁']; rw [e₂.coordChangeL_apply e₂']; rw [(e₁

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_prodMap, ContinuousLinearMap.ext_iff, coe_prodMap, coordChangeL, coordChangeL_apply, exacts, ext_iff
-/
theorem coordChangeL_prod [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] ⦃b⦄
    (hb : (b in e₁.baseSet ∧ b in e₂.baseSet) ∧ b in e₁'.baseSet ∧ b in e₂'.baseSet) :
    ((e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b : F₁ × F₂ ->L[𝕜] F₁ × F₂) =
      (e₁.coordChangeL 𝕜 e₁' b : F₁ ->L[𝕜] F₁).prodMap (e₂.coordChangeL 𝕜 e₂' b) := by
  rw [ContinuousLinearMap.ext_iff]; rw [ContinuousLinearMap.coe_prodMap']
  rintro ⟨v₁, v₂⟩
  change
    (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
  rw [e₁.coordChangeL_apply e₁']; rw [e₂.coordChangeL_apply e₂']; rw [(e₁.prod e₂).coordChangeL_apply']
  exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]

variable {e₁ e₂} [forall x : B, TopologicalSpace (E₁ x)] [forall x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/--
theorem `prod_apply'` / 定理 `prod_apply'`

English:
theorem prod_apply'
  statement: [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B} (hx₁ : x in e₁.baseSet)
  proof: rfl

中文:
定理 prod_apply'
  结论: [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B} (hx₁ : x in e₁.baseSet)
  证明: rfl
-/
theorem prod_apply' [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B} (hx₁ : x in e₁.baseSet)
    (hx₂ : x in e₂.baseSet) (v₁ : E₁ x) (v₂ : E₂ x) :
    prod e₁ e₂ ⟨x, (v₁, v₂)⟩ =
      ⟨x, e₁.continuousLinearEquivAt 𝕜 x hx₁ v₁, e₂.continuousLinearEquivAt 𝕜 x hx₂ v₂⟩ :=
  rfl

end Bundle.Trivialization

open Trivialization

variable [forall x, AddCommMonoid (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [forall x, AddCommMonoid (E₂ x)]
  [forall x, Module 𝕜 (E₂ x)] [forall x : B, TopologicalSpace (E₁ x)] [forall x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `VectorBundle.prod` / 实例 `VectorBundle.prod`

English:
instance VectorBundle.prod
  signature: [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
  body: by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine (((continuousOn_coordChange 𝕜 e₁ e₁').mono ?_).prod_mapL 𝕜
      ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)).congr ?_ <;>
    

中文:
实例 VectorBundle.prod
  签名: [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
  定义体: by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine (((continuousOn_coordChange 𝕜 e₁ e₁').mono ?_).prod_mapL 𝕜
      ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)).congr ?_ <;>
    

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, continuousOn_coordChange, coordChangeL, ext_iff, infer_instance, mfld_set_tac, mfld_simps, prod_baseSet, prod_mapL
-/
instance VectorBundle.prod [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] :
    VectorBundle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) where
  trivialization_linear' := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine (((continuousOn_coordChange 𝕜 e₁ e₁').mono ?_).prod_mapL 𝕜
      ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)).congr ?_ <;>
      dsimp only [prod_baseSet, mfld_simps]
    · mfld_set_tac
    · mfld_set_tac
    · rintro b hb
      rw [ContinuousLinearMap.ext_iff]
      rintro ⟨v₁, v₂⟩
      change (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
      rw [e₁.coordChangeL_apply e₁']; rw [e₂.coordChangeL_apply e₂']; rw [(e₁.prod e₂).coordChangeL_apply']
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]

variable {𝕜 F₁ E₁ F₂ E₂}

@[simp]
/--
theorem `Bundle.Trivialization.continuousLinearEquivAt_prod` / 定理 `Bundle.Trivialization.continuousLinearEquivAt_prod`

English:
theorem Bundle.Trivialization.continuousLinearEquivAt_prod
  statement: {e₁ : Trivialization F₁ (π F₁ E₁)}
  proof: by
  ext v : 2
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuousLinearEquivAt_apply 𝕜]; rw [Trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply' 𝕜 hx.1 hx.2 v₁ v₂) :)

中文:
定理 Bundle.Trivialization.continuousLinearEquivAt_prod
  结论: {e₁ : Trivialization F₁ (π F₁ E₁)}
  证明: by
  ext v : 2
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuousLinearEquivAt_apply 𝕜]; rw [Trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply' 𝕜 hx.1 hx.2 v₁ v₂) :)

Depends on / 依赖: Prod.snd, Trivialization, Trivialization.prod, congr_arg, continuousLinearEquivAt_apply, prod_apply
-/
theorem Bundle.Trivialization.continuousLinearEquivAt_prod {e₁ : Trivialization F₁ (π F₁ E₁)}
    {e₂ : Trivialization F₂ (π F₂ E₂)} [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B}
    (hx : x in (e₁.prod e₂).baseSet) :
    (e₁.prod e₂).continuousLinearEquivAt 𝕜 x hx =
      (e₁.continuousLinearEquivAt 𝕜 x hx.1).prodCongr (e₂.continuousLinearEquivAt 𝕜 x hx.2) := by
  ext v : 2
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuousLinearEquivAt_apply 𝕜]; rw [Trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply' 𝕜 hx.1 hx.2 v₁ v₂) :)

end

/-! ### Pullbacks of vector bundles -/

section

variable (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B -> Type*) {B' : Type*} (f : B' -> B)

-- This instance exists to avoid an nsmul diamond.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [forall x
  body: inferInstanceAs SMul R (E (f x))

中文:
实例 [Semiring
  签名: R] [对任意 x
  定义体: inferInstanceAs SMul R (E (f x))
-/
instance [Semiring R] [forall x : B, AddCommMonoid (E x)] [i : forall x, Module R (E x)] (x : B') :
    SMul R ((f *ᵖ E) x) :=
inferInstanceAs SMul R (E (f x))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : forall x : B, AddCommMonoid (E x)] (x : B') : AddCommMonoid ((f *ᵖ E) x)
  body: inferInstanceAs AddCommMonoid (E (f x))

中文:
实例 [i
  签名: : 对任意 x : B, AddCommMonoid (E x)] (x : B') : AddCommMonoid ((f *ᵖ E) x)
  定义体: inferInstanceAs AddCommMonoid (E (f x))

Depends on / 依赖: AddCommMonoid
-/
instance [i : forall x : B, AddCommMonoid (E x)] (x : B') : AddCommMonoid ((f *ᵖ E) x) :=
inferInstanceAs AddCommMonoid (E (f x))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [forall x
  body: inferInstanceAs Module R (E (f x))

中文:
实例 [Semiring
  签名: R] [对任意 x
  定义体: inferInstanceAs Module R (E (f x))

Depends on / 依赖: Module
-/
instance [Semiring R] [forall x : B, AddCommMonoid (E x)] [i : forall x, Module R (E x)] (x : B') :
    Module R ((f *ᵖ E) x) :=
inferInstanceAs Module R (E (f x))

variable {E F} [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [forall x, AddCommMonoid (E x)]
  [forall x, Module 𝕜 (E x)] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/--
Instance `Bundle.Trivialization.pullback_linear` / 实例 `Bundle.Trivialization.pullback_linear`

English:
instance Bundle.Trivialization.pullback_linear
  signature: (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
  body: e.linear 𝕜 h

中文:
实例 Bundle.Trivialization.pullback_linear
  签名: (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
  定义体: e.linear 𝕜 h

Depends on / 依赖: IsLinear
-/
instance Bundle.Trivialization.pullback_linear (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (f : K) : (e.pullback (B' := B') f).IsLinear 𝕜 where
  linear _ h := e.linear 𝕜 h

/--
Instance `VectorBundle.pullback` / 实例 `VectorBundle.pullback`

English:
instance VectorBundle.pullback
  signature: [forall x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  body: by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((continuousOn_coordChange 𝕜 e e').comp
      (map_continuous f).continuousOn fun b hb => hb).congr ?_
    rintro b (hb : f b in e.baseSet inter e'.baseSet); ext v


中文:
实例 VectorBundle.pullback
  签名: [对任意 x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  定义体: by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((continuousOn_coordChange 𝕜 e e').comp
      (map_continuous f).continuousOn fun b hb => hb).congr ?_
    rintro b (hb : f b in e.baseSet inter e'.baseSet); ext v


Depends on / 依赖: baseSet, continuousOn, continuousOn_coordChange, coordChangeL, coordChangeL_apply, e.baseSet, e.coordChangeL, e.coordChangeL_apply, e.pullback, exacts, infer_instance, map_continuous, pullback
-/
instance VectorBundle.pullback [forall x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (f : K) : VectorBundle 𝕜 F ((f : B' -> B) *ᵖ E) where
  trivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((continuousOn_coordChange 𝕜 e e').comp
      (map_continuous f).continuousOn fun b hb => hb).congr ?_
    rintro b (hb : f b in e.baseSet inter e'.baseSet); ext v
    change ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coordChangeL 𝕜 e' (f b)) v
    rw [e.coordChangeL_apply e' hb]; rw [(e.pullback f).coordChangeL_apply' _]
    exacts [rfl, hb]

end
