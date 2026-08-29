/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Long exact sequence in group cohomology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes
`0 ⟶ inhomogeneousCochains X₁ ⟶ inhomogeneousCochains X₂ ⟶ inhomogeneousCochains X₃ ⟶ 0`.

Since the cohomology of `inhomogeneousCochains Xᵢ` is the group cohomology of `Xᵢ`, this allows us
to specialize API about long exact sequences to group cohomology.

## Main Definitions

* `groupCohomology.δ hX i j hij`: the connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

## Main Statements

* `groupCohomology.δ_naturality`: naturality of the connecting homomorphism.

-/

public section

universe u v

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_cochainsFunctor_shortExact` / 引理 `map_cochainsFunctor_shortExact`

English:
lemma map_cochainsFunctor_shortExact
  proof: HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, Li

中文:
引理 map_cochainsFunctor_shortExact
  证明: HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, Li

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shortExact_of_degreewise_shortExact, LinearMap, LinearMap.ker, LinearMap.ker_compLeft, LinearMap.range, LinearMap.range_compLeft, ModuleCat, X.f.hom.toLinearMap, X.g.hom.toLinearMap, cochainsMap_id_f_map_epi, cochainsMap_id_f_map_mono, epi_g, hX.epi_g, hX.exact.map, hX.mono_f, ker_compLeft, moduleCat_exact_iff_range_eq_ker, moduleCat_range_eq_ker, mono_f
-/
lemma map_cochainsFunctor_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this]
    mono_f := letI := hX.mono_f; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; cochainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/--
Definition of `mapShortComplex₁` / `mapShortComplex₁` 的定义

English:
abbreviation mapShortComplex₁
  signature: {i j : Nat} (hij : i + 1 = j)
  body: (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

中文:
缩写 mapShortComplex₁
  签名: {i j : 自然数} (hij : i + 1 = j)
  定义体: (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

Depends on / 依赖: map_cochainsFunctor_shortExact, snakeInput
-/
noncomputable abbrev mapShortComplex₁ {i j : Nat} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/--
Definition of `mapShortComplex₂` / `mapShortComplex₂` 的定义

English:
abbreviation mapShortComplex₂
  signature: (i : Nat)
  body: X.map (functor k G i)

中文:
缩写 mapShortComplex₂
  签名: (i : 自然数)
  定义体: X.map (functor k G i)

Depends on / 依赖: X.map, functor
-/
noncomputable abbrev mapShortComplex₂ (i : Nat) := X.map (functor k G i)

/--
Definition of `mapShortComplex₃` / `mapShortComplex₃` 的定义

English:
abbreviation mapShortComplex₃
  signature: {i j : Nat} (hij : i + 1 = j)
  body: (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

中文:
缩写 mapShortComplex₃
  签名: {i j : 自然数} (hij : i + 1 = j)
  定义体: (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

Depends on / 依赖: map_cochainsFunctor_shortExact, snakeInput
-/
noncomputable abbrev mapShortComplex₃ {i j : Nat} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

/--
lemma `mapShortComplex₁_exact` / 引理 `mapShortComplex₁_exact`

English:
lemma mapShortComplex₁_exact
  given: {i j : Nat} (hij : i + 1 = j)
  proof: (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

中文:
引理 mapShortComplex₁_exact
  条件: {i j : 自然数} (hij : i + 1 = j)
  证明: (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

Depends on / 依赖: map_cochainsFunctor_shortExact
-/
lemma mapShortComplex₁_exact {i j : Nat} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

/--
lemma `mapShortComplex₂_exact` / 引理 `mapShortComplex₂_exact`

English:
lemma mapShortComplex₂_exact
  given: (i : Nat)
  proof: (map_cochainsFunctor_shortExact hX).homology_exact₂ i

中文:
引理 mapShortComplex₂_exact
  条件: (i : 自然数)
  证明: (map_cochainsFunctor_shortExact hX).homology_exact₂ i

Depends on / 依赖: map_cochainsFunctor_shortExact
-/
lemma mapShortComplex₂_exact (i : Nat) :
    (mapShortComplex₂ X i).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₂ i

/--
lemma `mapShortComplex₃_exact` / 引理 `mapShortComplex₃_exact`

English:
lemma mapShortComplex₃_exact
  given: {i j : Nat} (hij : i + 1 = j)
  proof: (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

中文:
引理 mapShortComplex₃_exact
  条件: {i j : 自然数} (hij : i + 1 = j)
  证明: (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

Depends on / 依赖: map_cochainsFunctor_shortExact
-/
lemma mapShortComplex₃_exact {i j : Nat} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: (i j : Nat) (hij : i + 1 = j)
  body: (map_cochainsFunctor_shortExact hX).δ i j hij

中文:
缩写 δ
  签名: (i j : 自然数) (hij : i + 1 = j)
  定义体: (map_cochainsFunctor_shortExact hX).δ i j hij

Depends on / 依赖: map_cochainsFunctor_shortExact
-/
noncomputable abbrev δ (i j : Nat) (hij : i + 1 = j) :
    groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
  (map_cochainsFunctor_shortExact hX).δ i j hij

open Limits

/--
theorem `epi_δ_of_isZero` / 定理 `epi_δ_of_isZero`

English:
theorem epi_δ_of_isZero
  given: (n : Nat) (h : IsZero (groupCohomology X.X₂ (n + 1)))
  proof: SnakeInput.epi_δ _ h

中文:
定理 epi_δ_of_isZero
  条件: (n : 自然数) (h : IsZero (groupCohomology X.X₂ (n + 1)))
  证明: SnakeInput.epi_δ _ h

Depends on / 依赖: SnakeInput, SnakeInput.epi_
-/
theorem epi_δ_of_isZero (n : Nat) (h : IsZero (groupCohomology X.X₂ (n + 1))) :
    Epi (δ hX n (n + 1) rfl) := SnakeInput.epi_δ _ h

/--
theorem `mono_δ_of_isZero` / 定理 `mono_δ_of_isZero`

English:
theorem mono_δ_of_isZero
  given: (n : Nat) (h : IsZero (groupCohomology X.X₂ n))
  proof: SnakeInput.mono_δ _ h

中文:
定理 mono_δ_of_isZero
  条件: (n : 自然数) (h : IsZero (groupCohomology X.X₂ n))
  证明: SnakeInput.mono_δ _ h

Depends on / 依赖: SnakeInput, SnakeInput.mono_
-/
theorem mono_δ_of_isZero (n : Nat) (h : IsZero (groupCohomology X.X₂ n)) :
    Mono (δ hX n (n + 1) rfl) := SnakeInput.mono_δ _ h

/--
theorem `isIso_δ_of_isZero` / 定理 `isIso_δ_of_isZero`

English:
theorem isIso_δ_of_isZero
  statement: (n : Nat) (h : IsZero (groupCohomology X.X₂ n))
  proof: SnakeInput.isIso_δ _ h hs

中文:
定理 isIso_δ_of_isZero
  结论: (n : 自然数) (h : IsZero (groupCohomology X.X₂ n))
  证明: SnakeInput.isIso_δ _ h hs

Depends on / 依赖: SnakeInput, SnakeInput.isIso_
-/
theorem isIso_δ_of_isZero (n : Nat) (h : IsZero (groupCohomology X.X₂ n))
    (hs : IsZero (groupCohomology X.X₂ (n + 1))) :
    IsIso (δ hX n (n + 1) rfl) := SnakeInput.isIso_δ _ h hs

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cocyclesMkOfCompEqD` / `cocyclesMkOfCompEqD` 的定义

English:
abbreviation cocyclesMkOfCompEqD
  signature: {i j : Nat} {y : (Fin i -> G) -> X.X₂}
  body: cocyclesMk x by simpa [CochainComplex.of.d] using!
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) (j + 1))

中文:
缩写 cocyclesMkOfCompEqD
  签名: {i j : 自然数} {y : (Fin i -> G) -> X.X₂}
  定义体: cocyclesMk x by simpa [CochainComplex.of.d] using!
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) (j + 1))

Depends on / 依赖: CochainComplex, CochainComplex.of.d, cocyclesMk, d_eq_zero_of_f_eq_d_apply, map_cochainsFunctor_shortExact
-/
noncomputable abbrev cocyclesMkOfCompEqD {i j : Nat} {y : (Fin i -> G) -> X.X₂}
    {x : (Fin j -> G) -> X.X₁} (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    cocycles X.X₁ j :=
cocyclesMk x by simpa [CochainComplex.of.d] using!
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) (j + 1))

/--
theorem `δ_apply` / 定理 `δ_apply`

English:
theorem δ_apply
  statement: {i j : Nat} (hij : i + 1 = j)
  proof: by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa using! hx) (j + 1) (by simp)

中文:
定理 δ_apply
  结论: {i j : 自然数} (hij : i + 1 = j)
  证明: by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa using! hx) (j + 1) (by simp)

Depends on / 依赖: map_cochainsFunctor_shortExact
-/
theorem δ_apply {i j : Nat} (hij : i + 1 = j)
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be an `i`-cocycle for `X₃`
    (z : (Fin i -> G) -> X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    -- Let `y` be an `i`-cochain for `X₂` such that `g ∘ y = z`
    (y : (Fin i -> G) -> X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    -- Let `x` be an `i + 1`-cochain for `X₁` such that `f ∘ x = d(y)`
    (x : (Fin j -> G) -> X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    -- Then `x` is an `i + 1`-cocycle and `δ z = x` in `Hⁱ⁺¹(X₁)`.
    δ hX i j hij (π X.X₃ i <| cocyclesMk z (by subst hij; simpa [CochainComplex.of.d] using! hz)) =
      π X.X₁ j (cocyclesMkOfCompEqD hX hx) := by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa using! hx) (j + 1) (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_cocycles₁_of_comp_eq_d₀₁` / 定理 `mem_cocycles₁_of_comp_eq_d₀₁`

English:
theorem mem_cocycles₁_of_comp_eq_d₀₁
  proof: by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

中文:
定理 mem_cocycles₁_of_comp_eq_d₀₁
  证明: by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

Depends on / 依赖: Function, Function.Injective.comp_left, Injective, LinearMap, LinearMap.compLeft, MonoidHom, MonoidHom.id, Rep.mono_iff_injective, compLeft, comp_left, mapShortComplexH1, mono_iff_injective, shortComplexH1
-/
theorem mem_cocycles₁_of_comp_eq_d₀₁
    {y : X.X₂} {x : G -> X.X₁} (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    x in cocycles₁ X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `δ₀_apply` / 定理 `δ₀_apply`

English:
theorem δ₀_apply
  proof: by
  simpa [H0Iso, H1π, ← cocyclesMk₁_eq X.X₁, ← cocyclesMk₀_eq z] using!
    δ_apply hX rfl ((cochainsIso₀ X.X₃).inv z.1) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₀₁_comp_inv]; simp)
      ((cochainsIso₀ X.X₂).inv y)
(by ext; simp [← hy, cochainsIso₀]) ((cochainsIso

中文:
定理 δ₀_apply
  证明: by
  simpa [H0Iso, H1π, ← cocyclesMk₁_eq X.X₁, ← cocyclesMk₀_eq z] using!
    δ_apply hX rfl ((cochainsIso₀ X.X₃).inv z.1) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₀₁_comp_inv]; simp)
      ((cochainsIso₀ X.X₂).inv y)
(by ext; simp [← hy, cochainsIso₀]) ((cochainsIso

Depends on / 依赖: CommSq, CommSq.vert_inv, LinearMap, LinearMap.comp_apply, ModuleCat, ModuleCat.hom_comp, MonoidHom, MonoidHom.id, comp_apply, congr_fun, hom_comp, vert_inv
-/
theorem δ₀_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z : X₃ᴳ` and `y : X₂` be such that `g(y) = z`.
    (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    -- Let `x` be a 1-cochain for `X₁` such that `f ∘ x = d(y)`.
    (x : G -> X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    -- Then `x` is a 1-cocycle and `δ z = x` in `H¹(X₁)`.
    δ hX 0 1 rfl ((H0Iso X.X₃).inv z) = H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  simpa [H0Iso, H1π, ← cocyclesMk₁_eq X.X₁, ← cocyclesMk₀_eq z] using!
    δ_apply hX rfl ((cochainsIso₀ X.X₃).inv z.1) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₀₁_comp_inv]; simp)
      ((cochainsIso₀ X.X₂).inv y)
(by ext; simp [← hy, cochainsIso₀]) ((cochainsIso₁ X.X₁).inv x) by
      ext g
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₀₁_comp_inv]
      simpa [← hx] using! congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_1_comp_cochainsIso₁ (MonoidHom.id G) X.f⟩).w) x)) g

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_cocycles₂_of_comp_eq_d₁₂` / 定理 `mem_cocycles₂_of_comp_eq_d₁₂`

English:
theorem mem_cocycles₂_of_comp_eq_d₁₂
  proof: by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH2, LinearMap.compLeft]

中文:
定理 mem_cocycles₂_of_comp_eq_d₁₂
  证明: by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH2, LinearMap.compLeft]

Depends on / 依赖: Function, Function.Injective.comp_left, Injective, LinearMap, LinearMap.compLeft, MonoidHom, MonoidHom.id, Rep.mono_iff_injective, Valuation, Valuation.map_zero, compLeft, comp_left, mapShortComplexH2, map_zero, mono_iff_injective, shortComplexH2
-/
theorem mem_cocycles₂_of_comp_eq_d₁₂
    {y : G -> X.X₂} {x : G × G -> X.X₁} (hx : X.f.hom ∘ x = d₁₂ X.X₂ y) :
    x in cocycles₂ X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH2, LinearMap.compLeft]

/--
theorem `δ₁_apply` / 定理 `δ₁_apply`

English:
theorem δ₁_apply
  proof: by
  simpa [H1π, H2π, ← cocyclesMk₂_eq X.X₁, ← cocyclesMk₁_eq X.X₃] using!
    δ_apply hX rfl ((cochainsIso₁ X.X₃).inv z) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₂_comp_inv]
      simp [cocycles₁.d₁₂_apply z]) ((cochainsIso₁ X.X₂).inv y) (by ext; simp [cochainsIso₁

中文:
定理 δ₁_apply
  证明: by
  simpa [H1π, H2π, ← cocyclesMk₂_eq X.X₁, ← cocyclesMk₁_eq X.X₃] using!
    δ_apply hX rfl ((cochainsIso₁ X.X₃).inv z) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₂_comp_inv]
      simp [cocycles₁.d₁₂_apply z]) ((cochainsIso₁ X.X₂).inv y) (by ext; simp [cochainsIso₁

Depends on / 依赖: CommSq, CommSq.vert_inv, LinearMap, LinearMap.comp_apply, ModuleCat, ModuleCat.hom_comp, Valuation, Valuation.map_one, comp_apply, congr_fun, hom_comp, map_one, vert_inv
-/
theorem δ₁_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be a 1-cocycle for `X₃` and `y` be a 1-cochain for `X₂` such that `g ∘ y = z`.
    (z : cocycles₁ X.X₃) (y : G -> X.X₂) (hy : X.g.hom ∘ y = z)
    -- Let `x` be a 2-cochain for `X₁` such that `f ∘ x = d(y)`.
    (x : G × G -> X.X₁) (hx : X.f.hom ∘ x = d₁₂ X.X₂ y) :
    -- Then `x` is a 2-cocycle and `δ z = x` in `H²(X₁)`.
    δ hX 1 2 rfl (H1π X.X₃ z) = H2π X.X₁ ⟨x, mem_cocycles₂_of_comp_eq_d₁₂ hX hx⟩ := by
  simpa [H1π, H2π, ← cocyclesMk₂_eq X.X₁, ← cocyclesMk₁_eq X.X₃] using!
    δ_apply hX rfl ((cochainsIso₁ X.X₃).inv z) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₂_comp_inv]
      simp [cocycles₁.d₁₂_apply z]) ((cochainsIso₁ X.X₂).inv y) (by ext; simp [cochainsIso₁, ← hy])
((cochainsIso₂ X.X₁).inv x) by
      ext g
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₂_comp_inv]
      simpa [← hx] using! congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_2_comp_cochainsIso₂ (MonoidHom.id G) X.f⟩).w) x)) g

/--
lemma `map_cochainsFunctor_eval_shortExact` / 引理 `map_cochainsFunctor_eval_shortExact`

English:
lemma map_cochainsFunctor_eval_shortExact
  given: (n : Nat)
  proof: (map_cochainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

omit hX in

中文:
引理 map_cochainsFunctor_eval_shortExact
  条件: (n : 自然数)
  证明: (map_cochainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

omit hX in

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, Valuation, Valuation.map_mul, map_cochainsFunctor_shortExact, map_mul, map_of_exact
-/
lemma map_cochainsFunctor_eval_shortExact (n : Nat) :
    ShortExact (X.map <| cochainsFunctor k G ⋙ HomologicalComplex.eval (ModuleCat k) (.up Nat) n) :=
  (map_cochainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

omit hX in
/--
theorem `δ_naturality` / 定理 `δ_naturality`

English:
theorem δ_naturality
  statement: {X1 X2 : ShortComplex (Rep k G)} (hX1 : X1.ShortExact)
  proof: HomologicalComplex.HomologySequence.δ_naturality
    ((cochainsFunctor k G).mapShortComplex.map F)
    (map_cochainsFunctor_shortExact hX1) (map_cochainsFunctor_shortExact hX2) i j hij

中文:
定理 δ_naturality
  结论: {X1 X2 : ShortComplex (Rep k G)} (hX1 : X1.ShortExact)
  证明: HomologicalComplex.HomologySequence.δ_naturality
    ((cochainsFunctor k G).mapShortComplex.map F)
    (map_cochainsFunctor_shortExact hX1) (map_cochainsFunctor_shortExact hX2) i j hij

Depends on / 依赖: HomologicalComplex, HomologicalComplex.HomologySequence, HomologySequence, Valuation, Valuation.map_add, cochainsFunctor, mapShortComplex, mapShortComplex.map, map_add, map_cochainsFunctor_shortExact
-/
theorem δ_naturality {X1 X2 : ShortComplex (Rep k G)} (hX1 : X1.ShortExact)
    (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i j : Nat) (hij : i + 1 = j) :
    (δ hX1 i j hij) ≫ map (.id G) F.τ₁ j = map (.id G) F.τ₃ i ≫ δ hX2 i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cochainsFunctor k G).mapShortComplex.map F)
    (map_cochainsFunctor_shortExact hX1) (map_cochainsFunctor_shortExact hX2) i j hij

end groupCohomology
