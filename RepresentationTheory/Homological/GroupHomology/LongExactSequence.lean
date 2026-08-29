/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Long exact sequence in group homology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes
`0 ⟶ inhomogeneousChains X₁ ⟶ inhomogeneousChains X₂ ⟶ inhomogeneousChains X₃ ⟶ 0`.

Since the homology of `inhomogeneousChains Xᵢ` is the group homology of `Xᵢ`, this allows us
to specialize API about long exact sequences to group homology.

## Main definitions

* `groupHomology.δ hX i j hij`: the connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

public section

universe v u

namespace groupHomology

open CategoryTheory ShortComplex Finsupp

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_chainsFunctor_shortExact` / 引理 `map_chainsFunctor_shortExact`

English:
lemma map_chainsFunctor_shortExact
  proof: letI := hX.mono_f
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_

中文:
引理 map_chainsFunctor_shortExact
  证明: letI := hX.mono_f
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shortExact_of_degreewise_shortExact, LinearMap, LinearMap.ker, LinearMap.ker_eq_bot, LinearMap.range, ModuleCat, Rep.mono_iff_injective, X.f.hom.toLinearMap, X.g.hom.toLinearMap, chains, chainsMap_id_f_map_mono, epi_g, hX.epi_g, hX.exact.map, hX.mono_f, ker_eq_bot, ker_mapRange, moduleCat_exact_iff_range_eq_ker, moduleCat_range_eq_ker
-/
lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  letI := hX.mono_f
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, ker_mapRange,
        range_mapRange_linearMap X.f.hom.toLinearMap (LinearMap.ker_eq_bot.2 <|
        (Rep.mono_iff_injective X.f).1 hX.mono_f), this]
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; chainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/--
Definition of `mapShortComplex₁` / `mapShortComplex₁` 的定义

English:
abbreviation mapShortComplex₁
  signature: {i j : Nat} (hij : j + 1 = i)
  body: (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₂'

中文:
缩写 mapShortComplex₁
  签名: {i j : 自然数} (hij : j + 1 = i)
  定义体: (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₂'

Depends on / 依赖: map_chainsFunctor_shortExact, snakeInput
-/
noncomputable abbrev mapShortComplex₁ {i j : Nat} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₂'

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
  signature: {i j : Nat} (hij : j + 1 = i)
  body: (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₁'

中文:
缩写 mapShortComplex₃
  签名: {i j : 自然数} (hij : j + 1 = i)
  定义体: (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₁'

Depends on / 依赖: map_chainsFunctor_shortExact, snakeInput
-/
noncomputable abbrev mapShortComplex₃ {i j : Nat} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₁'

/--
lemma `mapShortComplex₁_exact` / 引理 `mapShortComplex₁_exact`

English:
lemma mapShortComplex₁_exact
  given: {i j : Nat} (hij : j + 1 = i)
  proof: (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

中文:
引理 mapShortComplex₁_exact
  条件: {i j : 自然数} (hij : j + 1 = i)
  证明: (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

Depends on / 依赖: map_chainsFunctor_shortExact
-/
lemma mapShortComplex₁_exact {i j : Nat} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

/--
lemma `mapShortComplex₂_exact` / 引理 `mapShortComplex₂_exact`

English:
lemma mapShortComplex₂_exact
  given: (i : Nat)
  proof: (map_chainsFunctor_shortExact hX).homology_exact₂ i

中文:
引理 mapShortComplex₂_exact
  条件: (i : 自然数)
  证明: (map_chainsFunctor_shortExact hX).homology_exact₂ i

Depends on / 依赖: map_chainsFunctor_shortExact
-/
lemma mapShortComplex₂_exact (i : Nat) :
    (mapShortComplex₂ X i).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₂ i

/--
lemma `mapShortComplex₃_exact` / 引理 `mapShortComplex₃_exact`

English:
lemma mapShortComplex₃_exact
  given: {i j : Nat} (hij : j + 1 = i)
  proof: (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

中文:
引理 mapShortComplex₃_exact
  条件: {i j : 自然数} (hij : j + 1 = i)
  证明: (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

Depends on / 依赖: map_chainsFunctor_shortExact
-/
lemma mapShortComplex₃_exact {i j : Nat} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: (i j : Nat) (hij : j + 1 = i)
  body: (map_chainsFunctor_shortExact hX).δ i j hij

中文:
缩写 δ
  签名: (i j : 自然数) (hij : j + 1 = i)
  定义体: (map_chainsFunctor_shortExact hX).δ i j hij

Depends on / 依赖: map_chainsFunctor_shortExact
-/
noncomputable abbrev δ (i j : Nat) (hij : j + 1 = i) :
    groupHomology X.X₃ i ⟶ groupHomology X.X₁ j :=
  (map_chainsFunctor_shortExact hX).δ i j hij

open Limits

/--
theorem `epi_δ_of_isZero` / 定理 `epi_δ_of_isZero`

English:
theorem epi_δ_of_isZero
  given: (n : Nat) (h : IsZero (groupHomology X.X₂ n))
  proof: SnakeInput.epi_δ _ h

中文:
定理 epi_δ_of_isZero
  条件: (n : 自然数) (h : 是零 (groupHomology X.X₂ n))
  证明: SnakeInput.epi_δ _ h

Depends on / 依赖: SnakeInput, SnakeInput.epi_
-/
theorem epi_δ_of_isZero (n : Nat) (h : IsZero (groupHomology X.X₂ n)) :
    Epi (δ hX (n + 1) n rfl) := SnakeInput.epi_δ _ h

/--
theorem `mono_δ_of_isZero` / 定理 `mono_δ_of_isZero`

English:
theorem mono_δ_of_isZero
  given: (n : Nat) (h : IsZero (groupHomology X.X₂ (n + 1)))
  proof: SnakeInput.mono_δ _ h

中文:
定理 mono_δ_of_isZero
  条件: (n : 自然数) (h : 是零 (groupHomology X.X₂ (n + 1)))
  证明: SnakeInput.mono_δ _ h

Depends on / 依赖: SnakeInput, SnakeInput.mono_
-/
theorem mono_δ_of_isZero (n : Nat) (h : IsZero (groupHomology X.X₂ (n + 1))) :
    Mono (δ hX (n + 1) n rfl) := SnakeInput.mono_δ _ h

/--
theorem `isIso_δ_of_isZero` / 定理 `isIso_δ_of_isZero`

English:
theorem isIso_δ_of_isZero
  statement: (n : Nat) (hs : IsZero (groupHomology X.X₂ (n + 1)))
  proof: SnakeInput.isIso_δ _ hs h

中文:
定理 isIso_δ_of_isZero
  结论: (n : 自然数) (hs : 是零 (groupHomology X.X₂ (n + 1)))
  证明: SnakeInput.isIso_δ _ hs h

Depends on / 依赖: SnakeInput, SnakeInput.isIso_
-/
theorem isIso_δ_of_isZero (n : Nat) (hs : IsZero (groupHomology X.X₂ (n + 1)))
    (h : IsZero (groupHomology X.X₂ n)) :
    IsIso (δ hX (n + 1) n rfl) := SnakeInput.isIso_δ _ hs h

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cyclesMkOfCompEqD` / `cyclesMkOfCompEqD` 的定义

English:
abbreviation cyclesMkOfCompEqD
  signature: {i j : Nat} {y : (Fin i -> G) ->₀ X.X₂}
  body: cyclesMk j _ rfl x by
    simpa using! (map_chainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) _

中文:
缩写 cyclesMkOfCompEqD
  签名: {i j : 自然数} {y : (有限集 i -> G) ->₀ X.X₂}
  定义体: cyclesMk j _ rfl x by
    simpa using! (map_chainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) _

Depends on / 依赖: cyclesMk, d_eq_zero_of_f_eq_d_apply, map_chainsFunctor_shortExact
-/
noncomputable abbrev cyclesMkOfCompEqD {i j : Nat} {y : (Fin i -> G) ->₀ X.X₂}
    {x : (Fin j -> G) ->₀ X.X₁}
    (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChains X.X₂).d i j y) :
    cycles X.X₁ j :=
cyclesMk j _ rfl x by
    simpa using! (map_chainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `δ_apply` / 定理 `δ_apply`

English:
theorem δ_apply
  statement: {i j : Nat} (hij : j + 1 = i)
  proof: by
  exact (map_chainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x (by simpa using! hx) _ rfl

中文:
定理 δ_apply
  结论: {i j : 自然数} (hij : j + 1 = i)
  证明: by
  exact (map_chainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x (by simpa using! hx) _ rfl

Depends on / 依赖: map_chainsFunctor_shortExact
-/
theorem δ_apply {i j : Nat} (hij : j + 1 = i)
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be an `j + 1`-cycle for `X₃`
    (z : (Fin i -> G) ->₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    -- Let `y` be an `j + 1`-chain for `X₂` such that `g ∘ y = z`
    (y : (Fin i -> G) ->₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    -- Let `x` be an `j`-chain for `X₁` such that `f ∘ x = d(y)`
    (x : (Fin j -> G) ->₀ X.X₁)
    -- Then `x` is an `j`-cycle and `δ z = x` in `Hⱼ(X₁)`.
    (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChains X.X₂).d i j y) :
    δ hX i j hij (π X.X₃ i <| cyclesMk i j (by simp [← hij]) z (by simpa using! hz)) =
      π X.X₁ j (cyclesMkOfCompEqD hX hx) := by
  exact (map_chainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x (by simpa using! hx) _ rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `δ₀_apply` / 定理 `δ₀_apply`

English:
theorem δ₀_apply
  proof: by
  simpa only [H1π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H0π,
    ← cyclesMk₀_eq X.X₁, ← cyclesMk₁_eq X.X₃]
  using! δ_apply hX (i := 1) (j := 0) rfl ((chainsIso₁ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₀_comp_inv]; simp)
    

中文:
定理 δ₀_apply
  证明: by
  simpa only [H1π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H0π,
    ← cyclesMk₀_eq X.X₁, ← cyclesMk₁_eq X.X₃]
  using! δ_apply hX (i := 1) (j := 0) rfl ((chainsIso₁ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₀_comp_inv]; simp)
    

Depends on / 依赖: Finsupp, Finsupp.ext, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.comp_apply, ModuleCat, ModuleCat.hom_comp, coe_comp, comp_apply, conv_rhs, hom_comp
-/
theorem δ₀_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` by a 1-cycle for `X₃` and `y` a 1-chain for `X₂` such that `g ∘ y = z`.
    (z : cycles₁ X.X₃) (y : G ->₀ X.X₂) (hy : mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    -- Let `x : X₁` be such that `f(x) = d(y)`.
    (x : X.X₁) (hx : X.f.hom x = d₁₀ X.X₂ y) :
    -- Then `δ z = x` in `H₀(X₁)`.
    δ hX 1 0 rfl (H1π X.X₃ z) = H0π X.X₁ x := by
  simpa only [H1π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H0π,
    ← cyclesMk₀_eq X.X₁, ← cyclesMk₁_eq X.X₃]
  using! δ_apply hX (i := 1) (j := 0) rfl ((chainsIso₁ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₀_comp_inv]; simp)
    ((chainsIso₁ X.X₂).inv y) (Finsupp.ext fun _ => by simp [chainsIso₁, ← hy])
    ((chainsIso₀ X.X₁).inv x) (Finsupp.ext fun _ => by
      conv_rhs => rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₁₀_comp_inv]
      simp [chainsIso₀, ← hx])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_cycles₁_of_comp_eq_d₂₁` / 定理 `mem_cycles₁_of_comp_eq_d₂₁`

English:
theorem mem_cycles₁_of_comp_eq_d₂₁
  proof: LinearMap.mem_ker.2 (Rep.mono_iff_injective X.f).1 hX.2 by
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1]

中文:
定理 mem_cycles₁_of_comp_eq_d₂₁
  证明: LinearMap.mem_ker.2 (Rep.mono_iff_injective X.f).1 hX.2 by
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, MonoidHom, MonoidHom.id, Rep.mono_iff_injective, mapShortComplexH1, mem_ker, mono_iff_injective, shortComplexH1
-/
theorem mem_cycles₁_of_comp_eq_d₂₁
    {y : G × G ->₀ X.X₂} {x : G ->₀ X.X₁} (hx : mapRange.linearMap X.f.hom.toLinearMap x =
    d₂₁ X.X₂ y) :
x in cycles₁ X.X₁ := LinearMap.mem_ker.2 (Rep.mono_iff_injective X.f).1 hX.2 by
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `δ₁_apply` / 定理 `δ₁_apply`

English:
theorem δ₁_apply
  proof: by
  simpa only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H1π,
    ← cyclesMk₂_eq X.X₃, ← cyclesMk₁_eq X.X₁]
  using! δ_apply hX (i := 2) (j := 1) rfl ((chainsIso₂ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₂₁_comp_inv]; simp)
    

中文:
定理 δ₁_apply
  证明: by
  simpa only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H1π,
    ← cyclesMk₂_eq X.X₃, ← cyclesMk₁_eq X.X₁]
  using! δ_apply hX (i := 2) (j := 1) rfl ((chainsIso₂ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₂₁_comp_inv]; simp)
    

Depends on / 依赖: Finsupp, Finsupp.ext, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.comp_apply, ModuleCat, ModuleCat.hom_comp, coe_comp, comp_apply, conv_rhs, hom_comp
-/
theorem δ₁_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` by a 2-cycle for `X₃` and `y` a 2-chain for `X₂` such that `g ∘ y = z`.
    (z : cycles₂ X.X₃) (y : G × G ->₀ X.X₂) (hy : mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    -- Let `x` be a 1-chain for `X₁` such that `f ∘ x = d(y)`.
    (x : G ->₀ X.X₁) (hx : mapRange.linearMap X.f.hom.toLinearMap x = d₂₁ X.X₂ y) :
    -- Then `x` is a 1-cycle and `δ z = x` in `H₁(X₁)`.
    δ hX 2 1 rfl (H2π X.X₃ z) = H1π X.X₁ ⟨x, mem_cycles₁_of_comp_eq_d₂₁ hX hx⟩ := by
  simpa only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H1π,
    ← cyclesMk₂_eq X.X₃, ← cyclesMk₁_eq X.X₁]
  using! δ_apply hX (i := 2) (j := 1) rfl ((chainsIso₂ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₂₁_comp_inv]; simp)
    ((chainsIso₂ X.X₂).inv y) (Finsupp.ext fun _ => by simp [chainsIso₂, ← hy])
    ((chainsIso₁ X.X₁).inv x) (Finsupp.ext fun _ => by
    conv_rhs => rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₂₁_comp_inv]
    simp [← hx, chainsIso₁])

/--
lemma `map_chainsFunctor_eval_shortExact` / 引理 `map_chainsFunctor_eval_shortExact`

English:
lemma map_chainsFunctor_eval_shortExact
  given: (n : Nat)
  proof: (map_chainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

中文:
引理 map_chainsFunctor_eval_shortExact
  条件: (n : 自然数)
  证明: (map_chainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, map_chainsFunctor_shortExact, map_of_exact
-/
lemma map_chainsFunctor_eval_shortExact (n : Nat) :
    ShortExact (X.map <| chainsFunctor k G ⋙ HomologicalComplex.eval (ModuleCat k) (.down Nat) n) :=
  (map_chainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

end groupHomology
