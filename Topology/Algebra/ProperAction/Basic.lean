/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocalAtTarget

/-!
# Proper group action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense of `IsProperMap`.

## Main statements

* `t2Space_quotient_mulAction_of_properSMul`: If a group `G` acts properly
  on a topological space `X`, then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t1Group`: If a T1 group acts properly on a topological space,
  then this topological space is T2.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

Hausdorff, group action, proper action
-/

public section

open Filter Topology Set Prod

/--
Definition of `ProperVAdd` / `ProperVAdd` 的定义

English:
class ProperVAdd
  parameters: (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
  axioms and operations (1):
    - isProperMap_vadd_pair : IsProperMap (fun gx => (gx.1 +ᵥ gx.2, gx.2) : G × X -> X × X)

中文:
类 ProperVAdd
  参数: (G X : 类型) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
  公理与运算 (1 个):
    - isProperMap_vadd_pair : Is命题erMap (fun gx => (gx.1 +ᵥ gx.2, gx.2) : G × X -> X × X)
-/
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_vadd_pair : IsProperMap (fun gx => (gx.1 +ᵥ gx.2, gx.2) : G × X -> X × X)

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
@[to_additive existing (attr := mk_iff)]
/--
Definition of `ProperSMul` / `ProperSMul` 的定义

English:
class ProperSMul
  parameters: (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
  axioms and operations (1):
    - isProperMap_smul_pair : IsProperMap (fun gx => (gx.1 • gx.2, gx.2) : G × X -> X × X)

中文:
类 ProperSMul
  参数: (G X : 类型) [TopologicalSpace G] [TopologicalSpace X] [Group G]
  公理与运算 (1 个):
    - isProperMap_smul_pair : Is命题erMap (fun gx => (gx.1 • gx.2, gx.2) : G × X -> X × X)
-/
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_smul_pair : IsProperMap (fun gx => (gx.1 • gx.2, gx.2) : G × X -> X × X)

attribute [to_additive existing] properSMul_iff

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]

/-- If a group acts properly then in particular it acts continuously. -/
@[to_additive /-- If a group acts properly then in particular it acts continuously. -/]
-- See note [lower instance property]
instance (priority := 100) ProperSMul.toContinuousSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := isProperMap_smul_pair.continuous.fst

/-- A group `G` acts properly on a topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive /-- An additive group `G` acts properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`. -/]
/--
theorem `properSMul_iff_continuousSMul_ultrafilter_tendsto` / 定理 `properSMul_iff_continuousSMul_ultrafilter_tendsto`

English:
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto
  proof: by
  refine ⟨fun h => ⟨inferInstance, fun 𝒰 x₁ x₂ h' => ?_⟩, fun ⟨cont, h⟩ => ?_⟩
  · rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2

中文:
定理 properSMul_iff_continuousSMul_ultrafilter_tendsto
  证明: by
  refine ⟨fun h => ⟨inferInstance, fun 𝒰 x₁ x₂ h' => ?_⟩, fun ⟨cont, h⟩ => ?_⟩
  · rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2

Depends on / 依赖: Prod.mk.injEq, continuous_fst, continuous_fst.tendsto, fun_prop, isProperMap_iff_ultrafilter, mono_left, nhds_prod_eq, properSMul_iff, simp_rw, tendsto
-/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (forall 𝒰 : Ultrafilter (G × X), forall x₁ x₂ : X,
        Tendsto (fun gx : G × X => (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) ->
        exists g : G, g • x₂ = x₁ ∧ Tendsto (Prod.fst : G × X -> G) 𝒰 (𝓝 g)) := by
  refine ⟨fun h => ⟨inferInstance, fun 𝒰 x₁ x₂ h' => ?_⟩, fun ⟨cont, h⟩ => ?_⟩
  · rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2]; rw [hgx1.1]
  · rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx => ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine ⟨(g, x₂), by simp_rw [hg1], ?_⟩
    rw [nhds_prod_eq]; rw [𝒰.le_prod]
    exact ⟨hg2, (continuous_snd.tendsto _).comp hxx⟩

/--
theorem `properSMul_iff_continuousSMul_ultrafilter_tendsto_t2` / 定理 `properSMul_iff_continuousSMul_ultrafilter_tendsto_t2`

English:
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2
  given: [T2Space X]
  proof: by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc => ?_
  congrm forall 𝒰 x₁ x₂ hxx, exists g, ?_
  exact and_iff_right_of_imp fun hg => tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

中文:
定理 properSMul_iff_continuousSMul_ultrafilter_tendsto_t2
  条件: [T2Space X]
  证明: by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc => ?_
  congrm forall 𝒰 x₁ x₂ hxx, exists g, ?_
  exact and_iff_right_of_imp fun hg => tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

Depends on / 依赖: and_congr_right, and_iff_right_of_imp, congrm, continuous_fst, continuous_fst.tendsto, continuous_snd, continuous_snd.tendsto, hg.smul, properSMul_iff_continuousSMul_ultrafilter_tendsto, tendsto, tendsto_nhds_unique
-/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (forall 𝒰 : Ultrafilter (G × X), forall x₁ x₂ : X,
        Tendsto (fun gx : G × X => (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) ->
        exists g : G, Tendsto (Prod.fst : G × X -> G) 𝒰 (𝓝 g)) := by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc => ?_
  congrm forall 𝒰 x₁ x₂ hxx, exists g, ?_
  exact and_iff_right_of_imp fun hg => tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

/-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/
@[to_additive /-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/]
/--
Instance `t2Space_quotient_mulAction_of_properSMul` / 实例 `t2Space_quotient_mulAction_of_properSMul`

English:
instance t2Space_quotient_mulAction_of_properSMul
  signature: [ProperSMul G X]
  body: by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X -> Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  conver

中文:
实例 t2Space_quotient_mulAction_of_properSMul
  签名: [命题erSMul G X]
  定义体: by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X -> Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  conver

Depends on / 依赖: IsOpenQuotientMap, MulAction, MulAction.isOpenQuotientMap_quotientMk, MulAction.isOpenQuotientMap_quotientMk.prodMap, MulAction.orbitRel, Prod.exists, Prod.map, Prod.mk.injEq, ProperSMul, ProperSMul.isProperMap_smul_pair.isClosedMap.isClosed_range, Quotient, Quotient.eq, Quotient.mk, convert, exists_eq_right, isClosedMap, isClosed_preimage, isClosed_range, isOpenQuotientMap_quotientMk, isProperMap_smul_pair
-/
instance t2Space_quotient_mulAction_of_properSMul [ProperSMul G X] :
    T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X -> Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  convert! ProperSMul.isProperMap_smul_pair.isClosedMap.isClosed_range
  · ext ⟨x₁, x₂⟩
    simp only [mem_preimage, map_apply, mem_diagonal_iff, mem_range, Prod.mk.injEq, Prod.exists,
      exists_eq_right]
    rw [Quotient.eq']; rw [MulAction.orbitRel_apply]; rw [MulAction.mem_orbit_iff]
  all_goals infer_instance

/-- If a T1 group acts properly on a topological space, then this topological space is T2. -/
@[to_additive /-- If a T1 group acts properly on a topological space,
then this topological space is T2. -/]
/--
theorem `t2Space_of_properSMul_of_t1Group` / 定理 `t2Space_of_properSMul_of_t1Group`

English:
theorem t2Space_of_properSMul_of_t1Group
  given: [h_proper : ProperSMul G X] [T1Space G]
  statement: T2Space X
  proof: by
  let f := fun x : X => ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight 1, ?_⟩
    have : range f = ({1} ×ˢ univ) := by simp [f, Set.singleton_prod]
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isCl

中文:
定理 t2Space_of_properSMul_of_t1Group
  条件: [h_proper : 命题erSMul G X] [T1Space G]
  结论: T2Space X
  证明: by
  let f := fun x : X => ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight 1, ?_⟩
    have : range f = ({1} ×ˢ univ) := by simp [f, Set.singleton_prod]
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isCl

Depends on / 依赖: Function, Function.diag, IsClosedEmbedding, IsClosedEmbedding.isProperMap, IsProperMap, Set.singleton_prod, diagon, h_proper, isClosed_singleton, isClosed_singleton.prod, isClosed_univ, isEmbedding_prodMkRight, isProperMap, properSMul_iff, proper_f, proper_g, range_gf, singleton_prod, t2_iff_isClosed_diagonal
-/
theorem t2Space_of_properSMul_of_t1Group [h_proper : ProperSMul G X] [T1Space G] : T2Space X := by
  let f := fun x : X => ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight 1, ?_⟩
    have : range f = ({1} ×ˢ univ) := by simp [f, Set.singleton_prod]
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X => (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = Function.diag := by ext x <;> simp [f, g]
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_g.comp proper_f).isClosed_range

/-- If two groups `H` and `G` act on a topological space `X` such that `G` acts properly and
there exists a group homomorphism `H → G` which is a closed embedding compatible with the actions,
then `H` also acts properly on `X`. -/
@[to_additive /-- If two groups `H` and `G` act on a topological space `X` such that `G` acts
properly and there exists a group homomorphism `H → G` which is a closed embedding compatible with
the actions, then `H` also acts properly on `X`. -/]
/--
theorem `properSMul_of_isClosedEmbedding` / 定理 `properSMul_of_isClosedEmbedding`

English:
theorem properSMul_of_isClosedEmbedding
  statement: {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
  proof: by
    have h : IsProperMap (Prod.map f (fun x : X => x)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : (fun hx : H × X => (hx.1 • hx.2, hx.2)) = (fun hx => (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact ProperSMul.isProperMap_smul_pair.comp h

中文:
定理 properSMul_of_isClosedEmbedding
  结论: {H : 类型} [Group H] [MulAction H X] [TopologicalSpace H]
  证明: by
    have h : IsProperMap (Prod.map f (fun x : X => x)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : (fun hx : H × X => (hx.1 • hx.2, hx.2)) = (fun hx => (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact ProperSMul.isProperMap_smul_pair.comp h

Depends on / 依赖: IsProperMap, Prod.map, ProperSMul, ProperSMul.isProperMap_smul_pair.comp, f_clemb, f_clemb.isProperMap.prodMap, f_compat, isProperMap, isProperMap_id, isProperMap_smul_pair, prodMap
-/
theorem properSMul_of_isClosedEmbedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H ->* G) (f_clemb : IsClosedEmbedding f)
    (f_compat : forall (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair := by
    have h : IsProperMap (Prod.map f (fun x : X => x)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : (fun hx : H × X => (hx.1 • hx.2, hx.2)) = (fun hx => (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact ProperSMul.isProperMap_smul_pair.comp h

/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/
@[to_additive
/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_isClosedEmbedding H.subtype H_closed.isClosedEmbedding_subtypeVal fun _ _ => rfl

/-- The action `G ↷ G` by left translations is proper. -/
@[to_additive
/-- The action `G ↷ G` by left translations is proper. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalGroup
  signature: G] : ProperSMul G G where
  body: by
    let Φ : G × G ≃ₜ G × G :=
    { toFun := fun gh => (gh.1 * gh.2, gh.2)
      invFun := fun gh => (gh.1 * gh.2⁻¹, gh.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
    exact Φ.isProperMap

中文:
实例 [IsTopologicalGroup
  签名: G] : 命题erSMul G G where
  定义体: by
    let Φ : G × G ≃ₜ G × G :=
    { toFun := fun gh => (gh.1 * gh.2, gh.2)
      invFun := fun gh => (gh.1 * gh.2⁻¹, gh.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
    exact Φ.isProperMap

Depends on / 依赖: invFun, isProperMap, left_inv, right_inv
-/
instance [IsTopologicalGroup G] : ProperSMul G G where
  isProperMap_smul_pair := by
    let Φ : G × G ≃ₜ G × G :=
    { toFun := fun gh => (gh.1 * gh.2, gh.2)
      invFun := fun gh => (gh.1 * gh.2⁻¹, gh.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
    exact Φ.isProperMap

open MulOpposite in
/-- The action `Gᵐᵒᵖ ↷ G` by right translations is proper. -/
@[to_additive
/-- The action `Gᵃᵒᵖ ↷ G` by right translations is proper. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalGroup
  signature: G] : ProperSMul Gᵐᵒᵖ G where
  body: by
    let Φ : Gᵐᵒᵖ × G ≃ₜ G × G :=
    { toFun := fun gh => (gh.2 * (unop gh.1), gh.2)
      invFun := fun gh => (op (gh.2⁻¹ * gh.1), gh.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
    exact Φ.isProperMap

中文:
实例 [IsTopologicalGroup
  签名: G] : 命题erSMul Gᵐᵒᵖ G where
  定义体: by
    let Φ : Gᵐᵒᵖ × G ≃ₜ G × G :=
    { toFun := fun gh => (gh.2 * (unop gh.1), gh.2)
      invFun := fun gh => (op (gh.2⁻¹ * gh.1), gh.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
    exact Φ.isProperMap

Depends on / 依赖: invFun, isProperMap, left_inv, right_inv
-/
instance [IsTopologicalGroup G] : ProperSMul Gᵐᵒᵖ G where
  isProperMap_smul_pair := by
    let Φ : Gᵐᵒᵖ × G ≃ₜ G × G :=
    { toFun := fun gh => (gh.2 * (unop gh.1), gh.2)
      invFun := fun gh => (op (gh.2⁻¹ * gh.1), gh.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
    exact Φ.isProperMap

/-- Given a closed subgroup `H` of a topological group `G`, the right action of `H` on `G`
is proper. Note that the corresponding statement for the left action can be proven by
`inferInstance`. -/
@[to_additive /-- Given a closed subgroup `H` of an additive topological group `G`, the right
action of `H` on `G` is proper. Note that the corresponding statement for the left action can be
proven by `inferInstance`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalGroup
  signature: G] {H
  body: have : IsClosed (H.op : Set Gᵐᵒᵖ) := H_closed.preimage MulOpposite.continuous_unop
  inferInstance

@[to_additive]

中文:
实例 [IsTopologicalGroup
  签名: G] {H
  定义体: have : IsClosed (H.op : Set Gᵐᵒᵖ) := H_closed.preimage MulOpposite.continuous_unop
  inferInstance

@[to_additive]

Depends on / 依赖: H.op, H_closed, H_closed.preimage, IsClosed, MulOpposite, MulOpposite.continuous_unop, continuous_unop, preimage
-/
instance [IsTopologicalGroup G] {H : Subgroup G} [H_closed : IsClosed (H : Set G)] :
    ProperSMul H.op G :=
  have : IsClosed (H.op : Set Gᵐᵒᵖ) := H_closed.preimage MulOpposite.continuous_unop
  inferInstance

@[to_additive]
/--
Instance `QuotientGroup.instT2Space` / 实例 `QuotientGroup.instT2Space`

English:
instance QuotientGroup.instT2Space
  signature: [IsTopologicalGroup G] {H : Subgroup G} [IsClosed (H : Set G)]
  body: t2Space_quotient_mulAction_of_properSMul

中文:
实例 QuotientGroup.instT2Space
  签名: [IsTopologicalGroup G] {H : Subgroup G} [IsClosed (H : Set G)]
  定义体: t2Space_quotient_mulAction_of_properSMul

Depends on / 依赖: t2Space_quotient_mulAction_of_properSMul
-/
instance QuotientGroup.instT2Space [IsTopologicalGroup G] {H : Subgroup G} [IsClosed (H : Set G)] :
    T2Space (G ⧸ H) :=
  t2Space_quotient_mulAction_of_properSMul

/-- If `G` acts on `X` properly, then the map `G × T → X × T, (g, t) ↦ (g • t, t)` is still
proper for *any* subset `T` of `X`. -/
@[to_additive
/-- If `G` acts on `X` properly, then the map `G × T → X × T, (g, t) ↦ (g +ᵥ t, t)` is still
proper for *any* subset `T` of `X`. -/]
/--
lemma `ProperSMul.isProperMap_smul_pair_set` / 引理 `ProperSMul.isProperMap_smul_pair_set`

English:
lemma ProperSMul.isProperMap_smul_pair_set
  given: [ProperSMul G X] {t : Set X}
  proof: by
  let Φ : G × X -> X × X := fun gx => (gx.1 • gx.2, gx.2)
  have Φ_proper : IsProperMap Φ := ProperSMul.isProperMap_smul_pair
  let α : G × t ≃ₜ (Φ ⁻¹' snd ⁻¹' t) :=
    have : univ ×ˢ t = Φ ⁻¹' snd ⁻¹' t := by ext; simp [Φ]
.trans .symm.prodCongr (.refl t) Homeomorph.Set.univ G
.trans (Homeomorp

中文:
引理 ProperSMul.isProperMap_smul_pair_set
  条件: [命题erSMul G X] {t : Set X}
  证明: by
  let Φ : G × X -> X × X := fun gx => (gx.1 • gx.2, gx.2)
  have Φ_proper : IsProperMap Φ := ProperSMul.isProperMap_smul_pair
  let α : G × t ≃ₜ (Φ ⁻¹' snd ⁻¹' t) :=
    have : univ ×ˢ t = Φ ⁻¹' snd ⁻¹' t := by ext; simp [Φ]
.trans .symm.prodCongr (.refl t) Homeomorph.Set.univ G
.trans (Homeomorp

Depends on / 依赖: Homeomorph, Homeomorph.Set.prod, Homeomorph.Set.univ, Homeomorph.setCongr, IsProperMap, ProperSMul, ProperSMul.isProperMap_smul_pair, isProperMap_smul_pair, prodCongr, setCongr, symm.prodCongr, univ_prod
-/
lemma ProperSMul.isProperMap_smul_pair_set [ProperSMul G X] {t : Set X} :
    IsProperMap (fun (gx : G × t) => ((gx.1 • gx.2, gx.2) : X × t)) := by
  let Φ : G × X -> X × X := fun gx => (gx.1 • gx.2, gx.2)
  have Φ_proper : IsProperMap Φ := ProperSMul.isProperMap_smul_pair
  let α : G × t ≃ₜ (Φ ⁻¹' snd ⁻¹' t) :=
    have : univ ×ˢ t = Φ ⁻¹' snd ⁻¹' t := by ext; simp [Φ]
.trans .symm.prodCongr (.refl t) Homeomorph.Set.univ G
.trans (Homeomorph.setCongr this) ((Homeomorph.Set.prod _ t).symm)
  let β : X × t ≃ₜ (snd ⁻¹' t) :=
.trans .symm.prodCongr (.refl t) Homeomorph.Set.univ X
.trans (Homeomorph.setCongr univ_prod) ((Homeomorph.Set.prod _ t).symm)
.comp α.isProperMap exact β.symm.isProperMap.comp (Φ_proper.restrictPreimage (snd ⁻¹' t))

open scoped Pointwise in
/-- If `G` acts on `X` properly, the set `s • t` is closed when `s : Set G` is *closed* and
`t : Set X` is *compact*.

See also `IsClosed.smul_left_of_isCompact` for a version with the assumptions on `s` and `t`
reversed. -/
@[to_additive
/-- If `G` acts on `X` properly, the set `s +ᵥ t` is closed when `s : Set G` is *closed* and
`t : Set X` is *compact*. In particular, this applies when the action comes from an
`IsTopologicalAddTorsor`.

See also `IsClosed.vadd_left_of_isCompact` for a version with the assumptions on `s` and `t`
reversed. -/]
/--
theorem `IsClosed.smul_right_of_isCompact` / 定理 `IsClosed.smul_right_of_isCompact`

English:
theorem IsClosed.smul_right_of_isCompact
  statement: [ProperSMul G X] {s : Set G} {t : Set X} (hs : IsClosed s)
  proof: by
  let Ψ : G × t -> X × t := fun gx => (gx.1 • gx.2, gx.2)
  have Ψ_proper : IsProperMap Ψ := ProperSMul.isProperMap_smul_pair_set
  have : s • t = (fst ∘ Ψ) '' fst ⁻¹' s :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx => mem_image_of_mem (fst ∘ Ψ) (x := ⟨g, ⟨x, hx⟩⟩) hg)
      (im

中文:
定理 IsClosed.smul_right_of_isCompact
  结论: [命题erSMul G X] {s : Set G} {t : Set X} (hs : IsClosed s)
  证明: by
  let Ψ : G × t -> X × t := fun gx => (gx.1 • gx.2, gx.2)
  have Ψ_proper : IsProperMap Ψ := ProperSMul.isProperMap_smul_pair_set
  have : s • t = (fst ∘ Ψ) '' fst ⁻¹' s :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx => mem_image_of_mem (fst ∘ Ψ) (x := ⟨g, ⟨x, hx⟩⟩) hg)
      (im

Depends on / 依赖: CompactSpace, IsProperMap, ProperSMul, ProperSMul.isProperMap_smul_pair_set, continuous, hs.preimage, image_subset_iff, image_subset_iff.mpr, isClosedMap, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isProperMap_fst_of_compactSpace, isProperMap_fst_of_compactSpace.comp, isProperMap_smul_pair_set, mem_image_of_mem, preimage, smul_mem_smul, smul_subset_iff, smul_subset_iff.mpr, subset_antisymm
-/
theorem IsClosed.smul_right_of_isCompact [ProperSMul G X] {s : Set G} {t : Set X} (hs : IsClosed s)
    (ht : IsCompact t) : IsClosed (s • t) := by
  let Ψ : G × t -> X × t := fun gx => (gx.1 • gx.2, gx.2)
  have Ψ_proper : IsProperMap Ψ := ProperSMul.isProperMap_smul_pair_set
  have : s • t = (fst ∘ Ψ) '' fst ⁻¹' s :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx => mem_image_of_mem (fst ∘ Ψ) (x := ⟨g, ⟨x, hx⟩⟩) hg)
      (image_subset_iff.mpr fun ⟨g, ⟨x, hx⟩⟩ hg => smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace t := isCompact_iff_compactSpace.mp ht
  exact (isProperMap_fst_of_compactSpace.comp Ψ_proper).isClosedMap _ (hs.preimage continuous_fst)

/-! One may expect `IsClosed.smul_right_of_isCompact` to hold for arbitrary continuous actions,
but such a lemma can't be true in this level of generality. For a counterexample, consider
`ℚ` acting on `ℝ` by translation, and let `s : Set ℚ := univ`, `t : set ℝ := {0}`. Then `s` is
closed and `t` is compact, but `s +ᵥ t` is the set of all rationals, which is definitely not
closed in `ℝ`. -/

open scoped Pointwise in
/-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `g • U` intersects `V` is compact.

See `MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/
@[to_additive /-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `g +ᵥ U` intersects `V` is compact.

See `AddAction.properVAdd_iff_isCompact_setOfPred_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/]
/--
lemma `ProperSMul.isCompact_setOfPred_inter_nonempty` / 引理 `ProperSMul.isCompact_setOfPred_inter_nonempty`

English:
lemma ProperSMul.isCompact_setOfPred_inter_nonempty
  proof: by
  convert!
    ((ProperSMul.isProperMap_smul_pair (G := G)).isCompact_preimage (hV.prod hU)).image
      continuous_fst
  ext g
  suffices (exists v, v in g • U ∧ v in V) ↔ exists u, g • u in V ∧ u in U by simpa
  rw [← (MulAction.toPerm g).exists_congr_right]
  simp [and_comm]

@[deprecated (sin

中文:
引理 ProperSMul.isCompact_setOfPred_inter_nonempty
  证明: by
  convert!
    ((ProperSMul.isProperMap_smul_pair (G := G)).isCompact_preimage (hV.prod hU)).image
      continuous_fst
  ext g
  suffices (exists v, v in g • U ∧ v in V) ↔ exists u, g • u in V ∧ u in U by simpa
  rw [← (MulAction.toPerm g).exists_congr_right]
  simp [and_comm]

@[deprecated (sin

Depends on / 依赖: MulAction, MulAction.toPerm, ProperSMul, ProperSMul.isProperMap_smul_pair, and_comm, continuous_fst, convert, exists_congr_right, hV.prod, isCompact_preimage, isProperMap_smul_pair, toPerm
-/
lemma ProperSMul.isCompact_setOfPred_inter_nonempty
    {G : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [ProperSMul G X]
    {U V : Set X} (hU : IsCompact U) (hV : IsCompact V) :
    IsCompact {g : G | (g • U inter V).Nonempty} := by
  convert!
    ((ProperSMul.isProperMap_smul_pair (G := G)).isCompact_preimage (hV.prod hU)).image
      continuous_fst
  ext g
  suffices (exists v, v in g • U ∧ v in V) ↔ exists u, g • u in V ∧ u in U by simpa
  rw [← (MulAction.toPerm g).exists_congr_right]
  simp [and_comm]

@[deprecated (since := "2026-07-09")]
alias ProperSMul.isCompact_setOf_inter_nonempty := ProperSMul.isCompact_setOfPred_inter_nonempty

@[deprecated (since := "2026-07-09")]
alias ProperVAdd.isCompact_setOf_inter_nonempty := ProperVAdd.isCompact_setOfPred_inter_nonempty

/-- If `G` acts transitively on `X`, and the orbit map of a point in `X` is a proper map, then the
action is proper. -/
@[to_additive]
/--
lemma `MulAction.properSMul_of_proper_orbitMap` / 引理 `MulAction.properSMul_of_proper_orbitMap`

English:
lemma MulAction.properSMul_of_proper_orbitMap
  proof: by
  constructor
  let f : G × G -> G × X := Prod.map id (fun g => g • x)
  have hfsurj : f.Surjective := Function.surjective_id.prodMap (surjective_smul G x)
  refine isProperMap_of_comp_of_surj (by fun_prop) (by fun_prop) ?_ hfsurj
  simpa [Function.comp_def, Prod.map_apply, mul_smul]
    using! (

中文:
引理 MulAction.properSMul_of_proper_orbitMap
  证明: by
  constructor
  let f : G × G -> G × X := Prod.map id (fun g => g • x)
  have hfsurj : f.Surjective := Function.surjective_id.prodMap (surjective_smul G x)
  refine isProperMap_of_comp_of_surj (by fun_prop) (by fun_prop) ?_ hfsurj
  simpa [Function.comp_def, Prod.map_apply, mul_smul]
    using! (

Depends on / 依赖: Function, Function.comp_def, Function.surjective_id.prodMap, Prod.map, Prod.map_apply, ProperSMul, ProperSMul.isProperMap_smul_pair, Surjective, comp_def, f.Surjective, fun_prop, hfsurj, hx.prodMap, isProperMap_of_comp_of_surj, isProperMap_smul_pair, map_apply, mul_smul, prodMap, surjective_id, surjective_smul
-/
lemma MulAction.properSMul_of_proper_orbitMap
    [ContinuousSMul G X] [IsTopologicalGroup G] [MulAction.IsPretransitive G X]
    {x : X} (hx : IsProperMap fun g : G => g • x) : ProperSMul G X := by
  constructor
  let f : G × G -> G × X := Prod.map id (fun g => g • x)
  have hfsurj : f.Surjective := Function.surjective_id.prodMap (surjective_smul G x)
  refine isProperMap_of_comp_of_surj (by fun_prop) (by fun_prop) ?_ hfsurj
  simpa [Function.comp_def, Prod.map_apply, mul_smul]
    using! (hx.prodMap hx).comp (ProperSMul.isProperMap_smul_pair (G := G))

end
