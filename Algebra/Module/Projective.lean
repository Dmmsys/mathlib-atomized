/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Antoine Labelle
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Logic.UnivLE

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `Module.Projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `Module.projective_lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `Module.Projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `Module.Projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## Tags

projective module

-/

@[expose] public section

universe w v u

open LinearMap hiding id
open DirectSum hiding id_apply
open Finsupp

/- The actual implementation we choose: `P` is projective if the natural surjection
from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
if maps from the module lift along surjections. There are several other equivalent
definitions. -/
@[wikidata Q942423]
/--
Definition of `Module.Projective` / `Module.Projective` 的定义

English:
class Module.Projective
  parameters: (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P] [Module R P]
  axioms and operations (1):
    - out : exists s : P ->ₗ[R] P ->₀ R, Function.LeftInverse (Finsupp.linearCombination R id) s

中文:
类 模.投射
  参数: (R : 类型) [半环 R] (P : 类型) [加法交换幺半群 P] [模 R P]
  公理与运算 (1 个):
    - out : 存在 s : P ->ₗ[R] P ->₀ R, 函数.左逆 (有限支撑.linearCombination R id) s
-/
class Module.Projective (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P] [Module R P] :
    Prop where
  out : exists s : P ->ₗ[R] P ->₀ R, Function.LeftInverse (Finsupp.linearCombination R id) s

namespace Module

section Semiring

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

/--
theorem `projective_def` / 定理 `projective_def`

English:
theorem projective_def
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 projective_def
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem projective_def :
    Projective R P ↔ exists s : P ->ₗ[R] P ->₀ R, Function.LeftInverse (linearCombination R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `projective_def'` / 定理 `projective_def'`

English:
theorem projective_def'
  proof: by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]

中文:
定理 projective_def'
  证明: by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Function, Function.LeftInverse, LeftInverse, comp_apply, ext_iff, id_apply, projective_def, simp_rw
-/
theorem projective_def' :
    Projective R P ↔ exists s : P ->ₗ[R] P ->₀ R, Finsupp.linearCombination R id ∘ₗ s = .id := by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]

/--
theorem `projective_lifting_property` / 定理 `projective_lifting_property`

English:
theorem projective_lifting_property
  statement: [h : Projective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N)
  proof: by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `Finsupp.linearCombination` says that to a map
    `X → N` from a type to an `R`-module, we get an associated R-module map
    `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
    `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
    a map `φ : (P →₀ R) →ₗ M`.
    -/
  let φ : (P ->₀ R) ->ₗ[R] M := Finsupp.linearCombination _ fun p => Function.surjInv hf (g p)
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  obtain ⟨s, hs⟩ := h.out
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.linearCombination_apply, Function.surjInv_eq hf, map_finsuppSum]

中文:
定理 projective_lifting_property
  结论: [h : 投射 R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N)
  证明: by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `Finsupp.linearCombination` says that to a map
    `X → N` from a type to an `R`-module, we get an associated R-module map
    `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
    `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
    a map `φ : (P →₀ R) →ₗ M`.
    -/
  let φ : (P ->₀ R) ->ₗ[R] M := Finsupp.linearCombination _ fun p => Function.surjInv hf (g p)
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  obtain ⟨s, hs⟩ := h.out
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.linearCombination_apply, Function.surjInv_eq hf, map_finsuppSum]
-/
theorem projective_lifting_property [h : Projective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N)
    (hf : Function.Surjective f) : exists h : P ->ₗ[R] M, f ∘ₗ h = g := by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `Finsupp.linearCombination` says that to a map
    `X → N` from a type to an `R`-module, we get an associated R-module map
    `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
    `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
    a map `φ : (P →₀ R) →ₗ M`.
    -/
  let φ : (P ->₀ R) ->ₗ[R] M := Finsupp.linearCombination _ fun p => Function.surjInv hf (g p)
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  obtain ⟨s, hs⟩ := h.out
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.linearCombination_apply, Function.surjInv_eq hf, map_finsuppSum]

/--
theorem `_root_.LinearMap.exists_rightInverse_of_surjective` / 定理 `_root_.LinearMap.exists_rightInverse_of_surjective`

English:
theorem _root_.LinearMap.exists_rightInverse_of_surjective
  statement: [Projective R P]
  proof: projective_lifting_property f (.id : P ->ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)

中文:
定理 _root_.线性映射.存在_rightInverse_of_surjective
  结论: [投射 R P]
  证明: projective_lifting_property f (.id : P ->ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, hf_surj, projective_lifting_property, range_eq_top
-/
theorem _root_.LinearMap.exists_rightInverse_of_surjective [Projective R P]
    (f : M ->ₗ[R] P) (hf_surj : range f = ⊤) : exists g : P ->ₗ[R] M, f ∘ₗ g = LinearMap.id :=
  projective_lifting_property f (.id : P ->ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)

open Function in
/--
theorem `_root_.Function.Surjective.surjective_linearMapComp_left` / 定理 `_root_.Function.Surjective.surjective_linearMapComp_left`

English:
theorem _root_.Function.Surjective.surjective_linearMapComp_left
  statement: [Projective R P]
  proof: surjective_comp_left_of_exists_rightInverse
f.exists_rightInverse_of_surjective range_eq_top_of_surjective f hf_surj

中文:
定理 _root_.函数.满射.surjective_linearMapComp_left
  结论: [投射 R P]
  证明: surjective_comp_left_of_exists_rightInverse
f.exists_rightInverse_of_surjective range_eq_top_of_surjective f hf_surj

Depends on / 依赖: exists_rightInverse_of_surjective, f.exists_rightInverse_of_surjective, hf_surj, range_eq_top_of_surjective, surjective_comp_left_of_exists_rightInverse
-/
theorem _root_.Function.Surjective.surjective_linearMapComp_left [Projective R P]
    {f : M ->ₗ[R] P} (hf_surj : Surjective f) : Surjective (fun g : N ->ₗ[R] M => f.comp g) :=
surjective_comp_left_of_exists_rightInverse
f.exists_rightInverse_of_surjective range_eq_top_of_surjective f hf_surj

/--
theorem `Projective.of_lifting_property''` / 定理 `Projective.of_lifting_property''`

English:
theorem Projective.of_lifting_property''
  statement: {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
  proof: projective_def'.2 huniv (Finsupp.linearCombination R (id : P -> P))
    (linearCombination_surjective _ Function.surjective_id)

中文:
定理 投射.of_lifting_property''
  结论: {R : 类型u} [半环 R] {P : 类型v} [加法交换幺半群 P]
  证明: projective_def'.2 huniv (Finsupp.linearCombination R (id : P -> P))
    (linearCombination_surjective _ Function.surjective_id)

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Function, Function.surjective_id, linearCombination, linearCombination_surjective, projective_def, surjective_id
-/
theorem Projective.of_lifting_property'' {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
    [Module R P] (huniv : forall (f : (P ->₀ R) ->ₗ[R] P), Function.Surjective f ->
      exists h : P ->ₗ[R] (P ->₀ R), f.comp h = .id) :
    Projective R P :=
projective_def'.2 huniv (Finsupp.linearCombination R (id : P -> P))
    (linearCombination_surjective _ Function.surjective_id)

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Projective
  signature: R P] [Projective R Q] : Projective R (P × Q)
  body: by
  refine .of_lifting_property'' fun f hf => ?_
  rcases projective_lifting_property f (.inl _ _ _) hf with ⟨g₁, hg₁⟩
  rcases projective_lifting_property f (.inr _ _ _) hf with ⟨g₂, hg₂⟩
  refine ⟨coprod g₁ g₂, ?_⟩
  rw [LinearMap.comp_coprod]; rw [hg₁]; rw [hg₂]; rw [LinearMap.coprod_inl_inr]

中文:
实例 [投射
  签名: R P] [投射 R Q] : 投射 R (P × Q)
  定义体: by
  refine .of_lifting_property'' fun f hf => ?_
  rcases projective_lifting_property f (.inl _ _ _) hf with ⟨g₁, hg₁⟩
  rcases projective_lifting_property f (.inr _ _ _) hf with ⟨g₂, hg₂⟩
  refine ⟨coprod g₁ g₂, ?_⟩
  rw [LinearMap.comp_coprod]; rw [hg₁]; rw [hg₂]; rw [LinearMap.coprod_inl_inr]

Depends on / 依赖: LinearMap, LinearMap.comp_coprod, LinearMap.coprod_inl_inr, comp_coprod, coprod, coprod_inl_inr, of_lifting_property, projective_lifting_property
-/
instance [Projective R P] [Projective R Q] : Projective R (P × Q) := by
  refine .of_lifting_property'' fun f hf => ?_
  rcases projective_lifting_property f (.inl _ _ _) hf with ⟨g₁, hg₁⟩
  rcases projective_lifting_property f (.inr _ _ _) hf with ⟨g₂, hg₂⟩
  refine ⟨coprod g₁ g₂, ?_⟩
  rw [LinearMap.comp_coprod]; rw [hg₁]; rw [hg₂]; rw [LinearMap.coprod_inl_inr]

variable {ι : Type*} (A : ι -> Type*) [forall i : ι, AddCommMonoid (A i)] [forall i : ι, Module R (A i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : forall i : ι, Projective R (A i)] : Projective R (Π₀ i, A i)
  body: .of_lifting_property'' fun f hf => by
    classical
      choose g hg using fun i => projective_lifting_property f (DFinsupp.lsingle i) hf
      replace hg : forall i x, f (g i x) = DFinsupp.single i x := fun i => DFunLike.congr_fun (hg i)
      refine ⟨DFinsupp.coprodMap g, ?_⟩
      ext i x j
      simp only [comp_apply, id_apply, DFinsupp.lsingle_apply, DFinsupp.coprodMap_apply_single, hg]

中文:
实例 [h
  签名: : 对任意 i : ι, 投射 R (A i)] : 投射 R (Π₀ i, A i)
  定义体: .of_lifting_property'' fun f hf => by
    classical
      choose g hg using fun i => projective_lifting_property f (DFinsupp.lsingle i) hf
      replace hg : forall i x, f (g i x) = DFinsupp.single i x := fun i => DFunLike.congr_fun (hg i)
      refine ⟨DFinsupp.coprodMap g, ?_⟩
      ext i x j
      simp only [comp_apply, id_apply, DFinsupp.lsingle_apply, DFinsupp.coprodMap_apply_single, hg]

Depends on / 依赖: DFinsupp, DFinsupp.coprodMap, DFinsupp.coprodMap_apply_single, DFinsupp.lsingle, DFinsupp.lsingle_apply, DFinsupp.single, DFunLike, DFunLike.congr_fun, classical, comp_apply, congr_fun, coprodMap, coprodMap_apply_single, id_apply, lsingle, lsingle_apply, of_lifting_property, projective_lifting_property, replace, single
-/
instance [h : forall i : ι, Projective R (A i)] : Projective R (Π₀ i, A i) :=
  .of_lifting_property'' fun f hf => by
    classical
      choose g hg using fun i => projective_lifting_property f (DFinsupp.lsingle i) hf
      replace hg : forall i x, f (g i x) = DFinsupp.single i x := fun i => DFunLike.congr_fun (hg i)
      refine ⟨DFinsupp.coprodMap g, ?_⟩
      ext i x j
      simp only [comp_apply, id_apply, DFinsupp.lsingle_apply, DFinsupp.coprodMap_apply_single, hg]

/--
theorem `Projective.of_basis` / 定理 `Projective.of_basis`

English:
theorem Projective.of_basis
  given: {ι : Type*} (b : Basis ι R P)
  statement: Projective R P
  proof: by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr Nat fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsuppSum]
  exact b.linearCombination_repr m

中文:
定理 投射.of_basis
  条件: {ι : 类型} (b : 基 ι R P)
  结论: 投射 R P
  证明: by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr Nat fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsuppSum]
  exact b.linearCombination_repr m
-/
theorem Projective.of_basis {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr Nat fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsuppSum]
  exact b.linearCombination_repr m

instance (priority := 100) Projective.of_free [Module.Free R P] : Module.Projective R P :=
.of_basis Module.Free.chooseBasis R P

/--
theorem `Projective.of_split` / 定理 `Projective.of_split`

English:
theorem Projective.of_split
  statement: [Module.Projective R M]
  proof: by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x => ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x => ?_⟩
  rw [LinearMap.comp_apply]; rw [← LinearMap.comp_apply]; rw [hg]; rw [← LinearMap.comp_apply]; rw [H]; rw [LinearMap.id_apply]

中文:
定理 投射.of_split
  结论: [模.投射 R M]
  证明: by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x => ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x => ?_⟩
  rw [LinearMap.comp_apply]; rw [← LinearMap.comp_apply]; rw [hg]; rw [← LinearMap.comp_apply]; rw [H]; rw [LinearMap.id_apply]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.single, LinearMap, LinearMap.comp_apply, LinearMap.id_apply, comp_apply, g.comp, id_apply, linearCombination, projective_lifting_property, single
-/
theorem Projective.of_split [Module.Projective R M]
    (i : P ->ₗ[R] M) (s : M ->ₗ[R] P) (H : s.comp i = LinearMap.id) : Module.Projective R P := by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x => ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x => ?_⟩
  rw [LinearMap.comp_apply]; rw [← LinearMap.comp_apply]; rw [hg]; rw [← LinearMap.comp_apply]; rw [H]; rw [LinearMap.id_apply]

/--
theorem `Projective.of_equiv` / 定理 `Projective.of_equiv`

English:
theorem Projective.of_equiv
  statement: {R S} [Semiring R] [Semiring S] {M N}
  proof: by
  let e₁ : R ≃+* S := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N ->ₗ[S] N ->₀ S :=
  { toFun := fun x => (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y => by ext; simp
    map_smul' := fun r v => by ext i; simp [e₁, e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x => ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsuppSum, e₂.map_smulₛₗ] using! hf

中文:
定理 投射.of_equiv
  结论: {R S} [半环 R] [半环 S] {M N}
  证明: by
  let e₁ : R ≃+* S := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N ->ₗ[S] N ->₀ S :=
  { toFun := fun x => (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y => by ext; simp
    map_smul' := fun r v => by ext i; simp [e₁, e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x => ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsuppSum, e₂.map_smulₛₗ] using! hf

Depends on / 依赖: Projective, RingHomInvPair, RingHomInvPair.toRingEquiv, equivCongrLeft, linearCombination_apply, mapRange, map_add, map_finsuppSum, map_smul, map_zero, replace, sum_mapRange_index, symm.map_smul, toRingEquiv
-/
theorem Projective.of_equiv {R S} [Semiring R] [Semiring S] {M N}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] N)
    [Projective R M] : Projective S N := by
  let e₁ : R ≃+* S := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N ->ₗ[S] N ->₀ S :=
  { toFun := fun x => (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y => by ext; simp
    map_smul' := fun r v => by ext i; simp [e₁, e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x => ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsuppSum, e₂.map_smulₛₗ] using! hf

/--
theorem `Projective.of_equiv'` / 定理 `Projective.of_equiv'`

English:
theorem Projective.of_equiv'
  statement: [Module.Projective R M]
  proof: .of_equiv e

@[deprecated (since := "2026-02-14")] alias Projective.of_ringEquiv := Projective.of_equiv

中文:
定理 投射.of_equiv'
  结论: [模.投射 R M]
  证明: .of_equiv e

@[deprecated (since := "2026-02-14")] alias Projective.of_ringEquiv := Projective.of_equiv

Depends on / 依赖: of_equiv
-/
theorem Projective.of_equiv' [Module.Projective R M]
    (e : M ≃ₗ[R] P) : Module.Projective R P :=
  .of_equiv e

@[deprecated (since := "2026-02-14")] alias Projective.of_ringEquiv := Projective.of_equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Projective
  signature: R M] : Projective R (ULift.{w} M)
  body: Projective.of_equiv' ULift.moduleEquiv.symm

中文:
实例 [投射
  签名: R M] : 投射 R (类型层提升.{w} M)
  定义体: Projective.of_equiv' ULift.moduleEquiv.symm

Depends on / 依赖: Projective, Projective.of_equiv, ULift.moduleEquiv.symm, moduleEquiv, of_equiv
-/
instance [Projective R M] : Projective R (ULift.{w} M) :=
  Projective.of_equiv' ULift.moduleEquiv.symm

/--
theorem `Projective.of_ulift` / 定理 `Projective.of_ulift`

English:
theorem Projective.of_ulift
  given: [Projective R (ULift.{w} M)]
  statement: Projective R M
  proof: Projective.of_equiv' ULift.moduleEquiv

中文:
定理 投射.of_ulift
  条件: [投射 R (类型层提升.{w} M)]
  结论: 投射 R M
  证明: Projective.of_equiv' ULift.moduleEquiv

Depends on / 依赖: Projective, Projective.of_equiv, ULift.moduleEquiv, moduleEquiv, of_equiv
-/
theorem Projective.of_ulift [Projective R (ULift.{w} M)] : Projective R M :=
  Projective.of_equiv' ULift.moduleEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: M] [Projective R M] : Projective R (Shrink.{w} M)
  body: Projective.of_equiv' (Shrink.linearEquiv R M).symm

中文:
实例 [Small.{w}
  签名: M] [投射 R M] : 投射 R (Shrink.{w} M)
  定义体: Projective.of_equiv' (Shrink.linearEquiv R M).symm

Depends on / 依赖: Projective, Projective.of_equiv, Shrink, Shrink.linearEquiv, linearEquiv, of_equiv
-/
instance [Small.{w} M] [Projective R M] : Projective R (Shrink.{w} M) :=
  Projective.of_equiv' (Shrink.linearEquiv R M).symm

/--
theorem `Projective.of_shrink` / 定理 `Projective.of_shrink`

English:
theorem Projective.of_shrink
  given: [Small.{w} M] [Projective R (Shrink.{w} M)]
  statement: Projective R M
  proof: Projective.of_equiv' (Shrink.linearEquiv R M)

中文:
定理 投射.of_shrink
  条件: [Small.{w} M] [投射 R (Shrink.{w} M)]
  结论: 投射 R M
  证明: Projective.of_equiv' (Shrink.linearEquiv R M)

Depends on / 依赖: Projective, Projective.of_equiv, Shrink, Shrink.linearEquiv, linearEquiv, of_equiv
-/
theorem Projective.of_shrink [Small.{w} M] [Projective R (Shrink.{w} M)] : Projective R M :=
  Projective.of_equiv' (Shrink.linearEquiv R M)

/--
theorem `Projective.iff_split_of_projective` / 定理 `Projective.iff_split_of_projective`

English:
theorem Projective.iff_split_of_projective
  statement: [Module.Projective R M] (s : M ->ₗ[R] P)
  proof: ⟨fun _ => projective_lifting_property _ _ hs, fun ⟨i, H⟩ => Projective.of_split i s H⟩

中文:
定理 投射.iff_split_of_projective
  结论: [模.投射 R M] (s : M ->ₗ[R] P)
  证明: ⟨fun _ => projective_lifting_property _ _ hs, fun ⟨i, H⟩ => Projective.of_split i s H⟩

Depends on / 依赖: Projective, Projective.of_split, of_split, projective_lifting_property
-/
theorem Projective.iff_split_of_projective [Module.Projective R M] (s : M ->ₗ[R] P)
    (hs : Function.Surjective s) :
    Module.Projective R P ↔ exists i, s ∘ₗ i = LinearMap.id :=
  ⟨fun _ => projective_lifting_property _ _ hs, fun ⟨i, H⟩ => Projective.of_split i s H⟩

end Semiring

section Ring

variable {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module R P]
variable {R₀ M N} [CommSemiring R₀] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M]
variable [IsScalarTower R₀ R M] [AddCommMonoid N] [Module R₀ N]

/--
theorem `Projective.iff_split'` / 定理 `Projective.iff_split'`

English:
theorem Projective.iff_split'
  given: [Small.{w} R] [Small.{w} P]
  statement: Module.Projective R P ↔
  proof: by
  let e : (Shrink.{w, v} P ->₀ Shrink.{w, u} R) ≃ₗ[R] P ->₀ R :=
    Finsupp.mapDomain.linearEquiv _ R (equivShrink P).symm ≪≫ₗ
      Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)
  refine ⟨fun ⟨i, hi⟩ => ⟨(Shrink.{w} P) ->₀ (Shrink.{w} R), _, _, Free.of_basis ⟨e⟩,
    e.symm.toLinearMap ∘ₗ i, (linearCombination R id) ∘ₗ e.toLinearMap, ?_⟩,
      fun ⟨_, _, _, _, i, s, H⟩ => Projective.of_split i s H⟩
  apply LinearMap.ext
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.apply_symm_apply]
  exact hi

中文:
定理 投射.iff_split'
  条件: [Small.{w} R] [Small.{w} P]
  结论: 模.投射 R P ↔
  证明: by
  let e : (Shrink.{w, v} P ->₀ Shrink.{w, u} R) ≃ₗ[R] P ->₀ R :=
    Finsupp.mapDomain.linearEquiv _ R (equivShrink P).symm ≪≫ₗ
      Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)
  refine ⟨fun ⟨i, hi⟩ => ⟨(Shrink.{w} P) ->₀ (Shrink.{w} R), _, _, Free.of_basis ⟨e⟩,
    e.symm.toLinearMap ∘ₗ i, (linearCombination R id) ∘ₗ e.toLinearMap, ?_⟩,
      fun ⟨_, _, _, _, i, s, H⟩ => Projective.of_split i s H⟩
  apply LinearMap.ext
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.apply_symm_apply]
  exact hi

Depends on / 依赖: Finsupp, Finsupp.mapDomain.linearEquiv, Finsupp.mapRange.linearEquiv, Free.of_basis, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.ext, Projective, Projective.of_split, Shrink, Shrink.linearEquiv, apply_symm_apply, coe_coe, coe_comp, comp_apply, e.apply_symm_apply, e.symm.toLinearMap
-/
theorem Projective.iff_split' [Small.{w} R] [Small.{w} P] : Module.Projective R P ↔
    exists (M : Type w) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P ->ₗ[R] M) (s : M ->ₗ[R] P), s.comp i = LinearMap.id := by
  let e : (Shrink.{w, v} P ->₀ Shrink.{w, u} R) ≃ₗ[R] P ->₀ R :=
    Finsupp.mapDomain.linearEquiv _ R (equivShrink P).symm ≪≫ₗ
      Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)
  refine ⟨fun ⟨i, hi⟩ => ⟨(Shrink.{w} P) ->₀ (Shrink.{w} R), _, _, Free.of_basis ⟨e⟩,
    e.symm.toLinearMap ∘ₗ i, (linearCombination R id) ∘ₗ e.toLinearMap, ?_⟩,
      fun ⟨_, _, _, _, i, s, H⟩ => Projective.of_split i s H⟩
  apply LinearMap.ext
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.apply_symm_apply]
  exact hi

/--
theorem `Projective.iff_split` / 定理 `Projective.iff_split`

English:
theorem Projective.iff_split
  statement: Module.Projective R P ↔
  proof: Projective.iff_split'.{max u v}

中文:
定理 投射.iff_split
  结论: 模.投射 R P ↔
  证明: Projective.iff_split'.{max u v}

Depends on / 依赖: Projective, Projective.iff_split, iff_split
-/
theorem Projective.iff_split : Module.Projective R P ↔
    exists (M : Type max u v) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P ->ₗ[R] M) (s : M ->ₗ[R] P), s.comp i = LinearMap.id :=
  Projective.iff_split'.{max u v}

open TensorProduct in
/--
Instance `Projective.tensorProduct` / 实例 `Projective.tensorProduct`

English:
instance Projective.tensorProduct
  signature: [hM : Module.Projective R M] [hN : Module.Projective R₀ N]
  body: by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M otimes[R₀] (N ->₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M ->₀ R) otimes[R₀] (N ->₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N ->₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.linearCombination R id) (LinearMap.id (R := R₀) (M := N ->₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M otimes[R₀] (N ->₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) (linearCombination R₀ id))
  · ext; simp [hsN _]

中文:
实例 投射.tensorProduct
  签名: [hM : 模.投射 R M] [hN : 模.投射 R₀ N]
  定义体: by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M otimes[R₀] (N ->₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M ->₀ R) otimes[R₀] (N ->₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N ->₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.linearCombination R id) (LinearMap.id (R := R₀) (M := N ->₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M otimes[R₀] (N ->₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) (linearCombination R₀ id))
  · ext; simp [hsN _]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, Finsupp, Finsupp.linearCombination, Linear, LinearMap, LinearMap.id, Module, Module.Projective, Projective, Projective.of_split, fapply, linearCombination, of_split, otimes
-/
instance Projective.tensorProduct [hM : Module.Projective R M] [hN : Module.Projective R₀ N] :
    Module.Projective R (M otimes[R₀] N) := by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M otimes[R₀] (N ->₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M ->₀ R) otimes[R₀] (N ->₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N ->₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.linearCombination R id) (LinearMap.id (R := R₀) (M := N ->₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M otimes[R₀] (N ->₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) (linearCombination R₀ id))
  · ext; simp [hsN _]

end Ring

section OfLiftingProperty

/--
theorem `Projective.of_lifting_property'` / 定理 `Projective.of_lifting_property'`

English:
theorem Projective.of_lifting_property'
  statement: {R : Type u} [Semiring R] {P : Type v}
  proof: by
  refine of_lifting_property'' (fun p hp => ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

中文:
定理 投射.of_lifting_property'
  结论: {R : 类型u} [半环 R] {P : 类型v}
  证明: by
  refine of_lifting_property'' (fun p hp => ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearEquiv, LinearMap, LinearMap.id, Shrink, Shrink.linearEquiv, e.surjective, e.toLinearMap, hp.comp, linearEquiv, mapRange, of_lifting_property, surjective, toLinearMap
-/
theorem Projective.of_lifting_property' {R : Type u} [Semiring R] {P : Type v}
    [AddCommMonoid P] [Module R P] [Small.{v} R]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (h : forall {M : Type v} {N : Type v} [AddCommMonoid M] [AddCommMonoid N]
      [Module R M] [Module R N] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N),
        Function.Surjective f -> exists h : P ->ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P := by
  refine of_lifting_property'' (fun p hp => ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

/--
theorem `Projective.of_lifting_property` / 定理 `Projective.of_lifting_property`

English:
theorem Projective.of_lifting_property
  statement: {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
  proof: by
  refine of_lifting_property'' (fun p hp => ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

中文:
定理 投射.of_lifting_property
  结论: {R : 类型u} [环 R] {P : 类型v} [加法交换群 P]
  证明: by
  refine of_lifting_property'' (fun p hp => ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearEquiv, LinearMap, LinearMap.id, Shrink, Shrink.linearEquiv, e.surjective, e.toLinearMap, hp.comp, linearEquiv, mapRange, of_lifting_property, surjective, toLinearMap
-/
theorem Projective.of_lifting_property {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
    [Module R P] [Small.{v} R]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (h : forall {M : Type v} {N : Type v} [AddCommGroup M] [AddCommGroup N]
      [Module R M] [Module R N] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N),
        Function.Surjective f -> exists h : P ->ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P := by
  refine of_lifting_property'' (fun p hp => ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

end OfLiftingProperty

section DirectSum

variable {R : Type u} [Semiring R]
variable {ι : Type v} {M : ι -> Type w} [(i : ι) -> AddCommMonoid (M i)] [(i : ι) -> Module R (M i)]

/--
theorem `Projective.directSum_iff` / 定理 `Projective.directSum_iff`

English:
theorem Projective.directSum_iff
  statement: Projective R (⨁ i, M i) ↔ forall (i : ι), Projective R (M i)
  proof: by
  classical
  refine ⟨fun H i => ?_, fun H => ?_⟩
  · exact .of_split (DirectSum.lof ..) (DirectSum.component ..) (by simp)
  · let e : (⨁ i, M i) ≃ₗ[R] Π₀ i, M i := .refl ..
    exact Projective.of_equiv' e.symm

中文:
定理 投射.directSum_iff
  结论: 投射 R (⨁ i, M i) ↔ 对任意 (i : ι), 投射 R (M i)
  证明: by
  classical
  refine ⟨fun H i => ?_, fun H => ?_⟩
  · exact .of_split (DirectSum.lof ..) (DirectSum.component ..) (by simp)
  · let e : (⨁ i, M i) ≃ₗ[R] Π₀ i, M i := .refl ..
    exact Projective.of_equiv' e.symm

Depends on / 依赖: DirectSum, DirectSum.component, DirectSum.lof, Projective, Projective.of_equiv, classical, component, e.symm, of_equiv, of_split
-/
theorem Projective.directSum_iff : Projective R (⨁ i, M i) ↔ forall (i : ι), Projective R (M i) := by
  classical
  refine ⟨fun H i => ?_, fun H => ?_⟩
  · exact .of_split (DirectSum.lof ..) (DirectSum.component ..) (by simp)
  · let e : (⨁ i, M i) ≃ₗ[R] Π₀ i, M i := .refl ..
    exact Projective.of_equiv' e.symm

/--
Instance `Projective.directSum` / 实例 `Projective.directSum`

English:
instance Projective.directSum
  signature: [forall (i : ι), Projective R (M i)]
  body: directSum_iff.mpr ‹_›

中文:
实例 投射.directSum
  签名: [对任意 (i : ι), 投射 R (M i)]
  定义体: directSum_iff.mpr ‹_›

Depends on / 依赖: directSum_iff, directSum_iff.mpr
-/
instance Projective.directSum [forall (i : ι), Projective R (M i)] : Projective R (⨁ i, M i) :=
  directSum_iff.mpr ‹_›

end DirectSum

end Module
