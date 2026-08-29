/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Hilbert's Theorem 90

Let `L/K` be a finite extension of fields. Then this file proves Noether's generalization of
Hilbert's Theorem 90: that the 1st group cohomology $H^1(Aut_K(L), L^\times)$ is trivial. We state
it both in terms of $H^1$ and in terms of cocycles being coboundaries.

Hilbert's original statement was that if $L/K$ is Galois, and $Gal(L/K)$ is cyclic, generated
by an element `σ`, then for every `x : L` such that $N_{L/K}(x) = 1,$ there exists `y : L` such
that $x = y/σ(y).$ Using the fact that `H¹(G, A) ≅ Ker(N_A)/(ρ(g) - 1)(A)` for any finite cyclic
group `G` with generator `g`, we deduce the original statement from Noether's generalization.

Noether's generalization also holds for infinite Galois extensions.

## Main statements

* `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`: Noether's generalization
  of Hilbert's Theorem 90: for all $f: Aut_K(L) \to L^\times$ satisfying the 1-cocycle
  condition, there exists `β : Lˣ` such that $g(β)/β = f(g)$ for all `g : Aut_K(L)`.
* `groupCohomology.H1ofAutOnUnitsUnique`: Noether's generalization of Hilbert's Theorem 90:
  $H^1(Aut_K(L), L^\times)$ is trivial.
* `groupCohomology.exists_div_of_norm_eq_one`: Hilbert's Theorem 90: given a finite cyclic Galois
  extension `L/K`, an element `x : L` such that `N_{L/K}(x) = 1`, and a generator `g` of
  `Gal(L/K)`, there exists `y : Lˣ` such that `y/g y = x`.

## Implementation notes

Given a commutative ring `k` and a group `G`, group cohomology is developed in terms of `k`-linear
`G`-representations on `k`-modules. Therefore stating Noether's generalization of Hilbert 90 in
terms of `H¹` requires us to turn the natural action of `Aut_K(L)` on `Lˣ` into a morphism
`Aut_K(L) →* (Additive Lˣ →ₗ[ℤ] Additive Lˣ)`. Thus we provide the non-`H¹` version too, as its
statement is clearer.

## TODO

* Develop Galois cohomology to extend Noether's result to infinite Galois extensions.
* "Additive Hilbert 90": let `L/K` be a finite Galois extension. Then $H^n(Gal(L/K), L)$ is trivial
  for all $1 ≤ n.$

-/

@[expose] public section


namespace groupCohomology
namespace Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/--
Definition of `aux` / `aux` 的定义

English:
definition aux
  signature: (f : Gal(L/K) -> Lˣ)
  body: Finsupp.linearCombination L (fun φ : Gal(L/K) => (φ : L -> L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

中文:
定义 aux
  签名: (f : Gal(L/K) -> Lˣ)
  定义体: Finsupp.linearCombination L (fun φ : Gal(L/K) => (φ : L -> L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm, Finsupp.linearCombination, equivFunOnFinite, linearCombination
-/
noncomputable def aux (f : Gal(L/K) -> Lˣ) : L -> L :=
  Finsupp.linearCombination L (fun φ : Gal(L/K) => (φ : L -> L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

/--
theorem `aux_ne_zero` / 定理 `aux_ne_zero`

English:
theorem aux_ne_zero
  given: (f : Gal(L/K) -> Lˣ)
  statement: aux f != 0

中文:
定理 aux_ne_zero
  条件: (f : Gal(L/K) -> Lˣ)
  结论: aux f != 0
-/
theorem aux_ne_zero (f : Gal(L/K) -> Lˣ) : aux f != 0 :=
/- the set `Aut_K(L)` is linearly independent in the `L`-vector space `L → L`, by Dedekind's
linear independence of characters -/
  have : LinearIndependent L (fun (f : Gal(L/K)) => (f : L -> L)) :=
    LinearIndependent.comp (ι' := Gal(L/K))
      (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

end Hilbert90
section
open Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/--
theorem `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` / 定理 `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`

English:
theorem isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
  proof: by

中文:
定理 isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
  证明: by
-/
theorem isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (f : Gal(L/K) -> Lˣ) (hf : IsMulCocycle₁ f) :
    IsMulCoboundary₁ f := by
/- Let `z : L` be such that `∑ f(h) * h(z) ≠ 0`, for `h ∈ Aut_K(L)` -/
  obtain ⟨z, hz⟩ : exists z, aux f z != 0 :=
    not_forall.1 (fun H => aux_ne_zero f <| funext <| fun x => H x)
  have : aux f z = ∑ h, f h * h z := by simp [aux, Finsupp.linearCombination, Finsupp.sum_fintype]
/- Let `β = (∑ f(h) * h(z))⁻¹.` -/
  use (Units.mk0 (aux f z) hz)⁻¹
  intro g
/- Then the equality follows from the hypothesis that `f` is a 1-cocycle. -/
  simp only [IsMulCocycle₁, AlgEquiv.smul_units_def,
    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, this,
    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L), ← mul_assoc, ← hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)
    (Group.mulLeft_bijective g) _ _ (fun i => rfl))

end
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/--
Instance `H1ofAutOnUnitsUnique` / 实例 `H1ofAutOnUnitsUnique`

English:
instance H1ofAutOnUnitsUnique
  signature: : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  body: 0
uniq := fun a => H1_induction_on a fun x => (H1π_eq_zero_iff _).2 by
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    rcases isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units x.1
      (isMulCocycle₁_of_mem_cocycles₁ _ x.2) with ⟨β, hβ⟩
    use β

中文:
实例 H1ofAutOnUnitsUnique
  签名: : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  定义体: 0
uniq := fun a => H1_induction_on a fun x => (H1π_eq_zero_iff _).2 by
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    rcases isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units x.1
      (isMulCocycle₁_of_mem_cocycles₁ _ x.2) with ⟨β, hβ⟩
    use β
-/
noncomputable instance H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  default := 0
uniq := fun a => H1_induction_on a fun x => (H1π_eq_zero_iff _).2 by
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    rcases isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units x.1
      (isMulCocycle₁_of_mem_cocycles₁ _ x.2) with ⟨β, hβ⟩
    use β

variable {K L} [IsGalois K L]

open Additive Rep

set_option backward.isDefEq.respectTransparency false in
/--
theorem `norm_ofAlgebraAutOnUnits_eq` / 定理 `norm_ofAlgebraAutOnUnits_eq`

English:
theorem norm_ofAlgebraAutOnUnits_eq
  given: (x : Lˣ)
  proof: by
  simp [Algebra.norm_eq_prod_automorphisms, Representation.norm]

中文:
定理 norm_ofAlgebraAutOnUnits_eq
  条件: (x : Lˣ)
  证明: by
  simp [Algebra.norm_eq_prod_automorphisms, Representation.norm]

Depends on / 依赖: Algebra, Algebra.norm_eq_prod_automorphisms, Representation, Representation.norm, norm_eq_prod_automorphisms
-/
theorem norm_ofAlgebraAutOnUnits_eq (x : Lˣ) :
    (toMul <| toAdditive ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (toAdditive.symm <| ofMul x))).1 = algebraMap K L (Algebra.norm K (x : L)) := by
  simp [Algebra.norm_eq_prod_automorphisms, Representation.norm]

variable [IsCyclic (L ≃ₐ[K] L)] {g : Gal(L/K)}

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] IsCyclic.commGroup in
/--
theorem `exists_div_of_norm_eq_one` / 定理 `exists_div_of_norm_eq_one`

English:
theorem exists_div_of_norm_eq_one
  statement: (hg : forall x, x in Subgroup.zpowers g) {x : L}
  proof: by
  suffices H : forall x, Algebra.norm K x = 1 -> exists y : Lˣ, g y / y = x by
    have hxinv : Algebra.norm K x⁻¹ = 1 := by simp [Algebra.norm_inv, hx]
    obtain ⟨y, hy⟩ := H _ hxinv
    use y
    rw [IsUnit.div_eq_iff y.isUnit] at hy
    rw [hy]
    field_simp
  intro x hx
  let xu : Lˣ := (Al

中文:
定理 exists_div_of_norm_eq_one
  结论: (hg : 对任意 x, x in Subgroup.zpowers g) {x : L}
  证明: by
  suffices H : forall x, Algebra.norm K x = 1 -> exists y : Lˣ, g y / y = x by
    have hxinv : Algebra.norm K x⁻¹ = 1 := by simp [Algebra.norm_inv, hx]
    obtain ⟨y, hy⟩ := H _ hxinv
    use y
    rw [IsUnit.div_eq_iff y.isUnit] at hy
    rw [hy]
    field_simp
  intro x hx
  let xu : Lˣ := (Al

Depends on / 依赖: Algebra, Algebra.norm, Algebra.norm_inv, Algebra.norm_ne_zero_iff, FiniteCyclic, IsUnit, IsUnit.div_eq_iff, algebraMap, div_eq_iff, isUnit, isUnit.unit, map_one, norm_inv, norm_ne_zero_iff, norm_ofAlgebraAutOnUnits_eq, y.isUnit, zero_ne_one, zero_ne_one.symm
-/
theorem exists_div_of_norm_eq_one (hg : forall x, x in Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) : exists y : Lˣ, y / g y = x := by
  suffices H : forall x, Algebra.norm K x = 1 -> exists y : Lˣ, g y / y = x by
    have hxinv : Algebra.norm K x⁻¹ = 1 := by simp [Algebra.norm_inv, hx]
    obtain ⟨y, hy⟩ := H _ hxinv
    use y
    rw [IsUnit.div_eq_iff y.isUnit] at hy
    rw [hy]
    field_simp
  intro x hx
  let xu : Lˣ := (Algebra.norm_ne_zero_iff.1 <| hx ▸ zero_ne_one.symm).isUnit.unit
  have hx' : algebraMap K L (Algebra.norm K (xu : L)) = _ := congrArg (algebraMap K L) hx
  rw [← norm_ofAlgebraAutOnUnits_eq xu]; rw [map_one] at hx'
  have := FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (ofAlgebraAutOnUnits K L) g hg
1 (by simp) ⟨toAdditive.symm ofMul xu, by simp_all⟩
  rcases this.1 (Subsingleton.elim (α := groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) _ _)
    with ⟨y, hy⟩
use toMul toAdditive y
  have := Units.ext_iff.1 congr(toMul <| toAdditive $hy)
  simp only [sub_hom, hom_id,
    Representation.IntertwiningMap.sub_toLinearMap, Representation.IntertwiningMap.toLinearMap_id,
    LinearMap.sub_apply, Representation.IntertwiningMap.coe_toLinearMap, applyAsHom_apply,
    LinearMap.id_coe, id_eq,
    toAdditive_symm_apply, toAdditive_apply, toMul_ofMul, IsUnit.unit_spec, xu] at this
  rw [← this]; rw [toMul_sub]
  simp

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K] [IsDomain A]
variable [IsIntegralClosure B A L]

open scoped nonZeroDivisors

/--
lemma `exists_mul_galRestrict_of_norm_eq_one` / 引理 `exists_mul_galRestrict_of_norm_eq_one`

English:
lemma exists_mul_galRestrict_of_norm_eq_one
  statement: (hg : forall x, x in Subgroup.zpowers g) {η : B}
  proof: by
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isL

中文:
引理 exists_mul_galRestrict_of_norm_eq_one
  结论: (hg : 对任意 x, x in Subgroup.zpowers g) {η : B}
  证明: by
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isL

Depends on / 依赖: Algebra, Algebra.algebraMapSubmo, Algebra.algebraMapSubmonoid, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.isLocalization, IsLocalization, IsLocalization.exists_mk, IsScalarTower, IsScalarTower.algebraMap_eq, IsTorsionFree, Module, Module.IsTorsionFree, Module.isTorsionFree_iff_algebraMap_injective, Units.mk0, algebraMap, algebraMapSubmo, algebraMapSubmonoid, algebraMap_eq
-/
lemma exists_mul_galRestrict_of_norm_eq_one (hg : forall x, x in Subgroup.zpowers g) {η : B}
    (hη : Algebra.norm K (algebraMap B L η) = 1) :
    exists ε : B, ε != 0 ∧ η * galRestrict A K L B g ε = ε := by
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let η' : Lˣ := Units.mk0 (algebraMap B L η) (fun h => by simp [h] at hη)
  obtain ⟨ε, hε⟩ := exists_div_of_norm_eq_one hg hη
  obtain ⟨a, b, h⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B A⁰) ε.1
  obtain ⟨t, ht, ht'⟩ := b.prop
  have : t • IsLocalization.mk' L a b = algebraMap _ _ a := by
    rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply A B L]; rw [ht']; rw [IsLocalization.mk'_spec']
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, _root_.map_zero, div_zero, ← h] at hε
    rw [← hε]; rw [Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · replace hε := hε.symm
    rw [← h]; rw [eq_div_iff_mul_eq] at hε
    · replace hε := congr_arg (t • ·) hε
      rw [Algebra.smul_def]; rw [mul_left_comm]; rw [← Algebra.smul_def t]; rw [← g.toAlgHom_apply]; rw [← AlgHom.map_smul_of_tower]; rw [this] at hε
      apply IsIntegralClosure.algebraMap_injective B A L
      rw [map_mul]; rw [← hε]
      congr 1
      exact algebraMap_galRestrictHom_apply A K L B g a
    · intro e
      rw [(map_eq_zero _).mp e]; rw [zero_div] at hε
      rw [hε]; rw [Algebra.norm_zero] at hη
      exact zero_ne_one hη

end groupCohomology
