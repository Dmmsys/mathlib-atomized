/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Maschke's theorem

We prove **Maschke's theorem** for finite groups,
in the formulation that every submodule of a `k[G]` module has a complement,
when `k` is a field with `Fintype.card G` invertible in `k`.

We do the core computation in greater generality.
For any commutative ring `k` in which `Fintype.card G` is invertible,
and a `k[G]`-linear map `i : V → W` which admits a `k`-linear retraction `π`,
we produce a `k[G]`-linear retraction by
taking the average over `G` of the conjugates of `π`.

## Implementation Notes

* These results assume `IsUnit (Fintype.card G : k)` which is equivalent to the more
  familiar `¬(ringChar k ∣ Fintype.card G)`.

## Future work
It's not so far to give the usual statement, that every finite-dimensional representation
of a finite group is semisimple (i.e. a direct sum of irreducibles).
-/

@[expose] public section

noncomputable section

open Module MonoidAlgebra
open scoped Ring

/-!
We now do the key calculation in Maschke's theorem.

Given `V → W`, an inclusion of `k[G]` modules,
assume we have some retraction `π` (i.e. `∀ v, π (i v) = v`),
just as a `k`-linear map.
(When `k` is a field, this will be available cheaply, by choosing a basis.)

We now construct a retraction of the inclusion as a `k[G]`-linear map,
by the formula
$$ \frac{1}{|G|} \sum_{g \in G} g⁻¹ • π(g • -). $$
-/

namespace LinearMap


-- At first we work with any `[CommRing k]`, and add the assumption that
-- `IsUnit (Fintype.card G : k)` when it is required.
variable {k : Type*} [CommRing k] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module k[G] V] [IsScalarTower k k[G] V]
variable {W : Type*} [AddCommGroup W] [Module k W] [Module k[G] W] [IsScalarTower k k[G] W]
variable (π : W ->ₗ[k] V)

/--
Definition of `conjugate` / `conjugate` 的定义

English:
definition conjugate
  signature: (g : G)
  body: GroupSMul.linearMap k V g⁻¹ ∘ₗ π ∘ₗ GroupSMul.linearMap k W g

中文:
定义 conjugate
  签名: (g : G)
  定义体: GroupSMul.linearMap k V g⁻¹ ∘ₗ π ∘ₗ GroupSMul.linearMap k W g

Depends on / 依赖: GroupSMul, GroupSMul.linearMap, linearMap
-/
def conjugate (g : G) : W ->ₗ[k] V :=
  GroupSMul.linearMap k V g⁻¹ ∘ₗ π ∘ₗ GroupSMul.linearMap k W g

/--
theorem `conjugate_apply` / 定理 `conjugate_apply`

English:
theorem conjugate_apply
  given: (g : G) (v : W)
  proof: rfl

中文:
定理 conjugate_apply
  条件: (g : G) (v : W)
  证明: rfl
-/
theorem conjugate_apply (g : G) (v : W) :
    π.conjugate g v = MonoidAlgebra.single g⁻¹ (1 : k) • π (MonoidAlgebra.single g (1 : k) • v) :=
  rfl

variable (i : V ->ₗ[k[G]] W)

section

/--
theorem `conjugate_i` / 定理 `conjugate_i`

English:
theorem conjugate_i
  given: (h : forall v : V, π (i v) = v) (g : G) (v : V)
  proof: by
  rw [conjugate_apply]; rw [← i.map_smul]; rw [h]; rw [← mul_smul]; rw [single_mul_single]; rw [mul_one]; rw [inv_mul_cancel]; rw [← one_def]; rw [one_smul]

中文:
定理 conjugate_i
  条件: (h : 对任意 v : V, π (i v) = v) (g : G) (v : V)
  证明: by
  rw [conjugate_apply]; rw [← i.map_smul]; rw [h]; rw [← mul_smul]; rw [single_mul_single]; rw [mul_one]; rw [inv_mul_cancel]; rw [← one_def]; rw [one_smul]

Depends on / 依赖: conjugate_apply, i.map_smul, inv_mul_cancel, map_smul, mul_one, mul_smul, one_def, one_smul, single_mul_single
-/
theorem conjugate_i (h : forall v : V, π (i v) = v) (g : G) (v : V) :
    (conjugate π g : W -> V) (i v) = v := by
  rw [conjugate_apply]; rw [← i.map_smul]; rw [h]; rw [← mul_smul]; rw [single_mul_single]; rw [mul_one]; rw [inv_mul_cancel]; rw [← one_def]; rw [one_smul]

end

variable (G) [Fintype G]

/--
Definition of `sumOfConjugates` / `sumOfConjugates` 的定义

English:
definition sumOfConjugates
  signature: : W ->ₗ[k] V
  body: ∑ g : G, π.conjugate g

中文:
定义 sumOfConjugates
  签名: : W ->ₗ[k] V
  定义体: ∑ g : G, π.conjugate g

Depends on / 依赖: conjugate
-/
def sumOfConjugates : W ->ₗ[k] V :=
  ∑ g : G, π.conjugate g

/--
lemma `sumOfConjugates_apply` / 引理 `sumOfConjugates_apply`

English:
lemma sumOfConjugates_apply
  given: (v : W)
  statement: π.sumOfConjugates G v = ∑ g : G, π.conjugate g v
  proof: LinearMap.sum_apply _ _ _

中文:
引理 sumOfConjugates_apply
  条件: (v : W)
  结论: π.sumOfConjugates G v = ∑ g : G, π.conjugate g v
  证明: LinearMap.sum_apply _ _ _

Depends on / 依赖: LinearMap, LinearMap.sum_apply, sum_apply
-/
lemma sumOfConjugates_apply (v : W) : π.sumOfConjugates G v = ∑ g : G, π.conjugate g v :=
  LinearMap.sum_apply _ _ _

/--
Definition of `sumOfConjugatesEquivariant` / `sumOfConjugatesEquivariant` 的定义

English:
definition sumOfConjugatesEquivariant
  signature: : W ->ₗ[k[G]] V
  body: MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v => by
    simp only [sumOfConjugates_apply, Finset.smul_sum, conjugate_apply]
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ fun i => ?_
    simp only [smul_smul, single_mul_single, mul_inv_rev, mul_inv_

中文:
定义 sumOfConjugatesEquivariant
  签名: : W ->ₗ[k[G]] V
  定义体: MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v => by
    simp only [sumOfConjugates_apply, Finset.smul_sum, conjugate_apply]
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ fun i => ?_
    simp only [smul_smul, single_mul_single, mul_inv_rev, mul_inv_

Depends on / 依赖: Finset, Finset.smul_sum, Fintype, Fintype.sum_bijective, Group.mulRight_bijective, MonoidAlgebra, MonoidAlgebra.equivariantOfLinearOfComm, conjugate_apply, equivariantOfLinearOfComm, mulRight_bijective, mul_inv_cancel_left, mul_inv_rev, one_mul, single_mul_single, smul_smul, smul_sum, sumOfConjugates, sumOfConjugates_apply, sum_bijective
-/
def sumOfConjugatesEquivariant : W ->ₗ[k[G]] V :=
  MonoidAlgebra.equivariantOfLinearOfComm (π.sumOfConjugates G) fun g v => by
    simp only [sumOfConjugates_apply, Finset.smul_sum, conjugate_apply]
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ fun i => ?_
    simp only [smul_smul, single_mul_single, mul_inv_rev, mul_inv_cancel_left, one_mul]

/--
theorem `sumOfConjugatesEquivariant_apply` / 定理 `sumOfConjugatesEquivariant_apply`

English:
theorem sumOfConjugatesEquivariant_apply
  given: (v : W)
  proof: π.sumOfConjugates_apply G v

中文:
定理 sumOfConjugatesEquivariant_apply
  条件: (v : W)
  证明: π.sumOfConjugates_apply G v

Depends on / 依赖: sumOfConjugates_apply
-/
theorem sumOfConjugatesEquivariant_apply (v : W) :
    π.sumOfConjugatesEquivariant G v = ∑ g : G, π.conjugate g v :=
  π.sumOfConjugates_apply G v

section

/--
Definition of `equivariantProjection` / `equivariantProjection` 的定义

English:
definition equivariantProjection
  signature: : W ->ₗ[k[G]] V
  body: (Fintype.card G : k)⁻¹ʳ • π.sumOfConjugatesEquivariant G

中文:
定义 equivariantProjection
  签名: : W ->ₗ[k[G]] V
  定义体: (Fintype.card G : k)⁻¹ʳ • π.sumOfConjugatesEquivariant G

Depends on / 依赖: Fintype, Fintype.card, sumOfConjugatesEquivariant
-/
def equivariantProjection : W ->ₗ[k[G]] V :=
  (Fintype.card G : k)⁻¹ʳ • π.sumOfConjugatesEquivariant G

/--
theorem `equivariantProjection_apply` / 定理 `equivariantProjection_apply`

English:
theorem equivariantProjection_apply
  given: (v : W)
  proof: by
  simp only [equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply,
    Fintype.card_eq_nat_card]

中文:
定理 equivariantProjection_apply
  条件: (v : W)
  证明: by
  simp only [equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply,
    Fintype.card_eq_nat_card]

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, card_eq_nat_card, equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply
-/
theorem equivariantProjection_apply (v : W) :
    π.equivariantProjection G v = (Nat.card G : k)⁻¹ʳ • ∑ g : G, π.conjugate g v := by
  simp only [equivariantProjection, smul_apply, sumOfConjugatesEquivariant_apply,
    Fintype.card_eq_nat_card]

/--
theorem `equivariantProjection_condition` / 定理 `equivariantProjection_condition`

English:
theorem equivariantProjection_condition
  statement: (hcard : IsUnit (Nat.card G : k))
  proof: by
  rw [equivariantProjection_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const]; rw [Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul k]; rw [smul_smul]; rw [Fintype.card_eq_nat_card]; rw [Ring.inverse_mul_cancel _ hcard]; rw [one_smul]

中文:
定理 equivariantProjection_condition
  结论: (hcard : 是单位 (自然数.card G : k))
  证明: by
  rw [equivariantProjection_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const]; rw [Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul k]; rw [smul_smul]; rw [Fintype.card_eq_nat_card]; rw [Ring.inverse_mul_cancel _ hcard]; rw [one_smul]

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Fintype, Fintype.card_eq_nat_card, Nat.cast_smul_eq_nsmul, Ring.inverse_mul_cancel, card_eq_nat_card, card_univ, cast_smul_eq_nsmul, conjugate_i, equivariantProjection_apply, inverse_mul_cancel, one_smul, smul_smul, sum_const
-/
theorem equivariantProjection_condition (hcard : IsUnit (Nat.card G : k))
    (h : forall v : V, π (i v) = v) (v : V) : (π.equivariantProjection G) (i v) = v := by
  rw [equivariantProjection_apply]
  simp only [conjugate_i π i h]
  rw [Finset.sum_const]; rw [Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul k]; rw [smul_smul]; rw [Fintype.card_eq_nat_card]; rw [Ring.inverse_mul_cancel _ hcard]; rw [one_smul]

end

end LinearMap

end

namespace MonoidAlgebra

-- Now we work over a `[Field k]`.
variable {k : Type*} [Field k] {G : Type*} [Finite G] [NeZero (Nat.card G : k)]
variable [Group G]
variable {V : Type*} [AddCommGroup V] [Module k[G] V]
variable {W : Type*} [AddCommGroup W] [Module k[G] W]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_leftInverse_of_injective` / 定理 `exists_leftInverse_of_injective`

English:
theorem exists_leftInverse_of_injective
  given: (f : V ->ₗ[k[G]] W) (hf : LinearMap.ker f = ⊥)
  proof: by
  let A := k[G]
  let : Module k W := .compHom W (algebraMap k A)
  let : Module k V := .compHom V (algebraMap k A)
  have := IsScalarTower.of_compHom k A W
  have := IsScalarTower.of_compHom k A V
  set φ := (f.restrictScalars k).leftInverse
  have hφ : forall (x : V), φ (f x) = x := by
    appl

中文:
定理 存在_leftInverse_of_injective
  条件: (f : V ->ₗ[k[G]] W) (hf : 线性映射.ker f = ⊥)
  证明: by
  let A := k[G]
  let : Module k W := .compHom W (algebraMap k A)
  let : Module k V := .compHom V (algebraMap k A)
  have := IsScalarTower.of_compHom k A W
  have := IsScalarTower.of_compHom k A V
  set φ := (f.restrictScalars k).leftInverse
  have hφ : forall (x : V), φ (f x) = x := by
    appl

Depends on / 依赖: Fintype, Fintype.ofFinite, IsScalarTower, IsScalarTower.of_compHom, LinearMap, LinearMap.ext, LinearMap.leftInverse_apply_of_inj, Module, NeZero, NeZero.ne, algebraMap, compHom, equivariantProjection, equivariantProjection_condition, f.restrictScalars, leftInverse, leftInverse_apply_of_inj, ofFinite, of_compHom, restrictScalars
-/
theorem exists_leftInverse_of_injective (f : V ->ₗ[k[G]] W) (hf : LinearMap.ker f = ⊥) :
    exists g : W ->ₗ[k[G]] V, g.comp f = .id := by
  let A := k[G]
  let : Module k W := .compHom W (algebraMap k A)
  let : Module k V := .compHom V (algebraMap k A)
  have := IsScalarTower.of_compHom k A W
  have := IsScalarTower.of_compHom k A V
  set φ := (f.restrictScalars k).leftInverse
  have hφ : forall (x : V), φ (f x) = x := by
    apply LinearMap.leftInverse_apply_of_inj
    simp [hf]
  have _ : Fintype G := Fintype.ofFinite G
  refine ⟨φ.equivariantProjection G, LinearMap.ext ?_⟩
exact φ.equivariantProjection_condition G _ (.mk0 _ <| NeZero.ne _) hφ

namespace Submodule

/--
theorem `exists_isCompl` / 定理 `exists_isCompl`

English:
theorem exists_isCompl
  given: (p : Submodule k[G] V)
  statement: exists q : Submodule k[G] V, IsCompl p q
  proof: by
  rcases MonoidAlgebra.exists_leftInverse_of_injective p.subtype p.ker_subtype with ⟨f, hf⟩
exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj DFunLike.congr_fun hf⟩

中文:
定理 存在_isCompl
  条件: (p : 子模 k[G] V)
  结论: 存在 q : 子模 k[G] V, 是补集 p q
  证明: by
  rcases MonoidAlgebra.exists_leftInverse_of_injective p.subtype p.ker_subtype with ⟨f, hf⟩
exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj DFunLike.congr_fun hf⟩

Depends on / 依赖: DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.isCompl_of_proj, LinearMap.ker, MonoidAlgebra, MonoidAlgebra.exists_leftInverse_of_injective, congr_fun, exists_leftInverse_of_injective, isCompl_of_proj, ker_subtype, p.ker_subtype, p.subtype, subtype
-/
theorem exists_isCompl (p : Submodule k[G] V) : exists q : Submodule k[G] V, IsCompl p q := by
  rcases MonoidAlgebra.exists_leftInverse_of_injective p.subtype p.ker_subtype with ⟨f, hf⟩
exact ⟨LinearMap.ker f, LinearMap.isCompl_of_proj DFunLike.congr_fun hf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSemisimpleModule k[G] V
  body: exists_isCompl

中文:
实例 :
  签名: 是半单模 k[G] V
  定义体: exists_isCompl

Depends on / 依赖: exists_isCompl
-/
instance : IsSemisimpleModule k[G] V where
  exists_isCompl := exists_isCompl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: G] : IsSemisimpleRing (AddMonoidAlgebra k G)
  body: haveI : NeZero (Nat.card (Multiplicative G) : k) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := Nat)).toRingEquiv.symm.isSemisimpleRing

中文:
实例 [加法群
  签名: G] : IsSemisimpleRing (加法幺半群代数 k G)
  定义体: haveI : NeZero (Nat.card (Multiplicative G) : k) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := Nat)).toRingEquiv.symm.isSemisimpleRing

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.toMultiplicativeAlgEquiv, Multiplicative, Multiplicative.toAdd, Nat.card, Nat.card_congr, NeZero, card_congr, isSemisimpleRing, toMultiplicativeAlgEquiv, toRingEquiv, toRingEquiv.symm.isSemisimpleRing
-/
instance [AddGroup G] : IsSemisimpleRing (AddMonoidAlgebra k G) :=
  haveI : NeZero (Nat.card (Multiplicative G) : k) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k G (R := Nat)).toRingEquiv.symm.isSemisimpleRing

section

variable {G k V : Type*} [Group G] [Field k] [Finite G] [NeZero (Nat.card G : k)] [AddCommGroup V]
  [Module k V] (ρ : Representation k G V)

open Representation

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSemisimpleRepresentation ρ
  body: by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

中文:
实例 :
  签名: IsSemisimpleRepresentation ρ
  定义体: by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

Depends on / 依赖: infer_instance, isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
-/
instance : IsSemisimpleRepresentation ρ := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

end

end Submodule

end MonoidAlgebra
