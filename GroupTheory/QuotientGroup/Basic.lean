/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Quotients of groups by normal subgroups

This file develops the basic theory of quotients of groups by normal subgroups. In particular, it
proves Noether's first and second isomorphism theorems.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `QuotientGroup.quotientInfEquivProdNormalizerQuotient`: Noether's second isomorphism
  theorem, an explicit isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H`
  that lies in the normalizer `N_G(N)` of a subgroup `N` of a group `G`.
* `QuotientGroup.quotientQuotientEquivQuotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / N) / (M / N)` and `G / M`, where `N ≤ M`.
* `QuotientGroup.comapMk'OrderIso`: The correspondence theorem, a lattice
  isomorphism between the lattice of subgroups of `G ⧸ N` and the sublattice
  of subgroups of `G` containing `N`.

## Tags

isomorphism theorems, quotient groups
-/

@[expose] public section

open Function
open scoped Pointwise

universe u v w x
namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

open scoped Pointwise in
@[to_additive]
/--
theorem `sound` / 定理 `sound`

English:
theorem sound
  given: (U : Set (G ⧸ N)) (g : N.op)
  proof: by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

中文:
定理 sound
  条件: (U : Set (G ⧸ N)) (g : N.op)
  证明: by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

Depends on / 依赖: Quotient, Quotient.sound, Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_smul_set_iff_inv_smul_mem
-/
theorem sound (U : Set (G ⧸ N)) (g : N.op) :
    g • (mk' N) ⁻¹' U = (mk' N) ⁻¹' U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

-- for commutative groups we don't need normality assumption

local notation " Q " => G ⧸ N

@[to_additive (attr := simp)]
/--
theorem `mk_prod` / 定理 `mk_prod`

English:
theorem mk_prod
  given: {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι -> G}
  proof: map_prod (QuotientGroup.mk' N) _ _

@[to_additive QuotientAddGroup.strictMono_comap_prod_map]

中文:
定理 mk_prod
  条件: {G ι : 类型} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι -> G}
  证明: map_prod (QuotientGroup.mk' N) _ _

@[to_additive QuotientAddGroup.strictMono_comap_prod_map]

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, map_prod
-/
theorem mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι -> G} :
    ((Finset.prod s f : G) : G ⧸ N) = Finset.prod s (fun i => (f i : G ⧸ N)) :=
  map_prod (QuotientGroup.mk' N) _ _

@[to_additive QuotientAddGroup.strictMono_comap_prod_map]
/--
theorem `strictMono_comap_prod_map` / 定理 `strictMono_comap_prod_map`

English:
theorem strictMono_comap_prod_map
  proof: strictMono_comap_prod_image N

中文:
定理 strictMono_comap_prod_map
  证明: strictMono_comap_prod_image N

Depends on / 依赖: strictMono_comap_prod_image
-/
theorem strictMono_comap_prod_map :
    StrictMono fun H : Subgroup G => (H.comap N.subtype, H.map (mk' N)) :=
  strictMono_comap_prod_image N

/-- `(G × H) / (A × B)` is in bijection with `G / A × H / B`. -/
@[to_additive (attr := simps) QuotientAddGroup.prodEquiv
/-- `(G × H) / (A × B)` is in bijection with `G / A × H / B`. -/]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (A : Subgroup G) (B : Subgroup H)
  body: q.liftOn' (fun (g, h) => (g, h))
      (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq])
  invFun q := q.1.liftOn₂' q.2 (fun g h => (g, h))
    (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq, ← and_imp])
  left_inv q := q.inductionOn' (by simp)


中文:
定义 prodEquiv
  签名: (A : Subgroup G) (B : Subgroup H)
  定义体: q.liftOn' (fun (g, h) => (g, h))
      (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq])
  invFun q := q.1.liftOn₂' q.2 (fun g h => (g, h))
    (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq, ← and_imp])
  left_inv q := q.inductionOn' (by simp)


Depends on / 依赖: liftOn, q.liftOn
-/
def prodEquiv (A : Subgroup G) (B : Subgroup H) : (G × H) ⧸ (A.prod B) ≃ (G ⧸ A) × H ⧸ B where
  toFun q := q.liftOn' (fun (g, h) => (g, h))
      (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq])
  invFun q := q.1.liftOn₂' q.2 (fun g h => (g, h))
    (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq, ← and_imp])
  left_inv q := q.inductionOn' (by simp)
  right_inv := fun (q₁, q₂) => Quotient.inductionOn₂' q₁ q₂ (by simp)

/-- `(G × H) / (A × B)` is isomorphic to `G / A × H / B`. -/
@[to_additive (attr := simps!) QuotientAddGroup.prodAddEquiv
/-- `(G × H) / (A × B)` is isomorphic to `G / A × H / B`. -/]
/--
Definition of `prodMulEquiv` / `prodMulEquiv` 的定义

English:
definition prodMulEquiv
  signature: (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal]
  body: prodEquiv A B
  map_mul' q₁ q₂ := Quotient.inductionOn₂' q₁ q₂ (fun _ _ => rfl)

中文:
定义 prodMulEquiv
  签名: (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal]
  定义体: prodEquiv A B
  map_mul' q₁ q₂ := Quotient.inductionOn₂' q₁ q₂ (fun _ _ => rfl)

Depends on / 依赖: prodEquiv
-/
def prodMulEquiv (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] :
    (G × H) ⧸ (A.prod B) ≃* (G ⧸ A) × H ⧸ B where
  __ := prodEquiv A B
  map_mul' q₁ q₂ := Quotient.inductionOn₂' q₁ q₂ (fun _ _ => rfl)

variable (φ : G ->* H)

open MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive /-- The induced map from the quotient by the kernel to the codomain. -/]
/--
Definition of `kerLift` / `kerLift` 的定义

English:
definition kerLift
  signature: : G ⧸ ker φ ->* H
  body: lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]

中文:
定义 kerLift
  签名: : G ⧸ ker φ ->* H
  定义体: lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]

Depends on / 依赖: mem_ker, mem_ker.mp
-/
def kerLift : G ⧸ ker φ ->* H :=
  lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]
/--
theorem `kerLift_mk` / 定理 `kerLift_mk`

English:
theorem kerLift_mk
  given: (g : G)
  statement: (kerLift φ) g = φ g
  proof: rfl

@[to_additive]

中文:
定理 kerLift_mk
  条件: (g : G)
  结论: (kerLift φ) g = φ g
  证明: rfl

@[to_additive]
-/
theorem kerLift_mk (g : G) : (kerLift φ) g = φ g :=
  rfl

@[to_additive]
/--
theorem `kerLift_injective` / 定理 `kerLift_injective`

English:
theorem kerLift_injective
  statement: Injective (kerLift φ)
  proof: fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
Quotient.sound' by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_cancel]

中文:
定理 kerLift_injective
  结论: Injective (kerLift φ)
  证明: fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
Quotient.sound' by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_cancel]
-/
theorem kerLift_injective : Injective (kerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
Quotient.sound' by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_cancel]

-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive /-- The induced map from the quotient by the kernel to the range. -/]
/--
Definition of `rangeKerLift` / `rangeKerLift` 的定义

English:
definition rangeKerLift
  signature: : G ⧸ ker φ ->* φ.range
  body: lift _ φ.rangeRestrict fun g hg => mem_ker.mp by rwa [ker_rangeRestrict]

@[to_additive]

中文:
定义 rangeKerLift
  签名: : G ⧸ ker φ ->* φ.range
  定义体: lift _ φ.rangeRestrict fun g hg => mem_ker.mp by rwa [ker_rangeRestrict]

@[to_additive]

Depends on / 依赖: ker_rangeRestrict, mem_ker, mem_ker.mp, rangeRestrict
-/
def rangeKerLift : G ⧸ ker φ ->* φ.range :=
lift _ φ.rangeRestrict fun g hg => mem_ker.mp by rwa [ker_rangeRestrict]

@[to_additive]
/--
theorem `rangeKerLift_injective` / 定理 `rangeKerLift_injective`

English:
theorem rangeKerLift_injective
  statement: Injective (rangeKerLift φ)
  proof: fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
Quotient.sound' by
      rw [leftRel_apply]; rw [← ker_rangeRestrict]; rw [mem_ker]; rw [φ.rangeRestrict.map_mul]; rw [← h]; rw [φ.rangeRestrict.map_inv]; rw [inv_mul_cancel]

@[to_additive]

中文:
定理 rangeKerLift_injective
  结论: Injective (rangeKerLift φ)
  证明: fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
Quotient.sound' by
      rw [leftRel_apply]; rw [← ker_rangeRestrict]; rw [mem_ker]; rw [φ.rangeRestrict.map_mul]; rw [← h]; rw [φ.rangeRestrict.map_inv]; rw [inv_mul_cancel]

@[to_additive]
-/
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
Quotient.sound' by
      rw [leftRel_apply]; rw [← ker_rangeRestrict]; rw [mem_ker]; rw [φ.rangeRestrict.map_mul]; rw [← h]; rw [φ.rangeRestrict.map_inv]; rw [inv_mul_cancel]

@[to_additive]
/--
theorem `rangeKerLift_surjective` / 定理 `rangeKerLift_surjective`

English:
theorem rangeKerLift_surjective
  statement: Surjective (rangeKerLift φ)
  proof: by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl

中文:
定理 rangeKerLift_surjective
  结论: Surjective (rangeKerLift φ)
  证明: by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl
-/
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive /-- The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/]
/--
Definition of `quotientKerEquivRange` / `quotientKerEquivRange` 的定义

English:
definition quotientKerEquivRange
  signature: : G ⧸ ker φ ≃* range φ
  body: MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

中文:
定义 quotientKerEquivRange
  签名: : G ⧸ ker φ ≃* range φ
  定义体: MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, ofBijective, rangeKerLift, rangeKerLift_injective, rangeKerLift_surjective
-/
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive (attr := simps) /-- The canonical isomorphism `G/(ker φ) ≃+ H` induced by a
homomorphism `φ : G →+ H` with a right inverse `ψ : H → G`. -/]
/--
Definition of `quotientKerEquivOfRightInverse` / `quotientKerEquivOfRightInverse` 的定义

English:
definition quotientKerEquivOfRightInverse
  signature: (ψ : H -> G) (hφ : RightInverse ψ φ)
  body: { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk, hφ])
    right_inv := hφ }

中文:
定义 quotientKerEquivOfRightInverse
  签名: (ψ : H -> G) (hφ : RightInverse ψ φ)
  定义体: { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk, hφ])
    right_inv := hφ }

Depends on / 依赖: Function, Function.comp_apply, comp_apply, invFun, kerLift, kerLift_injective, kerLift_mk, left_inv, right_inv
-/
def quotientKerEquivOfRightInverse (ψ : H -> G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk, hφ])
    right_inv := hφ }

/-- The canonical isomorphism `G/⊥ ≃* G`. -/
@[to_additive (attr := simps!) /-- The canonical isomorphism `G/⊥ ≃+ G`. -/]
/--
Definition of `quotientBot` / `quotientBot` 的定义

English:
definition quotientBot
  signature: : G ⧸ (⊥ : Subgroup G) ≃* G
  body: quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl

中文:
定义 quotientBot
  签名: : G ⧸ (⊥ : Subgroup G) ≃* G
  定义体: quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl

Depends on / 依赖: MonoidHom, MonoidHom.id, quotientKerEquivOfRightInverse
-/
def quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G :=
  quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `QuotientGroup.quotientKerEquivOfRightInverse`.
-/
@[to_additive /-- The canonical isomorphism `G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.
For a `computable` version, see `QuotientAddGroup.quotientKerEquivOfRightInverse`. -/]
/--
Definition of `quotientKerEquivOfSurjective` / `quotientKerEquivOfSurjective` 的定义

English:
definition quotientKerEquivOfSurjective
  signature: (hφ : Surjective φ)
  body: quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec

中文:
定义 quotientKerEquivOfSurjective
  签名: (hφ : Surjective φ)
  定义体: quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec

Depends on / 依赖: choose_spec, hasRightInverse, hasRightInverse.choose_spec, quotientKerEquivOfRightInverse
-/
noncomputable def quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H :=
  quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive /-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/]
/--
Definition of `quotientMulEquivOfEq` / `quotientMulEquivOfEq` 的定义

English:
definition quotientMulEquivOfEq
  signature: {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N)
  body: { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }

@[to_additive (attr := simp)]

中文:
定义 quotientMulEquivOfEq
  签名: {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N)
  定义体: { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.inductionOn, Subgroup, Subgroup.quotientEquivOfEq, map_mul, quotientEquivOfEq
-/
def quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N :=
  { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }

@[to_additive (attr := simp)]
/--
theorem `quotientMulEquivOfEq_mk` / 定理 `quotientMulEquivOfEq_mk`

English:
theorem quotientMulEquivOfEq_mk
  given: {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G)
  proof: rfl

中文:
定理 quotientMulEquivOfEq_mk
  条件: {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G)
  证明: rfl
-/
theorem quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G) :
    QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive /-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`, then there is a
map `A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions. -/]
/--
Definition of `quotientMapSubgroupOfOfLe` / `quotientMapSubgroupOfOfLe` 的定义

English:
definition quotientMapSubgroupOfOfLe
  signature: {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
  body: map _ _ (Subgroup.inclusion h) Subgroup.comap_mono h'

@[to_additive (attr := simp)]

中文:
定义 quotientMapSubgroupOfOfLe
  签名: {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
  定义体: map _ _ (Subgroup.inclusion h) Subgroup.comap_mono h'

@[to_additive (attr := simp)]

Depends on / 依赖: Subgroup, Subgroup.comap_mono, Subgroup.inclusion, comap_mono, inclusion
-/
def quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' <= B') (h : A <= B) :
    A ⧸ A'.subgroupOf A ->* B ⧸ B'.subgroupOf B :=
map _ _ (Subgroup.inclusion h) Subgroup.comap_mono h'

@[to_additive (attr := simp)]
/--
theorem `quotientMapSubgroupOfOfLe_mk` / 定理 `quotientMapSubgroupOfOfLe_mk`

English:
theorem quotientMapSubgroupOfOfLe_mk
  statement: {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
  proof: rfl

中文:
定理 quotientMapSubgroupOfOfLe_mk
  结论: {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
  证明: rfl
-/
theorem quotientMapSubgroupOfOfLe_mk {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' <= B') (h : A <= B) (x : A) :
    quotientMapSubgroupOfOfLe h' h x = ↑(Subgroup.inclusion h x : B) :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroupOf A : Subgroup A)` depends on `A`.
-/
@[to_additive /-- Let `A', A, B', B` be subgroups of `G`. If `A' = B'` and `A = B`, then the
quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic. Applying this equiv is nicer than
rewriting along the equalities, since the type of `(A'.addSubgroupOf A : AddSubgroup A)` depends on
`A`. -/]
/--
Definition of `equivQuotientSubgroupOfOfEq` / `equivQuotientSubgroupOfOfEq` 的定义

English:
definition equivQuotientSubgroupOfOfEq
  signature: {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
  body: (quotientMapSubgroupOfOfLe h'.le h.le).toMulEquiv (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)

中文:
定义 equivQuotientSubgroupOfOfEq
  签名: {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
  定义体: (quotientMapSubgroupOfOfLe h'.le h.le).toMulEquiv (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)

Depends on / 依赖: h.ge, h.le, quotientMapSubgroupOfOfLe, toMulEquiv
-/
def equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
    [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) :
    A ⧸ A'.subgroupOf A ≃* B ⧸ B'.subgroupOf B :=
  (quotientMapSubgroupOfOfLe h'.le h.le).toMulEquiv (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)

section ZPow

variable {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
variable (f : A ->* B) (g : B ->* A) (e : A ≃* B) (d : B ≃* C) (n : Int)

/-- The map of quotients by powers of an integer induced by a group homomorphism. -/
@[to_additive /-- The map of quotients by multiples of an integer induced by an additive group
homomorphism. -/]
/--
Definition of `homQuotientZPowOfHom` / `homQuotientZPowOfHom` 的定义

English:
definition homQuotientZPowOfHom
  signature: :
  body: lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩

@[to_additive (attr := simp)]

中文:
定义 homQuotientZPowOfHom
  签名: :
  定义体: lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩

@[to_additive (attr := simp)]

Depends on / 依赖: eq_one_iff, map_zpow, zpowGroupHom_apply
-/
def homQuotientZPowOfHom :
    A ⧸ (zpowGroupHom n : A ->* A).range ->* B ⧸ (zpowGroupHom n : B ->* B).range :=
  lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩

@[to_additive (attr := simp)]
/--
theorem `homQuotientZPowOfHom_id` / 定理 `homQuotientZPowOfHom_id`

English:
theorem homQuotientZPowOfHom_id
  statement: homQuotientZPowOfHom (MonoidHom.id A) n = MonoidHom.id _
  proof: monoidHom_ext _ rfl

@[to_additive (attr := simp)]

中文:
定理 homQuotientZPowOfHom_id
  结论: homQuotientZPowOfHom (MonoidHom.id A) n = MonoidHom.id _
  证明: monoidHom_ext _ rfl

@[to_additive (attr := simp)]

Depends on / 依赖: monoidHom_ext
-/
theorem homQuotientZPowOfHom_id : homQuotientZPowOfHom (MonoidHom.id A) n = MonoidHom.id _ :=
  monoidHom_ext _ rfl

@[to_additive (attr := simp)]
/--
theorem `homQuotientZPowOfHom_comp` / 定理 `homQuotientZPowOfHom_comp`

English:
theorem homQuotientZPowOfHom_comp
  proof: monoidHom_ext _ rfl

@[to_additive (attr := simp)]

中文:
定理 homQuotientZPowOfHom_comp
  证明: monoidHom_ext _ rfl

@[to_additive (attr := simp)]

Depends on / 依赖: monoidHom_ext
-/
theorem homQuotientZPowOfHom_comp :
    homQuotientZPowOfHom (f.comp g) n =
      (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) :=
  monoidHom_ext _ rfl

@[to_additive (attr := simp)]
/--
theorem `homQuotientZPowOfHom_comp_of_rightInverse` / 定理 `homQuotientZPowOfHom_comp_of_rightInverse`

English:
theorem homQuotientZPowOfHom_comp_of_rightInverse
  given: (i : Function.RightInverse g f)
  proof: monoidHom_ext _ MonoidHom.ext fun x => congrArg _ i x

中文:
定理 homQuotientZPowOfHom_comp_of_rightInverse
  条件: (i : Function.RightInverse g f)
  证明: monoidHom_ext _ MonoidHom.ext fun x => congrArg _ i x

Depends on / 依赖: MonoidHom, MonoidHom.ext, monoidHom_ext
-/
theorem homQuotientZPowOfHom_comp_of_rightInverse (i : Function.RightInverse g f) :
    (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) = MonoidHom.id _ :=
monoidHom_ext _ MonoidHom.ext fun x => congrArg _ i x

/-- The equivalence of quotients by powers of an integer induced by a group isomorphism. -/
@[to_additive /-- The equivalence of quotients by multiples of an integer induced by an additive
group isomorphism. -/]
/--
Definition of `equivQuotientZPowOfEquiv` / `equivQuotientZPowOfEquiv` 的定义

English:
definition equivQuotientZPowOfEquiv
  signature: :
  body: MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B ->* A) (e : A ->* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A ->* B) (e.symm : B ->* A) n e.right_inv)
    -- Porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s

@[to_ad

中文:
定义 equivQuotientZPowOfEquiv
  签名: :
  定义体: MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B ->* A) (e : A ->* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A ->* B) (e.symm : B ->* A) n e.right_inv)
    -- Porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s

@[to_ad

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, e.left_inv, e.right_inv, e.symm, homQuotientZPowOfHom_comp_of_rightInverse, left_inv, right_inv, toMulEquiv
-/
def equivQuotientZPowOfEquiv :
    A ⧸ (zpowGroupHom n : A ->* A).range ≃* B ⧸ (zpowGroupHom n : B ->* B).range :=
  MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B ->* A) (e : A ->* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A ->* B) (e.symm : B ->* A) n e.right_inv)
    -- Porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s

@[to_additive (attr := simp)]
/--
theorem `equivQuotientZPowOfEquiv_refl` / 定理 `equivQuotientZPowOfEquiv_refl`

English:
theorem equivQuotientZPowOfEquiv_refl
  proof: by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

@[to_additive (attr := simp)]

中文:
定理 equivQuotientZPowOfEquiv_refl
  证明: by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem equivQuotientZPowOfEquiv_refl :
    MulEquiv.refl (A ⧸ (zpowGroupHom n : A ->* A).range) =
      equivQuotientZPowOfEquiv (MulEquiv.refl A) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

@[to_additive (attr := simp)]
/--
theorem `equivQuotientZPowOfEquiv_symm` / 定理 `equivQuotientZPowOfEquiv_symm`

English:
theorem equivQuotientZPowOfEquiv_symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 equivQuotientZPowOfEquiv_symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem equivQuotientZPowOfEquiv_symm :
    (equivQuotientZPowOfEquiv e n).symm = equivQuotientZPowOfEquiv e.symm n :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `equivQuotientZPowOfEquiv_trans` / 定理 `equivQuotientZPowOfEquiv_trans`

English:
theorem equivQuotientZPowOfEquiv_trans
  proof: by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

中文:
定理 equivQuotientZPowOfEquiv_trans
  证明: by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem equivQuotientZPowOfEquiv_trans :
    (equivQuotientZPowOfEquiv e n).trans (equivQuotientZPowOfEquiv d n) =
      equivQuotientZPowOfEquiv (e.trans d) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

end ZPow

section SndIsomorphismThm

open Subgroup

/-- **Noether's second isomorphism theorem**: given a subgroup `N` of `G` and a
subgroup `H` of the normalizer of `N` in `G`,
defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive /-- Noether's second isomorphism theorem: given a subgroup `N` of `G` and a
subgroup `H` of the normalizer of `N` in `G`,
defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N` -/]
/--
Definition of `quotientInfEquivProdNormalizerQuotient` / `quotientInfEquivProdNormalizerQuotient` 的定义

English:
definition quotientInfEquivProdNormalizerQuotient
  signature: (H N : Subgroup G)
  body: Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer

中文:
定义 quotientInfEquivProdNormalizerQuotient
  签名: (H N : Subgroup G)
  定义体: Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer

Depends on / 依赖: Subgroup, Subgroup.normal_subgroupOf_of_le_normalizer, normal_subgroupOf_of_le_normalizer
-/
noncomputable def quotientInfEquivProdNormalizerQuotient (H N : Subgroup G)
    (hLE : H <= normalizer N) :
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  -- φ is the natural homomorphism H →* (HN)/N.
  let φ : H ->* _ ⧸ N.subgroupOf (H ⊔ N) :=
    (mk' <| N.subgroupOf (H ⊔ N)).comp (inclusion le_sup_left)
  have φ_surjective : Surjective φ := fun x =>
x.inductionOn' by
      rintro ⟨y, hy : y in (H ⊔ N)⟩
      rw [← SetLike.mem_coe] at hy
      rw [coe_mul_of_left_le_normalizer_right H N hLE] at hy
      rcases hy with ⟨h, hh, n, hn, rfl⟩
      simp only [SetLike.mem_coe] at hn
      use ⟨h, hh⟩
      refine Quotient.eq.mpr ?_
      simp [leftRel_apply, inclusion, mem_subgroupOf, hn]
  (quotientMulEquivOfEq (by simp [φ, ← comap_ker])).trans
    (quotientKerEquivOfSurjective φ φ_surjective)

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`,
where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive /-- Noether's second isomorphism theorem: given two subgroups `H` and `N` of a group
`G`, where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`. -/]
/--
Definition of `quotientInfEquivProdNormalQuotient` / `quotientInfEquivProdNormalQuotient` 的定义

English:
definition quotientInfEquivProdNormalQuotient
  signature: (H N : Subgroup G) [hN : N.Normal]
  body: quotientInfEquivProdNormalizerQuotient H N le_normalizer_of_normal

中文:
定义 quotientInfEquivProdNormalQuotient
  签名: (H N : Subgroup G) [hN : N.Normal]
  定义体: quotientInfEquivProdNormalizerQuotient H N le_normalizer_of_normal

Depends on / 依赖: le_normalizer_of_normal, quotientInfEquivProdNormalizerQuotient
-/
noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [hN : N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  quotientInfEquivProdNormalizerQuotient H N le_normalizer_of_normal

end SndIsomorphismThm

section ThirdIsoThm

variable (M : Subgroup G) [nM : M.Normal]

@[to_additive]
/--
Instance `map_normal` / 实例 `map_normal`

English:
instance map_normal
  signature: : (M.map (QuotientGroup.mk' N)).Normal
  body: nM.map _ mk_surjective

中文:
实例 map_normal
  签名: : (M.map (QuotientGroup.mk' N)).Normal
  定义体: nM.map _ mk_surjective

Depends on / 依赖: mk_surjective, nM.map
-/
instance map_normal : (M.map (QuotientGroup.mk' N)).Normal :=
  nM.map _ mk_surjective

variable (h : N <= M)

set_option backward.isDefEq.respectTransparency false in
/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive /-- The map from the third isomorphism theorem for additive groups:
`(A / N) / (M / N) → A / M`. -/]
/--
Definition of `quotientQuotientEquivQuotientAux` / `quotientQuotientEquivQuotientAux` 的定义

English:
definition quotientQuotientEquivQuotientAux
  signature: : (G ⧸ N) ⧸ M.map (mk' N) ->* G ⧸ M
  body: lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker]; rw [map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

@[to_additive (attr := simp)]

中文:
定义 quotientQuotientEquivQuotientAux
  签名: : (G ⧸ N) ⧸ M.map (mk' N) ->* G ⧸ M
  定义体: lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker]; rw [map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

@[to_additive (attr := simp)]

Depends on / 依赖: M.map, MonoidHom, MonoidHom.id, QuotientGroup, QuotientGroup.eq_one_iff, eq_one_iff, map_mk, mem_ker
-/
def quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) ->* G ⧸ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker]; rw [map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

@[to_additive (attr := simp)]
/--
theorem `quotientQuotientEquivQuotientAux_mk` / 定理 `quotientQuotientEquivQuotientAux_mk`

English:
theorem quotientQuotientEquivQuotientAux_mk
  given: (x : G ⧸ N)
  proof: QuotientGroup.lift_mk' _ _ x

@[to_additive]

中文:
定理 quotientQuotientEquivQuotientAux_mk
  条件: (x : G ⧸ N)
  证明: QuotientGroup.lift_mk' _ _ x

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.lift_mk, lift_mk
-/
theorem quotientQuotientEquivQuotientAux_mk (x : G ⧸ N) :
    quotientQuotientEquivQuotientAux N M h x = QuotientGroup.map N M (MonoidHom.id G) h x :=
  QuotientGroup.lift_mk' _ _ x

@[to_additive]
/--
theorem `quotientQuotientEquivQuotientAux_mk_mk` / 定理 `quotientQuotientEquivQuotientAux_mk_mk`

English:
theorem quotientQuotientEquivQuotientAux_mk_mk
  given: (x : G)
  proof: QuotientGroup.lift_mk' (M.map (mk' N)) _ x

中文:
定理 quotientQuotientEquivQuotientAux_mk_mk
  条件: (x : G)
  证明: QuotientGroup.lift_mk' (M.map (mk' N)) _ x

Depends on / 依赖: M.map, QuotientGroup, QuotientGroup.lift_mk, lift_mk
-/
theorem quotientQuotientEquivQuotientAux_mk_mk (x : G) :
    quotientQuotientEquivQuotientAux N M h (x : G ⧸ N) = x :=
  QuotientGroup.lift_mk' (M.map (mk' N)) _ x

set_option backward.isDefEq.respectTransparency false in
/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃* G / M`. -/
@[to_additive
/-- **Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃+ A / M`. -/]
/--
Definition of `quotientQuotientEquivQuotient` / `quotientQuotientEquivQuotient` 的定义

English:
definition quotientQuotientEquivQuotient
  signature: : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M
  body: MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)

中文:
定义 quotientQuotientEquivQuotient
  签名: : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M
  定义体: MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, QuotientGroup, QuotientGroup.map, QuotientGroup.mk, Subgroup, Subgroup.le_comap_map, le_comap_map, quotientQuotientEquivQuotientAux, toMulEquiv
-/
def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)

end ThirdIsoThm

section CorrespTheorem

-- All these theorems are primed because `QuotientGroup.mk'` is.
set_option linter.docPrime false

@[to_additive]
/--
theorem `le_comap_mk'` / 定理 `le_comap_mk'`

English:
theorem le_comap_mk'
  given: (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N))
  proof: by
  simpa using Subgroup.comap_mono (f := mk' N) bot_le

@[to_additive (attr := simp)]

中文:
定理 le_comap_mk'
  条件: (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N))
  证明: by
  simpa using Subgroup.comap_mono (f := mk' N) bot_le

@[to_additive (attr := simp)]

Depends on / 依赖: Subgroup, Subgroup.comap_mono, bot_le, comap_mono
-/
theorem le_comap_mk' (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) :
    N <= Subgroup.comap (QuotientGroup.mk' N) H := by
  simpa using Subgroup.comap_mono (f := mk' N) bot_le

@[to_additive (attr := simp)]
/--
theorem `comap_map_mk'` / 定理 `comap_map_mk'`

English:
theorem comap_map_mk'
  given: (N H : Subgroup G) [N.Normal]
  proof: by
  simp [Subgroup.comap_map_eq, sup_comm]

中文:
定理 comap_map_mk'
  条件: (N H : Subgroup G) [N.Normal]
  证明: by
  simp [Subgroup.comap_map_eq, sup_comm]

Depends on / 依赖: Subgroup, Subgroup.comap_map_eq, comap_map_eq, sup_comm
-/
theorem comap_map_mk' (N H : Subgroup G) [N.Normal] :
    Subgroup.comap (mk' N) (Subgroup.map (mk' N) H) = N ⊔ H := by
  simp [Subgroup.comap_map_eq, sup_comm]

/-- The **correspondence theorem**, or lattice theorem,
or fourth isomorphism theorem for multiplicative groups -/
@[to_additive /-- The **correspondence theorem**, or lattice theorem,
  or fourth isomorphism theorem for additive groups -/]
/--
Definition of `comapMk'OrderIso` / `comapMk'OrderIso` 的定义

English:
definition comapMk'OrderIso
  signature: (N : Subgroup G) [hn : N.Normal]
  body: ⟨Subgroup.comap (mk' N) H', le_comap_mk' N _⟩
  invFun H := Subgroup.map (mk' N) H
left_inv H' := Subgroup.map_comap_eq_self by simp
right_inv := fun ⟨H, hH⟩ => Subtype.ext by simpa
map_rel_iff' := Subgroup.comap_le_comap_of_surjective mk'_surjective _

中文:
定义 comapMk'OrderIso
  签名: (N : Subgroup G) [hn : N.Normal]
  定义体: ⟨Subgroup.comap (mk' N) H', le_comap_mk' N _⟩
  invFun H := Subgroup.map (mk' N) H
left_inv H' := Subgroup.map_comap_eq_self by simp
right_inv := fun ⟨H, hH⟩ => Subtype.ext by simpa
map_rel_iff' := Subgroup.comap_le_comap_of_surjective mk'_surjective _

Depends on / 依赖: Subgroup, Subgroup.comap, le_comap_mk
-/
def comapMk'OrderIso (N : Subgroup G) [hn : N.Normal] :
    Subgroup (G ⧸ N) ≃o { H : Subgroup G // N <= H } where
  toFun H' := ⟨Subgroup.comap (mk' N) H', le_comap_mk' N _⟩
  invFun H := Subgroup.map (mk' N) H
left_inv H' := Subgroup.map_comap_eq_self by simp
right_inv := fun ⟨H, hH⟩ => Subtype.ext by simpa
map_rel_iff' := Subgroup.comap_le_comap_of_surjective mk'_surjective _

end CorrespTheorem

section trivial

@[to_additive]
/--
theorem `subsingleton_quotient_top` / 定理 `subsingleton_quotient_top`

English:
theorem subsingleton_quotient_top
  statement: Subsingleton (G ⧸ (⊤ : Subgroup G))
  proof: by
  simp

中文:
定理 subsingleton_quotient_top
  结论: Subsingleton (G ⧸ (⊤ : Subgroup G))
  证明: by
  simp
-/
theorem subsingleton_quotient_top : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  simp

/-- If the quotient by a subgroup gives a singleton then the subgroup is the whole group. -/
@[to_additive /-- If the quotient by an additive subgroup gives a singleton then the additive
subgroup is the whole additive group. -/]
/--
theorem `subgroup_eq_top_of_subsingleton` / 定理 `subgroup_eq_top_of_subsingleton`

English:
theorem subgroup_eq_top_of_subsingleton
  given: (H : Subgroup G) (h : Subsingleton (G ⧸ H))
  statement: H = ⊤
  proof: top_unique fun x _ => by
    have : 1⁻¹ * x in H := QuotientGroup.eq.1 (Subsingleton.elim _ _)
    rwa [inv_one, one_mul] at this

中文:
定理 subgroup_eq_top_of_subsingleton
  条件: (H : Subgroup G) (h : Subsingleton (G ⧸ H))
  结论: H = ⊤
  证明: top_unique fun x _ => by
    have : 1⁻¹ * x in H := QuotientGroup.eq.1 (Subsingleton.elim _ _)
    rwa [inv_one, one_mul] at this

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, Subsingleton, Subsingleton.elim, inv_one, one_mul, top_unique
-/
theorem subgroup_eq_top_of_subsingleton (H : Subgroup G) (h : Subsingleton (G ⧸ H)) : H = ⊤ :=
  top_unique fun x _ => by
    have : 1⁻¹ * x in H := QuotientGroup.eq.1 (Subsingleton.elim _ _)
    rwa [inv_one, one_mul] at this

end trivial

@[to_additive]
/--
theorem `comap_comap_center` / 定理 `comap_comap_center`

English:
theorem comap_comap_center
  given: {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal]
  proof: by
  ext x
  simp only [mk'_apply, Subgroup.mem_comap, Subgroup.mem_center_iff, forall_mk, ← mk_mul,
    eq_iff_div_mem, mk_div]

中文:
定理 comap_comap_center
  条件: {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal]
  证明: by
  ext x
  simp only [mk'_apply, Subgroup.mem_comap, Subgroup.mem_center_iff, forall_mk, ← mk_mul,
    eq_iff_div_mem, mk_div]

Depends on / 依赖: Subgroup, Subgroup.mem_center_iff, Subgroup.mem_comap, _apply, eq_iff_div_mem, forall_mk, mem_center_iff, mem_comap, mk_div, mk_mul
-/
theorem comap_comap_center {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal] :
    ((Subgroup.center ((G ⧸ H₁) ⧸ H₂)).comap (mk' H₂)).comap (mk' H₁) =
      (Subgroup.center (G ⧸ H₂.comap (mk' H₁))).comap (mk' (H₂.comap (mk' H₁))) := by
  ext x
  simp only [mk'_apply, Subgroup.mem_comap, Subgroup.mem_center_iff, forall_mk, ← mk_mul,
    eq_iff_div_mem, mk_div]

open Subgroup in
@[to_additive]
/--
theorem `_root_.Subgroup.Characteristic.comap_quotient_mk` / 定理 `_root_.Subgroup.Characteristic.comap_quotient_mk`

English:
theorem _root_.Subgroup.Characteristic.comap_quotient_mk
  statement: {H : Subgroup G} [hH : H.Characteristic]
  proof: characteristic_iff_comap_eq.mpr fun φ => congr_arg (comap (mk' H))
    (characteristic_iff_comap_eq.mp hK (congr H H φ (characteristic_iff_map_eq.mp hH φ)))

中文:
定理 _root_.Subgroup.Characteristic.comap_quotient_mk
  结论: {H : Subgroup G} [hH : H.Characteristic]
  证明: characteristic_iff_comap_eq.mpr fun φ => congr_arg (comap (mk' H))
    (characteristic_iff_comap_eq.mp hK (congr H H φ (characteristic_iff_map_eq.mp hH φ)))

Depends on / 依赖: characteristic_iff_comap_eq, characteristic_iff_comap_eq.mp, characteristic_iff_comap_eq.mpr, characteristic_iff_map_eq, characteristic_iff_map_eq.mp, congr_arg
-/
theorem _root_.Subgroup.Characteristic.comap_quotient_mk {H : Subgroup G} [hH : H.Characteristic]
    {K : Subgroup (G ⧸ H)} (hK : K.Characteristic) :
    Characteristic (K.comap (mk' H)) :=
  characteristic_iff_comap_eq.mpr fun φ => congr_arg (comap (mk' H))
    (characteristic_iff_comap_eq.mp hK (congr H H φ (characteristic_iff_map_eq.mp hH φ)))

/--
The `MulEquiv` between the kernel of the restriction map to a normal subgroup `H` of homomorphisms
of type `G →* A` and the group of homomorphisms `G ⧸ H →* A`.
-/
@[to_additive
/--
The `AddEquiv` between the kernel of the restriction map to a normal subgroup `H` of homomorphisms
of type `G →+ A` and the group of homomorphisms `G ⧸ H →+ A`.
-/]
/--
Definition of `_root_.MonoidHom.domRestrictHomKerEquiv` / `_root_.MonoidHom.domRestrictHomKerEquiv` 的定义

English:
definition _root_.MonoidHom.domRestrictHomKerEquiv
  signature: (A : Type*) [CommGroup A] (H : Subgroup G) [H.Normal]
  body: fun ⟨f, hf⟩ => QuotientGroup.lift _ f
    (by simpa [mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff] using! hf)
invFun f := ⟨f.comp (QuotientGroup.mk' H), domRestrict_eq_one_iff.mpr le_comap_mk' H f.ker⟩
  map_mul' _ _ := by ext; simp
  left_inv _ := by simp
  right_inv _ := by ext; simp

@[s

中文:
定义 _root_.MonoidHom.domRestrictHomKerEquiv
  签名: (A : 类型) [CommGroup A] (H : Subgroup G) [H.Normal]
  定义体: fun ⟨f, hf⟩ => QuotientGroup.lift _ f
    (by simpa [mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff] using! hf)
invFun f := ⟨f.comp (QuotientGroup.mk' H), domRestrict_eq_one_iff.mpr le_comap_mk' H f.ker⟩
  map_mul' _ _ := by ext; simp
  left_inv _ := by simp
  right_inv _ := by ext; simp

@[s

Depends on / 依赖: QuotientGroup, QuotientGroup.lift
-/
def _root_.MonoidHom.domRestrictHomKerEquiv (A : Type*) [CommGroup A] (H : Subgroup G) [H.Normal] :
    (MonoidHom.domRestrictHom H A).ker ≃* (G ⧸ H ->* A) where
  toFun := fun ⟨f, hf⟩ => QuotientGroup.lift _ f
    (by simpa [mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff] using! hf)
invFun f := ⟨f.comp (QuotientGroup.mk' H), domRestrict_eq_one_iff.mpr le_comap_mk' H f.ker⟩
  map_mul' _ _ := by ext; simp
  left_inv _ := by simp
  right_inv _ := by ext; simp

@[simp]
/--
theorem `_root_.MonoidHom.domRestrictHomKerEquiv_apply_coe` / 定理 `_root_.MonoidHom.domRestrictHomKerEquiv_apply_coe`

English:
theorem _root_.MonoidHom.domRestrictHomKerEquiv_apply_coe
  statement: (A : Type*) [CommGroup A] (H : Subgroup G)
  proof: rfl

@[simp]

中文:
定理 _root_.MonoidHom.domRestrictHomKerEquiv_apply_coe
  结论: (A : 类型) [CommGroup A] (H : Subgroup G)
  证明: rfl

@[simp]
-/
theorem _root_.MonoidHom.domRestrictHomKerEquiv_apply_coe (A : Type*) [CommGroup A] (H : Subgroup G)
    [H.Normal] (f : (MonoidHom.domRestrictHom H A).ker) (g : G) :
    domRestrictHomKerEquiv A H f g = f.val g := rfl

@[simp]
/--
theorem `_root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply` / 定理 `_root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply`

English:
theorem _root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply
  statement: (A : Type*) [CommGroup A]
  proof: rfl

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrictHomKerEquiv := _root_.MonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHomKerEquiv := _root_.AddMonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")] ali

中文:
定理 _root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply
  结论: (A : 类型) [CommGroup A]
  证明: rfl

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrictHomKerEquiv := _root_.MonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHomKerEquiv := _root_.AddMonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")] ali
-/
theorem _root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply (A : Type*) [CommGroup A]
    (H : Subgroup G) [H.Normal] (f : G ⧸ H ->* A) (g : G) :
    ((domRestrictHomKerEquiv A H).symm f).val g = f g := rfl

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrictHomKerEquiv := _root_.MonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHomKerEquiv := _root_.AddMonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")] alias _root_.MonoidHom.restrictHomKerEquiv_apply_coe :=
  _root_.MonoidHom.domRestrictHomKerEquiv_apply_coe
@[deprecated (since := "2026-07-19")] alias _root_.MonoidHom.restrictHomKerEquiv_symm_coe_apply :=
  _root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply

end QuotientGroup

namespace QuotientAddGroup

variable {R : Type*} [NonAssocRing R] (N : AddSubgroup R) [N.Normal]

@[simp]
/--
theorem `mk_nat_mul` / 定理 `mk_nat_mul`

English:
theorem mk_nat_mul
  given: (n : Nat) (a : R)
  statement: ((n * a : R) : R ⧸ N) = n • ↑a
  proof: by
  rw [← nsmul_eq_mul]; rw [mk_nsmul N a n]

@[simp]

中文:
定理 mk_nat_mul
  条件: (n : 自然数) (a : R)
  结论: ((n * a : R) : R ⧸ N) = n • ↑a
  证明: by
  rw [← nsmul_eq_mul]; rw [mk_nsmul N a n]

@[simp]

Depends on / 依赖: mk_nsmul, nsmul_eq_mul
-/
theorem mk_nat_mul (n : Nat) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a := by
  rw [← nsmul_eq_mul]; rw [mk_nsmul N a n]

@[simp]
/--
theorem `mk_int_mul` / 定理 `mk_int_mul`

English:
theorem mk_int_mul
  given: (n : Int) (a : R)
  statement: ((n * a : R) : R ⧸ N) = n • ↑a
  proof: by
  rw [← zsmul_eq_mul]; rw [mk_zsmul N a n]

中文:
定理 mk_int_mul
  条件: (n : 整数) (a : R)
  结论: ((n * a : R) : R ⧸ N) = n • ↑a
  证明: by
  rw [← zsmul_eq_mul]; rw [mk_zsmul N a n]

Depends on / 依赖: mk_zsmul, zsmul_eq_mul
-/
theorem mk_int_mul (n : Int) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a := by
  rw [← zsmul_eq_mul]; rw [mk_zsmul N a n]

end QuotientAddGroup

namespace QuotientGroup

section powMonoidHom

-- TODO: Generalize to arbitrary products of homomorphisms

variable {ι : Type*} (A : ι -> Type*) [forall i, CommGroup (A i)] (n : Nat)

/-- The isomorphism between the quotient of a product by the image of the `n`th power map
and the product of the quotients by the images of the `n`th power maps on the factors. -/
@[to_additive
  /-- The isomorphism between the quotient of a product by the image of the multiplication-by-`n`
  map and the product of the quotients by the images of the multiplication-by-`n` maps
  on the factors. -/ ]
noncomputable
/--
Definition of `mulEquivPiModRangePowMonoidHom` / `mulEquivPiModRangePowMonoidHom` 的定义

English:
definition mulEquivPiModRangePowMonoidHom
  signature: :
  body: let φ : ((i : ι) -> A i) ->* (i : ι) -> A i ⧸ (powMonoidHom n).range := {
    toFun x := (x ·)
    map_one' := by simp [Pi.one_def]
    map_mul' x y := by simp [Pi.mul_def]
  }
liftEquiv (φ := φ) _ (fun y => ⟨fun i => Quotient.out (y i), by simp [φ]⟩) by
    ext x : 1
    simpa [φ, funext_iff] using

中文:
定义 mulEquivPiModRangePowMonoidHom
  签名: :
  定义体: let φ : ((i : ι) -> A i) ->* (i : ι) -> A i ⧸ (powMonoidHom n).range := {
    toFun x := (x ·)
    map_one' := by simp [Pi.one_def]
    map_mul' x y := by simp [Pi.mul_def]
  }
liftEquiv (φ := φ) _ (fun y => ⟨fun i => Quotient.out (y i), by simp [φ]⟩) by
    ext x : 1
    simpa [φ, funext_iff] using

Depends on / 依赖: Classical, Classical.skolem, Pi.mul_def, Pi.one_def, Quotient, Quotient.out, funext_iff, liftEquiv, map_mul, map_one, mul_def, one_def, powMonoidHom, skolem
-/
def mulEquivPiModRangePowMonoidHom :
    ((i : ι) -> A i) ⧸ (powMonoidHom n).range ≃* ((i : ι) -> A i ⧸ (powMonoidHom n).range) :=
  let φ : ((i : ι) -> A i) ->* (i : ι) -> A i ⧸ (powMonoidHom n).range := {
    toFun x := (x ·)
    map_one' := by simp [Pi.one_def]
    map_mul' x y := by simp [Pi.mul_def]
  }
liftEquiv (φ := φ) _ (fun y => ⟨fun i => Quotient.out (y i), by simp [φ]⟩) by
    ext x : 1
    simpa [φ, funext_iff] using (Classical.skolem (p := fun i a => a ^ n = x i)).symm

@[to_additive (attr := simp)]
/--
lemma `mulEquivPiModRangePowMonoidHom_apply` / 引理 `mulEquivPiModRangePowMonoidHom_apply`

English:
lemma mulEquivPiModRangePowMonoidHom_apply
  given: (x : (i : ι) -> A i)
  proof: rfl

中文:
引理 mulEquivPiModRangePowMonoidHom_apply
  条件: (x : (i : ι) -> A i)
  证明: rfl
-/
lemma mulEquivPiModRangePowMonoidHom_apply (x : (i : ι) -> A i) :
    mulEquivPiModRangePowMonoidHom A n ↑x = fun i => ↑(x i) :=
  rfl

end powMonoidHom

end QuotientGroup
