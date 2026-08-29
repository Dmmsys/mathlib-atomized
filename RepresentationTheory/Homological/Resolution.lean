/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# The standard and bar resolutions of `k` as a trivial `k`-linear `G`-representation

Given a commutative ring `k` and a group `G`, this file defines two projective resolutions of `k`
as a trivial `k`-linear `G`-representation.

The first one, the standard resolution, has objects `k[Gⁿ⁺¹]` equipped with the diagonal
representation, and differential defined by `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`.

We define this as the alternating face map complex associated to an appropriate simplicial
`k`-linear `G`-representation. This simplicial object is the `linearization` of the simplicial
`G`-set given by the universal cover of the classifying space of `G`, `EG`. We prove this
simplicial `G`-set `EG` is isomorphic to the Čech nerve of the natural arrow of `G`-sets
`G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `Rep.standardResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

We then construct the bar resolution. The `n`th object in this complex is the representation on
`Gⁿ →₀ k[G]` defined pointwise by the left regular representation on `k[G]`. The differentials are
defined by sending `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`.

In `RepresentationTheory.Rep` we define an isomorphism `Rep.diagonalSuccIsoFree` between
`k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ) ↦ g₀·(g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ)`.
We show that this isomorphism defines a commutative square with the bar resolution differential and
the standard resolution differential, and thus conclude that the bar resolution differential
squares to zero and that `Rep.diagonalSuccIsoFree` defines an isomorphism between the two
complexes. We carry the exactness properties across this isomorphism to conclude the bar resolution
is a projective resolution too, in `Rep.barResolution`.

In `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`, we then use
`Rep.barResolution` to define the inhomogeneous (co)chains of a representation, useful for
computing group (co)homology.

## Main definitions

* `groupCohomology.resolution.ofMulActionBasis`
* `classifyingSpaceUniversalCover`
* `Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv`
* `Rep.standardResolution`

TODO: There's bad DefEq abuses in `Action` and the way we do `Rep.standardComplex` should be
  unified with continuous cohomology, therefore we should remove the use of `Action` in `Rep` which
  would remove all the unification hints in this file.
-/

@[expose] public noncomputable section

suppress_compilation

open CategoryTheory Finsupp
open scoped MonoidAlgebra

universe u v w

variable {k G : Type u} [CommRing k] {n : Nat}

local notation "Gⁿ" => Fin n -> G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) -> G

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
@[simps obj map]
/--
Definition of `classifyingSpaceUniversalCover` / `classifyingSpaceUniversalCover` 的定义

English:
definition classifyingSpaceUniversalCover
  signature: [Monoid G]
  body: Action.ofMulAction G (Fin (n.unop.len + 1) -> G)
  map f :=
    { hom := ↾fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

中文:
定义 classifyingSpaceUniversalCover
  签名: [幺半群 G]
  定义体: Action.ofMulAction G (Fin (n.unop.len + 1) -> G)
  map f :=
    { hom := ↾fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

Depends on / 依赖: Action, Action.ofMulAction, n.unop.len, ofMulAction
-/
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) -> G)
  map f :=
    { hom := ↾fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

namespace classifyingSpaceUniversalCover

open CategoryTheory.Limits

variable [Monoid G]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cechNerveTerminalFromIso` / `cechNerveTerminalFromIso` 的定义

English:
definition cechNerveTerminalFromIso
  signature: : cechNerveTerminalFrom (Action.ofMulAction G (G)) ≅
  body: NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc]; rw [limit.isoLimitCone_hom_π]; rw [limit

中文:
定义 cechNerveTerminalFromIso
  签名: : cechNerveTerminalFrom (作用.ofMulAction G (G)) ≅
  定义体: NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc]; rw [limit.isoLimitCone_hom_π]; rw [limit

Depends on / 依赖: Action, Action.ofMulActionLimitCone, Category, Category.assoc, IsLimit, IsLimit.hom_ext, NatIso, NatIso.ofComponents, Pi.lift, cechNerveTerminalFrom, hom_ext, isoLimitCone, limit.isoLimitCone, limit.isoLimitCone_hom_, limit.lift_, ofComponents, ofMulActionLimitCone
-/
def cechNerveTerminalFromIso : cechNerveTerminalFrom (Action.ofMulAction G (G)) ≅
    classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc]; rw [limit.isoLimitCone_hom_π]; rw [limit.lift_π]; rw [Category.assoc]
    exact (limit.isoLimitCone_hom_π _ _).symm

/--
Definition of `cechNerveTerminalFromIsoCompForget` / `cechNerveTerminalFromIsoCompForget` 的定义

English:
definition cechNerveTerminalFromIsoCompForget
  signature: :
  body: by
  refine NatIso.ofComponents (fun _ => Types.productIso _) fun _ => ?_
  ext : 2
  exact Matrix.ext fun _ _ => Pi.lift_π_apply (f := fun _ => G) _ _ _

中文:
定义 cechNerveTerminalFromIsoCompForget
  签名: :
  定义体: by
  refine NatIso.ofComponents (fun _ => Types.productIso _) fun _ => ?_
  ext : 2
  exact Matrix.ext fun _ _ => Pi.lift_π_apply (f := fun _ => G) _ _ _

Depends on / 依赖: Matrix, Matrix.ext, NatIso, NatIso.ofComponents, Pi.lift_, Types.productIso, ofComponents, productIso
-/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ := by
  refine NatIso.ofComponents (fun _ => Types.productIso _) fun _ => ?_
  ext : 2
  exact Matrix.ext fun _ _ => Pi.lift_π_apply (f := fun _ => G) _ _ _

variable (k)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/--
Definition of `compForgetAugmented` / `compForgetAugmented` 的定义

English:
definition compForgetAugmented
  signature: : SimplicialObject.Augmented (Type u)
  body: SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _

中文:
定义 compForgetAugmented
  签名: : SimplicialObject.Augmented (类型u)
  定义体: SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _

Depends on / 依赖: SimplicialObject, SimplicialObject.augment, Subsingleton, Subsingleton.elim, augment, classifyingSpaceUniversalCover, forget, terminal, terminal.from
-/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `extraDegeneracyAugmentedCechNerve` / `extraDegeneracyAugmentedCechNerve` 的定义

English:
definition extraDegeneracyAugmentedCechNerve
  signature: :
  body: AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨↾fun _ => (1 : G), by cat_disch⟩

中文:
定义 extraDegeneracyAugmentedCechNerve
  签名: :
  定义体: AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨↾fun _ => (1 : G), by cat_disch⟩

Depends on / 依赖: Arrow.mk, AugmentedCechNerve, AugmentedCechNerve.extraDegeneracy, cat_disch, extraDegeneracy, terminal, terminal.from
-/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨↾fun _ => (1 : G), by cat_disch⟩

/--
Definition of `extraDegeneracyCompForgetAugmented` / `extraDegeneracyCompForgetAugmented` 的定义

English:
definition extraDegeneracyCompForgetAugmented
  signature: : ExtraDegeneracy (compForgetAugmented G)
  body: by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext termina

中文:
定义 extraDegeneracyCompForgetAugmented
  签名: : ExtraDegeneracy (compForgetAugmented G)
  定义体: by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext termina

Depends on / 依赖: Arrow.mk, CechNerveTerminalFrom, CechNerveTerminalFrom.iso, Comma.isoMk, ExtraDegeneracy, ExtraDegeneracy.ofIso, IsTerminal, IsTerminal.hom_ext, Iso.refl, augmentedCechNerve, cechNerveTerminalFromIsoCompForget, extraDegeneracyAugmentedCechNerve, hom_ext, terminal, terminal.from, terminalIsTerminal
-/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext terminalIsTerminal _ _)

/--
Definition of `compForgetAugmented.toModule` / `compForgetAugmented.toModule` 的定义

English:
definition compForgetAugmented.toModule
  signature: : SimplicialObject.Augmented (ModuleCat.{u} k)
  body: ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.monoidAlgebraFree k)).obj
    (compForgetAugmented G)

中文:
定义 compForgetAugmented.toModule
  签名: : SimplicialObject.Augmented (模范畴.{u} k)
  定义体: ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.monoidAlgebraFree k)).obj
    (compForgetAugmented G)

Depends on / 依赖: Augmented, ModuleCat, ModuleCat.monoidAlgebraFree, SimplicialObject, SimplicialObject.Augmented.whiskering, compForgetAugmented, monoidAlgebraFree, whiskering
-/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.monoidAlgebraFree k)).obj
    (compForgetAugmented G)

/--
Definition of `extraDegeneracyCompForgetAugmentedToModule` / `extraDegeneracyCompForgetAugmentedToModule` 的定义

English:
definition extraDegeneracyCompForgetAugmentedToModule
  signature: :
  body: .map (extraDegeneracyCompForgetAugmented G) (ModuleCat.monoidAlgebraFree k)

中文:
定义 extraDegeneracyCompForgetAugmentedToModule
  签名: :
  定义体: .map (extraDegeneracyCompForgetAugmented G) (ModuleCat.monoidAlgebraFree k)

Depends on / 依赖: ModuleCat, ModuleCat.monoidAlgebraFree, extraDegeneracyCompForgetAugmented, monoidAlgebraFree
-/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  .map (extraDegeneracyCompForgetAugmented G) (ModuleCat.monoidAlgebraFree k)

end classifyingSpaceUniversalCover

variable (k)

/--
Definition of `Rep.standardComplex` / `Rep.standardComplex` 的定义

English:
definition Rep.standardComplex
  signature: [Monoid G]
  body: (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ linearization k G)

中文:
定义 Rep.standardComplex
  签名: [幺半群 G]
  定义体: (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ linearization k G)

Depends on / 依赖: AlgebraicTopology, AlgebraicTopology.alternatingFaceMapComplex, alternatingFaceMapComplex, classifyingSpaceUniversalCover, linearization
-/
def Rep.standardComplex [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ linearization k G)

namespace Rep.standardComplex

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory.Limits

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (G : Type u) (n : Nat)
  body: (Finsupp.lift k[Fin n -> G] k (Fin (n + 1) -> G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      .single (g ∘ p.succAbove) ((-1 : k) ^ (p : Nat))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

中文:
定义 d
  签名: (G : 类型u) (n : 自然数)
  定义体: (Finsupp.lift k[Fin n -> G] k (Fin (n + 1) -> G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      .single (g ∘ p.succAbove) ((-1 : k) ^ (p : Nat))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

Depends on / 依赖: Finset, Finset.univ, Finsupp, Finsupp.lift, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, coeffLinearEquiv, p.succAbove, single, succAbove, toLinearMap
-/
def d (G : Type u) (n : Nat) : k[Fin (n + 1) -> G] ->ₗ[k] k[Fin n -> G] :=
  (Finsupp.lift k[Fin n -> G] k (Fin (n + 1) -> G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      .single (g ∘ p.succAbove) ((-1 : k) ^ (p : Nat))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

variable {k G}

@[simp]
/--
theorem `d_of` / 定理 `d_of`

English:
theorem d_of
  given: {n : Nat} (c : Fin (n + 1) -> G)
  proof: by
  simp [d]

中文:
定理 d_of
  条件: {n : 自然数} (c : 有限集 (n + 1) -> G)
  证明: by
  simp [d]
-/
theorem d_of {n : Nat} (c : Fin (n + 1) -> G) :
    d k G n (.single c 1) = ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) ((-1 : k) ^ p.val) := by
  simp [d]

/--
lemma `d_single` / 引理 `d_single`

English:
lemma d_single
  given: {n : Nat} (c : Fin (n + 1) -> G) (r : k)
  proof: by
  rw [← mul_one r]; rw [← smul_eq_mul]; rw [← MonoidAlgebra.smul_single]; rw [map_smul]; rw [d_of]
  simp [Finset.smul_sum]

中文:
引理 d_single
  条件: {n : 自然数} (c : 有限集 (n + 1) -> G) (r : k)
  证明: by
  rw [← mul_one r]; rw [← smul_eq_mul]; rw [← MonoidAlgebra.smul_single]; rw [map_smul]; rw [d_of]
  simp [Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, MonoidAlgebra, MonoidAlgebra.smul_single, d_of, map_smul, mul_one, smul_eq_mul, smul_single, smul_sum
-/
lemma d_single {n : Nat} (c : Fin (n + 1) -> G) (r : k) :
    d k G n (.single c r) =
      ∑ p : Fin (n + 1), .single (c ∘ p.succAbove) (r * (-1 : k) ^ p.val) := by
  rw [← mul_one r]; rw [← smul_eq_mul]; rw [← MonoidAlgebra.smul_single]; rw [map_smul]; rw [d_of]
  simp [Finset.smul_sum]

variable (k G) [Monoid G]

/--
Definition of `xIso` / `xIso` 的定义

English:
definition xIso
  signature: (n : Nat)
  body: Iso.refl _

中文:
定义 xIso
  签名: (n : 自然数)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def xIso (n : Nat) : (standardComplex k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) -> G) :=
  Iso.refl _

/--
Instance `x_projective` / 实例 `x_projective`

English:
instance x_projective
  signature: (G : Type u) [Group G] (n : Nat)
  body: by
exact inferInstanceAs Projective (Rep.diagonal k G (n + 1))

中文:
实例 x_projective
  签名: (G : 类型u) [群 G] (n : 自然数)
  定义体: by
exact inferInstanceAs Projective (Rep.diagonal k G (n + 1))

Depends on / 依赖: Projective, Rep.diagonal, diagonal
-/
instance x_projective (G : Type u) [Group G] (n : Nat) :
    Projective ((standardComplex k G).X n) := by
exact inferInstanceAs Projective (Rep.diagonal k G (n + 1))

set_option backward.defeqAttrib.useBackward true in
unif_hint where ⊢ Action.V (Action.ofMulAction G (Fin (n + 1) -> G)) ≟ Fin (n + 1) -> G in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `d_eq` / 定理 `d_eq`

English:
theorem d_eq
  given: (n : Nat)
  statement: ((standardComplex k G).d (n + 1) n).hom.toLinearMap =
  proof: by
  refine MonoidAlgebra.lhom_ext' fun (x : Fin (n + 2) -> G) => LinearMap.ext_ring ?_
  simp [standardComplex, Action.ofMulAction_V, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : Int), ← ofHom_smul, ← ofHom_sum,
    Representation.Intertwi

中文:
定理 d_eq
  条件: (n : 自然数)
  结论: ((standardComplex k G).d (n + 1) n).hom.toLinearMap =
  证明: by
  refine MonoidAlgebra.lhom_ext' fun (x : Fin (n + 2) -> G) => LinearMap.ext_ring ?_
  simp [standardComplex, Action.ofMulAction_V, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : Int), ← ofHom_smul, ← ofHom_sum,
    Representation.Intertwi

Depends on / 依赖: Action, Action.ofMulAction_V, Fin.succAboveOrderEmb, Int.cast_smul_eq_zsmul, IntertwiningMap, LinearMap, LinearMap.ext_ring, MonoidAlgebra, MonoidAlgebra.lhom_ext, Representation, Representation.IntertwiningMap.coe_toLinearMap, Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.sum_apply, Representation.linearizeMap_single, SimplexCategory, SimplicialObject, cast_smul_eq_zsmul, coe_toLinearMap, ext_ring, lhom_ext
-/
theorem d_eq (n : Nat) : ((standardComplex k G).d (n + 1) n).hom.toLinearMap =
    d k G (n + 1) := by
  refine MonoidAlgebra.lhom_ext' fun (x : Fin (n + 2) -> G) => LinearMap.ext_ring ?_
  simp [standardComplex, Action.ofMulAction_V, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : Int), ← ofHom_smul, ← ofHom_sum,
    Representation.IntertwiningMap.coe_toLinearMap, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, (Representation.linearizeMap_single),
    smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `d_apply` / 引理 `d_apply`

English:
lemma d_apply
  given: {n : Nat} (f : k[Fin (n + 1 + 1) -> G])
  proof: by
  rw [← Representation.IntertwiningMap.toLinearMap_apply]; rw [d_eq]; rfl

中文:
引理 d_apply
  条件: {n : 自然数} (f : k[有限集 (n + 1 + 1) -> G])
  证明: by
  rw [← Representation.IntertwiningMap.toLinearMap_apply]; rw [d_eq]; rfl

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.toLinearMap_apply, d_eq, toLinearMap_apply
-/
lemma d_apply {n : Nat} (f : k[Fin (n + 1 + 1) -> G]) :
    ((standardComplex k G).d (n + 1) n).hom f = d k G (n + 1) f := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply]; rw [d_eq]; rfl

section Exactness

/--
Definition of `forget₂ToModuleCat` / `forget₂ToModuleCat` 的定义

English:
definition forget₂ToModuleCat
  body: ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj (standardComplex k G)

中文:
定义 forget₂ToModuleCat
  定义体: ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj (standardComplex k G)

Depends on / 依赖: ModuleCat, mapHomologicalComplex, standardComplex
-/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj (standardComplex k G)

/--
Definition of `compForgetAugmentedIso` / `compForgetAugmentedIso` 的定义

English:
definition compForgetAugmentedIso
  signature: :
  body: eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ linearization k G))

中文:
定义 compForgetAugmentedIso
  签名: :
  定义体: eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ linearization k G))

Depends on / 依赖: Functor, Functor.congr_obj, ModuleCat, classifyingSpaceUniversalCover, congr_obj, eqToIso, linearization, map_alternatingFaceMapComplex
-/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      standardComplex.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ linearization k G))

/--
Definition of `forget₂ToModuleCatHomotopyEquiv` / `forget₂ToModuleCatHomotopyEquiv` 的定义

English:
definition forget₂ToModuleCatHomotopyEquiv
  signature: :
  body: (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (letI : Unique

中文:
定义 forget₂ToModuleCatHomotopyEquiv
  签名: :
  定义体: (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (letI : Unique

Depends on / 依赖: Augmented, ChainComplex, ChainComplex.single, ExtraDegeneracy, Finsupp, Finsupp.uniqueLinearEquiv, HomotopyEquiv, HomotopyEquiv.ofIso, ModuleCat, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, SimplicialObject, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, Types.terminalIso.toEquiv.unique, Unique, coeffLinearEquiv, compForgetAugmentedIso, extraDegeneracyCompForgetAugmentedToModule, homotopyEquiv, mapIso
-/
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (standardComplex.forget₂ToModuleCat k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
(HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (letI : Unique (⊤_ Type u) := Types.terminalIso.toEquiv.unique
           ((MonoidAlgebra.coeffLinearEquiv k (M := ⊤_ Type u)).trans
             (Finsupp.uniqueLinearEquiv k k default)).toModuleIso))

/--
Definition of `ε` / `ε` 的定义

English:
definition ε
  signature: : Rep.ofMulAction k G (Fin 1 -> G) ⟶ Rep.trivial k G k
  body: ofHom
  ⟨(Finsupp.linearCombination _ fun _ => (1 : k)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap,
fun _ => MonoidAlgebra.lhom_ext' fun _ => LinearMap.ext_ring by simp⟩

中文:
定义 ε
  签名: : Rep.ofMulAction k G (有限集 1 -> G) ⟶ Rep.trivial k G k
  定义体: ofHom
  ⟨(Finsupp.linearCombination _ fun _ => (1 : k)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap,
fun _ => MonoidAlgebra.lhom_ext' fun _ => LinearMap.ext_ring by simp⟩
-/
def ε : Rep.ofMulAction k G (Fin 1 -> G) ⟶ Rep.trivial k G k := ofHom
  ⟨(Finsupp.linearCombination _ fun _ => (1 : k)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap,
fun _ => MonoidAlgebra.lhom_ext' fun _ => LinearMap.ext_ring by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `forget₂ToModuleCatHomotopyEquiv_f_0_eq` / 定理 `forget₂ToModuleCatHomotopyEquiv_f_0_eq`

English:
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq
  proof: by
refine ModuleCat.hom_ext MonoidAlgebra.lhom_ext' fun (x : Fin 1 -> G) => LinearMap.ext_ring ?_
  simp [forget₂ToModuleCatHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, ChainComplex.single₀_map_f_zero,
    AlgebraicTopology.Al

中文:
定理 forget₂ToModuleCatHomotopyEquiv_f_0_eq
  证明: by
refine ModuleCat.hom_ext MonoidAlgebra.lhom_ext' fun (x : Fin 1 -> G) => LinearMap.ext_ring ?_
  simp [forget₂ToModuleCatHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, ChainComplex.single₀_map_f_zero,
    AlgebraicTopology.Al

Depends on / 依赖: AlgebraicTopology, AlgebraicTopology.AlternatingFaceMapComplex, AlternatingFaceMapComplex, Augmented, ChainComplex, ChainComplex.single, ExtraDegeneracy, HomologicalComplex, HomologicalComplex.eqToHom_f, HomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans, LinearMap, LinearMap.ext_ring, ModuleCat, ModuleCat.hom_ext, MonoidAlgebra, MonoidAlgebra.lhom_ext, SimplicialObject, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
-/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
refine ModuleCat.hom_ext MonoidAlgebra.lhom_ext' fun (x : Fin 1 -> G) => LinearMap.ext_ring ?_
  simp [forget₂ToModuleCatHomotopyEquiv, HomotopyEquiv.ofIso, HomotopyEquiv.trans,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, ChainComplex.single₀_map_f_zero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero, compForgetAugmentedIso, eqToIso.inv,
    HomologicalComplex.eqToHom_f, compForgetAugmented, compForgetAugmented.toModule, ε,
    SimplicialObject.augment, Unique.eq_default (terminal.from _), MonoidAlgebra.coeff_single,
    Finsupp.single_apply, if_pos (Subsingleton.elim _ _)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `d_comp_ε` / 定理 `d_comp_ε`

English:
theorem d_comp_ε
  statement: (standardComplex k G).d 1 0 ≫ ε k G = 0
  proof: by
  ext : 3
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq]; rw [← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.

中文:
定理 d_comp_ε
  结论: (standardComplex k G).d 1 0 ≫ ε k G = 0
  证明: by
  ext : 3
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq]; rw [← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ModuleCat, ModuleCat.hom_ext_iff.mp, comp_zero, ext_iff, hom_ext_iff
-/
theorem d_comp_ε : (standardComplex k G).d 1 0 ≫ ε k G = 0 := by
  ext : 3
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq]; rw [← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp this) _

/--
Definition of `εToSingle₀` / `εToSingle₀` 的定义

English:
definition εToSingle₀
  signature: :
  body: ((standardComplex k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

中文:
定义 εToSingle₀
  签名: :
  定义体: ((standardComplex k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

Depends on / 依赖: standardComplex
-/
def εToSingle₀ :
    standardComplex k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((standardComplex k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `εToSingle₀_comp_eq` / 定理 `εToSingle₀_comp_eq`

English:
theorem εToSingle₀_comp_eq
  proof: by
  dsimp
  ext1
  simpa using! (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm

中文:
定理 εToSingle₀_comp_eq
  证明: by
  dsimp
  ext1
  simpa using! (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm
-/
theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (forget₂ToModuleCatHomotopyEquiv k G).hom := by
  dsimp
  ext1
  simpa using! (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm

/--
theorem `quasiIso_forget₂_εToSingle₀` / 定理 `quasiIso_forget₂_εToSingle₀`

English:
theorem quasiIso_forget₂_εToSingle₀
  proof: by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)

中文:
定理 quasiIso_forget₂_εToSingle₀
  证明: by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)

Depends on / 依赖: QuasiIso, quasiIso_of_comp_right
-/
theorem quasiIso_forget₂_εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso (εToSingle₀ k G)
  body: by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

中文:
实例 :
  签名: 拟同构 (εToSingle₀ k G)
  定义体: by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso_map_iff_of_preservesHomology, ModuleCat, quasiIso_map_iff_of_preservesHomology
-/
instance : QuasiIso (εToSingle₀ k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

end Exactness
end standardComplex

open HomologicalComplex.Hom standardComplex

variable [Group G]

/--
Definition of `standardResolution` / `standardResolution` 的定义

English:
definition standardResolution
  signature: : ProjectiveResolution (Rep.trivial k G k) where
  body: standardComplex k G
  π := εToSingle₀ k G

中文:
定义 standardResolution
  签名: : 投射消解 (Rep.trivial k G k) where
  定义体: standardComplex k G
  π := εToSingle₀ k G

Depends on / 依赖: standardComplex
-/
def standardResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := standardComplex k G
  π := εToSingle₀ k G

/--
Definition of `standardResolution.extIso` / `standardResolution.extIso` 的定义

English:
definition standardResolution.extIso
  signature: (V : Rep k G) (n : Nat)
  body: (standardResolution k G).isoExt n V

中文:
定义 standardResolution.extIso
  签名: (V : Rep k G) (n : 自然数)
  定义体: (standardResolution k G).isoExt n V

Depends on / 依赖: isoExt, standardResolution
-/
def standardResolution.extIso (V : Rep k G) (n : Nat) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((standardComplex k G).linearYonedaObj k V).homology n :=
  (standardResolution k G).isoExt n V

namespace barComplex

open Rep Finsupp

variable (n)

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: : free k G Gⁿ⁺¹ ⟶ free k G Gⁿ
  body: freeLift k G _ fun g => single (fun i => g i.succ) (.single (g 0) 1) +
    ∑ j : Fin (n + 1), single (j.contractNth (· * ·) g) (.single (1 : G) ((-1 : k) ^ (j.val + 1)))

中文:
定义 d
  签名: : free k G Gⁿ⁺¹ ⟶ free k G Gⁿ
  定义体: freeLift k G _ fun g => single (fun i => g i.succ) (.single (g 0) 1) +
    ∑ j : Fin (n + 1), single (j.contractNth (· * ·) g) (.single (1 : G) ((-1 : k) ^ (j.val + 1)))

Depends on / 依赖: contractNth, freeLift, i.succ, j.contractNth, j.val, single
-/
def d : free k G Gⁿ⁺¹ ⟶ free k G Gⁿ :=
  freeLift k G _ fun g => single (fun i => g i.succ) (.single (g 0) 1) +
    ∑ j : Fin (n + 1), single (j.contractNth (· * ·) g) (.single (1 : G) ((-1 : k) ^ (j.val + 1)))

variable {k G} in
/--
lemma `d_single` / 引理 `d_single`

English:
lemma d_single
  given: (x : Gⁿ⁺¹)
  proof: by
  simp [d, ← Representation.IntertwiningMap.toLinearMap_apply]

中文:
引理 d_single
  条件: (x : Gⁿ⁺¹)
  证明: by
  simp [d, ← Representation.IntertwiningMap.toLinearMap_apply]

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.toLinearMap_apply, toLinearMap_apply
-/
lemma d_single (x : Gⁿ⁺¹) :
    (d k G n).hom (single x (.single 1 1)) = single (fun i => x i.succ) (.single (x 0) 1) +
      ∑ j : Fin (n + 1),
        single (j.contractNth (· * ·) x) (.single (1 : G) ((-1 : k) ^ (j.val + 1))) := by
  simp [d, ← Representation.IntertwiningMap.toLinearMap_apply]

set_option backward.defeqAttrib.useBackward true in
unif_hint (X : Type*) where ⊢ Action.V (Action.trivial G X) ≟ X in
unif_hint where ⊢ (HomologicalComplex.X (standardComplex k G) n).V ≟ k[Fin (n + 1) -> G] in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `d_comp_diagonalSuccIsoFree_inv_eq` / 引理 `d_comp_diagonalSuccIsoFree_inv_eq`

English:
lemma d_comp_diagonalSuccIsoFree_inv_eq
  proof: free_ext k G _ _ _ fun i => by
    have eq3 : MonoidAlgebra.single (i 0 • Fin.partialProd fun i_1 => i i_1.succ) (1 : k) =
        MonoidAlgebra.single (Fin.partialProd i ∘ Fin.succ) 1 := by
.symm congr; exact funext fun j => Fin.partialProd_succ' i j
    simp only [Rep.hom_comp, Representation.Inte

中文:
引理 d_comp_diagonalSuccIsoFree_inv_eq
  证明: free_ext k G _ _ _ fun i => by
    have eq3 : MonoidAlgebra.single (i 0 • Fin.partialProd fun i_1 => i i_1.succ) (1 : k) =
        MonoidAlgebra.single (Fin.partialProd i ∘ Fin.succ) 1 := by
.symm congr; exact funext fun j => Fin.partialProd_succ' i j
    simp only [Rep.hom_comp, Representation.Inte

Depends on / 依赖: Fin.partialProd, Fin.partialProd_succ, Fin.succ, IntertwiningMap, MonoidAlgebra, MonoidAlgebra.single, Rep.hom_comp, Representation, Representation.IntertwiningMap.comp_apply, comp_apply, d_single, free_ext, hom_comp, i_1.succ, map_add, map_sum, partialProd, partialProd_succ, single
-/
lemma d_comp_diagonalSuccIsoFree_inv_eq :
    d k G n ≫ (diagonalSuccIsoFree k G n).inv =
      (diagonalSuccIsoFree k G (n + 1)).inv ≫ (standardComplex k G).d (n + 1) n :=
  free_ext k G _ _ _ fun i => by
    have eq3 : MonoidAlgebra.single (i 0 • Fin.partialProd fun i_1 => i i_1.succ) (1 : k) =
        MonoidAlgebra.single (Fin.partialProd i ∘ Fin.succ) 1 := by
.symm congr; exact funext fun j => Fin.partialProd_succ' i j
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    rw [d_single (k := k)]; rw [map_add]; rw [map_sum]
    -- in-context `have`: at `Action` carriers, only locally re-elaborated statements key-match
    have H : forall (m : Nat) (f : Fin m -> G) (g : G) (r : k),
        (diagonalSuccIsoFree k G m).inv.hom (single f (MonoidAlgebra.single g r)) =
          MonoidAlgebra.single (g • Fin.partialProd f) r := by
      intro m f g r
      simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
        Representation.IntertwiningMap.comp_apply]
      have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m -> G)).inv)
          (single f (.single g r)) = .single g 1 otimesₜ[k] .single f r :=
        Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
      rw [step1]
      simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
        LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
        Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
        MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
        Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
        Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
      have key₁ := Representation.linearizeMap_single (k := k)
        (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
      have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
        (X := Action.leftRegular G) (Y := Action.trivial G (Fin m -> G)) g f 1 r
      exact ((congrArg (fun z => (Representation.linearizeMap
        (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)
    simp only [H, one_smul]
    simp [d_apply (k := k), Fin.partialProd_contractNth, Fin.sum_univ_succ, eq3]

end barComplex

open barComplex

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `barComplex` / `barComplex` 的定义

English:
abbreviation barComplex
  signature: : ChainComplex (Rep k G) Nat
  body: ChainComplex.of (fun n => free k G (Fin n -> G)) (fun n => d k G n) fun m => by
    have key : (d k G (m + 1) ≫ d k G m) ≫ (diagonalSuccIsoFree k G m).inv = 0 := by
      rw [Category.assoc]; rw [d_comp_diagonalSuccIsoFree_inv_eq]; rw [← Category.assoc]; rw [d_comp_diagonalSuccIsoFree_inv_eq]; rw [C

中文:
缩写 barComplex
  签名: : 链复形 (Rep k G) 自然数
  定义体: ChainComplex.of (fun n => free k G (Fin n -> G)) (fun n => d k G n) fun m => by
    have key : (d k G (m + 1) ≫ d k G m) ≫ (diagonalSuccIsoFree k G m).inv = 0 := by
      rw [Category.assoc]; rw [d_comp_diagonalSuccIsoFree_inv_eq]; rw [← Category.assoc]; rw [d_comp_diagonalSuccIsoFree_inv_eq]; rw [C

Depends on / 依赖: Category, Category.assoc, ChainComplex, ChainComplex.of, HomologicalComplex, HomologicalComplex.d_comp_d, Limits, Limits.comp_zero, cancel_mono, comp_zero, d_comp_d, d_comp_diagonalSuccIsoFree_inv_eq, diagonalSuccIsoFree
-/
noncomputable abbrev barComplex : ChainComplex (Rep k G) Nat :=
  ChainComplex.of (fun n => free k G (Fin n -> G)) (fun n => d k G n) fun m => by
    have key : (d k G (m + 1) ≫ d k G m) ≫ (diagonalSuccIsoFree k G m).inv = 0 := by
      rw [Category.assoc]; rw [d_comp_diagonalSuccIsoFree_inv_eq]; rw [← Category.assoc]; rw [d_comp_diagonalSuccIsoFree_inv_eq]; rw [Category.assoc]; rw [HomologicalComplex.d_comp_d]; rw [Limits.comp_zero]
    exact (cancel_mono (diagonalSuccIsoFree k G m).inv).mp (by simpa using key)

namespace barComplex

/--
theorem `d_def` / 定理 `d_def`

English:
theorem d_def
  statement: (barComplex k G).d (n + 1) n = d k G n
  proof: by simp

中文:
定理 d_def
  结论: (barComplex k G).d (n + 1) n = d k G n
  证明: by simp
-/
theorem d_def : (barComplex k G).d (n + 1) n = d k G n := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoStandardComplex` / `isoStandardComplex` 的定义

English:
definition isoStandardComplex
  signature: : barComplex k G ≅ standardComplex k G
  body: HomologicalComplex.Hom.isoOfComponents (fun i => (diagonalSuccIsoFree k G i).symm) fun i j => by
    rintro (rfl : j + 1 = i)
    rw [d_def]; rw [Iso.symm_hom]; rw [Iso.symm_hom]; rw [d_comp_diagonalSuccIsoFree_inv_eq]

中文:
定义 isoStandardComplex
  签名: : barComplex k G ≅ standardComplex k G
  定义体: HomologicalComplex.Hom.isoOfComponents (fun i => (diagonalSuccIsoFree k G i).symm) fun i j => by
    rintro (rfl : j + 1 = i)
    rw [d_def]; rw [Iso.symm_hom]; rw [Iso.symm_hom]; rw [d_comp_diagonalSuccIsoFree_inv_eq]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.symm_hom, d_comp_diagonalSuccIsoFree_inv_eq, d_def, diagonalSuccIsoFree, isoOfComponents, symm_hom
-/
def isoStandardComplex : barComplex k G ≅ standardComplex k G :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (diagonalSuccIsoFree k G i).symm) fun i j => by
    rintro (rfl : j + 1 = i)
    rw [d_def]; rw [Iso.symm_hom]; rw [Iso.symm_hom]; rw [d_comp_diagonalSuccIsoFree_inv_eq]

end barComplex

/-- The chain complex `barComplex k G` as a projective resolution of `k` as a trivial
`k`-linear `G`-representation. -/
@[simps complex]
/--
Definition of `barResolution` / `barResolution` 的定义

English:
definition barResolution
  signature: : ProjectiveResolution (Rep.trivial k G k) where
  body: barComplex k G
  projective n := (inferInstance : Projective (free k G (Fin n -> G)))
  π := (isoStandardComplex k G).hom ≫ standardComplex.εToSingle₀ k G

中文:
定义 barResolution
  签名: : 投射消解 (Rep.trivial k G k) where
  定义体: barComplex k G
  projective n := (inferInstance : Projective (free k G (Fin n -> G)))
  π := (isoStandardComplex k G).hom ≫ standardComplex.εToSingle₀ k G

Depends on / 依赖: barComplex
-/
def barResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := barComplex k G
  projective n := (inferInstance : Projective (free k G (Fin n -> G)))
  π := (isoStandardComplex k G).hom ≫ standardComplex.εToSingle₀ k G

/--
Definition of `barResolution.extIso` / `barResolution.extIso` 的定义

English:
definition barResolution.extIso
  signature: (V : Rep k G) (n : Nat)
  body: (barResolution k G).isoExt n V

中文:
定义 barResolution.extIso
  签名: (V : Rep k G) (n : 自然数)
  定义体: (barResolution k G).isoExt n V

Depends on / 依赖: barResolution, isoExt
-/
def barResolution.extIso (V : Rep k G) (n : Nat) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((barComplex k G).linearYonedaObj k V).homology n :=
  (barResolution k G).isoExt n V

end Rep
