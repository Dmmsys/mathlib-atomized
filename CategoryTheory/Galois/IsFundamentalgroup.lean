/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Universal property of fundamental group

Let `C` be a Galois category with fiber functor `F`. While in informal mathematics, we tend to
identify known groups from other contexts (e.g. the absolute Galois group of a field) with
the automorphism group `Aut F` of certain fiber functors `F`, this causes friction in formalization.

Hence, in this file we develop conditions when a topological group `G` is canonically isomorphic to
the automorphism group `Aut F` of `F`. Consequently, the API for Galois categories and their fiber
functors should be stated in terms of an abstract topological group `G` satisfying
`IsFundamentalGroup` in the places where `Aut F` would appear.

## Main definition

Given a compact, topological group `G` with an action on `F.obj X` on each `X`, we say that
`G` is a fundamental group of `F` (`IsFundamentalGroup F G`), if

- `naturality`: the `G`-action on `F.obj X` is compatible with morphisms in `C`
- `transitive_of_isGalois`: `G` acts transitively on `F.obj X` for all Galois objects `X : C`
- `continuous_smul`: the action of `G` on `F.obj X` is continuous if `F.obj X` is equipped with the
  discrete topology for all `X : C`.
- `non_trivial'`: if `g : G` acts trivially on all `F.obj X`, then `g = 1`.

Given this data, we define `toAut F G : G →* Aut F` in the natural way.

## Main results

- `toAut_bijective`: `toAut F G` is a group isomorphism given `IsFundamentalGroup F G`.
- `toAut_isHomeomorph`: `toAut F G` is a homeomorphism given `IsFundamentalGroup F G`.

## TODO

- Develop further equivalent conditions, in particular, relate the condition `non_trivial` with
  `G` being a `T2Space`.

-/

@[expose] public section

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

section

variable (G : Type*) [Group G] [forall X, MulAction G (F.obj X)]

/--
Definition of `IsNaturalSMul` / `IsNaturalSMul` 的定义

English:
class IsNaturalSMul
  parameters: : Prop where
  axioms and operations (1):
    - naturality((g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X)) : F.map f (g • x) = g • F.map f x

中文:
类 IsNaturalSMul
  参数: : 命题 where
  公理与运算 (1 个):
    - naturality((g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X)) : F.map f (g • x) = g • F.map f x

Depends on / 依赖: HasProducts, hasProductsOfShape_of_hasProducts
-/
class IsNaturalSMul : Prop where
  naturality (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X) : F.map f (g • x) = g • F.map f x

set_option backward.privateInPublic true in
variable {G} in
@[simps! -isSimp]
/--
Definition of `isoOnObj` / `isoOnObj` 的定义

English:
definition isoOnObj
  signature: (g : G) (X : C)
  body: FintypeCat.equivEquivIso {
    toFun := fun x => g • x
    invFun := fun x => g⁻¹ • x
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp
  }

中文:
定义 isoOnObj
  签名: (g : G) (X : C)
  定义体: FintypeCat.equivEquivIso {
    toFun := fun x => g • x
    invFun := fun x => g⁻¹ • x
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp
  }

Depends on / 依赖: HasCoproducts, hasCoproductsOfShape_of_hasCoproducts
-/
private def isoOnObj (g : G) (X : C) : F.obj X ≅ F.obj X :=
FintypeCat.equivEquivIso {
    toFun := fun x => g • x
    invFun := fun x => g⁻¹ • x
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp
  }

variable [IsNaturalSMul F G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `toAut` / `toAut` 的定义

English:
definition toAut
  signature: : G ->* Aut F where
  body: NatIso.ofComponents (isoOnObj F g) by
    intro X Y f
    ext
    exact (IsNaturalSMul.naturality _ _ _).symm
  map_one' := by
    ext
    dsimp [isoOnObj]
    cat_disch
  map_mul' := by
    intro g h
    ext X x
    apply mul_smul

中文:
定义 toAut
  签名: : G ->* Aut F where
  定义体: NatIso.ofComponents (isoOnObj F g) by
    intro X Y f
    ext
    exact (IsNaturalSMul.naturality _ _ _).symm
  map_one' := by
    ext
    dsimp [isoOnObj]
    cat_disch
  map_mul' := by
    intro g h
    ext X x
    apply mul_smul

Depends on / 依赖: IsNaturalSMul, IsNaturalSMul.naturality, NatIso, NatIso.ofComponents, cat_disch, isoOnObj, map_mul, map_one, mul_smul, naturality, ofComponents
-/
def toAut : G ->* Aut F where
toFun g := NatIso.ofComponents (isoOnObj F g) by
    intro X Y f
    ext
    exact (IsNaturalSMul.naturality _ _ _).symm
  map_one' := by
    ext
    dsimp [isoOnObj]
    cat_disch
  map_mul' := by
    intro g h
    ext X x
    apply mul_smul

variable {G} in
@[simp]
/--
lemma `toAut_hom_app_apply` / 引理 `toAut_hom_app_apply`

English:
lemma toAut_hom_app_apply
  given: (g : G) {X : C} (x : F.obj X)
  statement: (toAut F G g).hom.app X x = g • x
  proof: rfl

中文:
引理 toAut_hom_app_apply
  条件: (g : G) {X : C} (x : F.obj X)
  结论: (toAut F G g).hom.app X x = g • x
  证明: rfl
-/
lemma toAut_hom_app_apply (g : G) {X : C} (x : F.obj X) : (toAut F G g).hom.app X x = g • x :=
  rfl

/--
lemma `toAut_injective_of_non_trivial` / 引理 `toAut_injective_of_non_trivial`

English:
lemma toAut_injective_of_non_trivial
  given: (h : forall (g : G), (forall (X : C) (x : F.obj X), g • x = x) -> g = 1)
  proof: by
  rw [← MonoidHom.ker_eq_bot_iff]; rw [eq_bot_iff]
  intro g (hg : toAut F G g = 1)
  refine h g (fun X x => ?_)
  have : (toAut F G g).hom.app X = 𝟙 (F.obj X) := by
    rw [hg]
    rfl
  rw [← toAut_hom_app_apply]; rw [this]; rw [FintypeCat.id_apply]

中文:
引理 toAut_injective_of_non_trivial
  条件: (h : 对任意 (g : G), (对任意 (X : C) (x : F.obj X), g • x = x) -> g = 1)
  证明: by
  rw [← MonoidHom.ker_eq_bot_iff]; rw [eq_bot_iff]
  intro g (hg : toAut F G g = 1)
  refine h g (fun X x => ?_)
  have : (toAut F G g).hom.app X = 𝟙 (F.obj X) := by
    rw [hg]
    rfl
  rw [← toAut_hom_app_apply]; rw [this]; rw [FintypeCat.id_apply]

Depends on / 依赖: F.obj, FintypeCat, FintypeCat.id_apply, MonoidHom, MonoidHom.ker_eq_bot_iff, eq_bot_iff, hom.app, id_apply, ker_eq_bot_iff, toAut_hom_app_apply
-/
lemma toAut_injective_of_non_trivial (h : forall (g : G), (forall (X : C) (x : F.obj X), g • x = x) -> g = 1) :
    Function.Injective (toAut F G) := by
  rw [← MonoidHom.ker_eq_bot_iff]; rw [eq_bot_iff]
  intro g (hg : toAut F G g = 1)
  refine h g (fun X x => ?_)
  have : (toAut F G g).hom.app X = 𝟙 (F.obj X) := by
    rw [hg]
    rfl
  rw [← toAut_hom_app_apply]; rw [this]; rw [FintypeCat.id_apply]

variable [GaloisCategory C] [FiberFunctor F]

/--
lemma `toAut_continuous` / 引理 `toAut_continuous`

English:
lemma toAut_continuous
  statement: [TopologicalSpace G] [IsTopologicalGroup G]
  proof: by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def]; rw [map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  exact ⟨MulAction.stabilizer G X.pt, Set.preimage_mono (f := toAut F G) hX,
    stabilizer_isOpen G X.pt, one

中文:
引理 toAut_continuous
  结论: [TopologicalSpace G] [IsTopologicalGroup G]
  证明: by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def]; rw [map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  exact ⟨MulAction.stabilizer G X.pt, Set.preimage_mono (f := toAut F G) hX,
    stabilizer_isOpen G X.pt, one

Depends on / 依赖: MulAction, MulAction.stabilizer, Set.preimage_mono, X.pt, continuousAt_def, continuous_of_continuousAt_one, map_one, mem_iff, mem_nhds_iff, nhds_one_has_basis_stabilizers, one_mem, preimage_mono, stabilizer, stabilizer_isOpen
-/
lemma toAut_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    [forall (X : C), ContinuousSMul G (F.obj X)] :
    Continuous (toAut F G) := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def]; rw [map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  exact ⟨MulAction.stabilizer G X.pt, Set.preimage_mono (f := toAut F G) hX,
    stabilizer_isOpen G X.pt, one_mem _⟩

variable {G}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `action_ext_of_isGalois` / 引理 `action_ext_of_isGalois`

English:
lemma action_ext_of_isGalois
  statement: {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X)
  proof: by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [IsNaturalSMul.naturality]; rw [hg]; rw [FunctorToFintypeCat.naturality]

中文:
引理 action_ext_of_isGalois
  结论: {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X)
  证明: by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [IsNaturalSMul.naturality]; rw [hg]; rw [FunctorToFintypeCat.naturality]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.injective_of_mono_of_preservesPullback, F.map, Function, Function.Injective, FunctorToFintypeCat, FunctorToFintypeCat.naturality, Injective, IsNaturalSMul, IsNaturalSMul.naturality, MulAction, MulAction.exists_smul_eq, exists_smul_eq, injective_of_mono_of_preservesPullback, naturality
-/
lemma action_ext_of_isGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X)
    (hg : g • x = t.app X x) (y : F.obj X) : g • y = t.app X y := by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [IsNaturalSMul.naturality]; rw [hg]; rw [FunctorToFintypeCat.naturality]

variable (G)

/--
lemma `toAut_surjective_isGalois` / 引理 `toAut_surjective_isGalois`

English:
lemma toAut_surjective_isGalois
  statement: (t : Aut F) (X : C) [IsGalois X]
  proof: by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  exact ⟨g, action_ext_of_isGalois F _ hg⟩

中文:
引理 toAut_surjective_isGalois
  结论: (t : Aut F) (X : C) [IsGalois X]
  证明: by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  exact ⟨g, action_ext_of_isGalois F _ hg⟩

Depends on / 依赖: MulAction, MulAction.exists_smul_eq, Nonempty, Subsingleton, action_ext_of_isGalois, exists_smul_eq, hasProduct_unique, nonempty_fiber_of_isConnected, t.hom.app
-/
lemma toAut_surjective_isGalois (t : Aut F) (X : C) [IsGalois X]
    [MulAction.IsPretransitive G (F.obj X)] :
    exists (g : G), forall (x : F.obj X), g • x = t.hom.app X x := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  exact ⟨g, action_ext_of_isGalois F _ hg⟩

/--
lemma `toAut_surjective_isGalois_finite_family` / 引理 `toAut_surjective_isGalois_finite_family`

English:
lemma toAut_surjective_isGalois_finite_family
  statement: (t : Aut F) {ι : Type*} [Finite ι] (X : ι -> C)
  proof: by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  let is₁ : F.obj P ≅ ∏ᶜ fun i => (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i => F.obj (X i) : FintypeCat) ≃ forall i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i => 

中文:
引理 toAut_surjective_isGalois_finite_family
  结论: (t : Aut F) {ι : 类型} [Finite ι] (X : ι -> C)
  证明: by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  let is₁ : F.obj P ≅ ∏ᶜ fun i => (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i => F.obj (X i) : FintypeCat) ≃ forall i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i => 

Depends on / 依赖: F.map, F.obj, FintypeCat, FintypeCat.comp_apply, Limits, Limits.FintypeCat.productEquiv, PreservesProduct, PreservesProduct.iso, PreservesProduct.iso_hom, comp_apply, iso_hom, nonempty_fiber_of_isConnected, productEquiv
-/
lemma toAut_surjective_isGalois_finite_family (t : Aut F) {ι : Type*} [Finite ι] (X : ι -> C)
    [forall i, IsGalois (X i)] (h : forall (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    exists (g : G), forall (i : ι) (x : F.obj (X i)), g • x = t.hom.app (X i) x := by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  let is₁ : F.obj P ≅ ∏ᶜ fun i => (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i => F.obj (X i) : FintypeCat) ≃ forall i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i => (F.obj (X i)))
  let px : F.obj P := is₁.inv (is₂.symm x)
  have hpx (i : ι) : F.map (Pi.π X i) px = x i := by
    simp only [px, is₁, is₂, ← piComparison_comp_π, ← PreservesProduct.iso_hom,
      FintypeCat.comp_apply]
    rw [FintypeCat.inv_hom_id_apply]; rw [FintypeCat.productEquiv_symm_comp_π_apply]
  obtain ⟨A, f, a, _, hfa⟩ := exists_hom_from_galois_of_fiber F P px
  obtain ⟨g, hg⟩ := toAut_surjective_isGalois F G t A
  refine ⟨g, fun i y => action_ext_of_isGalois F (x i) ?_ _⟩
  rw [← hpx i]; rw [← IsNaturalSMul.naturality]; rw [FunctorToFintypeCat.naturality]; rw [← hfa]; rw [FunctorToFintypeCat.naturality]; rw [← IsNaturalSMul.naturality]; rw [hg]

open scoped Pointwise

/--
lemma `toAut_surjective_of_isPretransitive` / 引理 `toAut_surjective_of_isPretransitive`

English:
lemma toAut_surjective_of_isPretransitive
  statement: [TopologicalSpace G] [IsTopologicalGroup G]
  proof: by
  intro t
  choose gi hgi using (fun X : PointedGaloisObject F => toAut_surjective_isGalois F G t X)
  let cl (X : PointedGaloisObject F) : Set G := gi X • MulAction.stabilizer G X.pt
  let c : Set G := ⋂ i, cl i
  have hne : c.Nonempty := by
    rw [← Set.univ_inter c]
    apply CompactSpace.isC

中文:
引理 toAut_surjective_of_isPretransitive
  结论: [TopologicalSpace G] [IsTopologicalGroup G]
  证明: by
  intro t
  choose gi hgi using (fun X : PointedGaloisObject F => toAut_surjective_isGalois F G t X)
  let cl (X : PointedGaloisObject F) : Set G := gi X • MulAction.stabilizer G X.pt
  let c : Set G := ⋂ i, cl i
  have hne : c.Nonempty := by
    rw [← Set.univ_inter c]
    apply CompactSpace.isC

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ.inter_iInter_nonempty, IsClosed, IsClosed.leftCoset, MulAction, MulAction.stabilizer, Nonempty, PointedGaloisObject, Set.univ_inter, Subgroup, Subgroup.isClosed_of_isOpen, X.pt, c.Nonempty, inter_iInter_nonempty, isClosed_of_isOpen, isCompact_univ, leftCoset, stabilizer, stabilizer_isOpen, toAut_surjective_isGalois
-/
lemma toAut_surjective_of_isPretransitive [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [forall (X : C), ContinuousSMul G (F.obj X)]
    (h : forall (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    Function.Surjective (toAut F G) := by
  intro t
  choose gi hgi using (fun X : PointedGaloisObject F => toAut_surjective_isGalois F G t X)
  let cl (X : PointedGaloisObject F) : Set G := gi X • MulAction.stabilizer G X.pt
  let c : Set G := ⋂ i, cl i
  have hne : c.Nonempty := by
    rw [← Set.univ_inter c]
    apply CompactSpace.isCompact_univ.inter_iInter_nonempty
    · intro X
      apply IsClosed.leftCoset
      exact Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen G X.pt)
    · intro s
      rw [Set.univ_inter]
      obtain ⟨gs, hgs⟩ :=
        toAut_surjective_isGalois_finite_family F G t (fun X : s => X.val.obj) h
      use gs
      simp only [Set.mem_iInter]
      intro X hXmem
      rw [mem_leftCoset_iff]; rw [SetLike.mem_coe]; rw [MulAction.mem_stabilizer_iff]; rw [mul_smul]; rw [hgs ⟨X]; rw [hXmem⟩]; rw [← hgi X]; rw [inv_smul_smul]
  obtain ⟨g, hg⟩ := hne
refine ⟨g, Iso.ext natTrans_ext_of_isGalois _ fun X _ => ?_⟩
  ext x
  simp only [toAut_hom_app_apply]
  have : g in (gi ⟨X, x, inferInstance⟩ • MulAction.stabilizer G x : Set G) := by
    simp only [Set.mem_iInter, c] at hg
    exact hg _
  obtain ⟨s, (hsmem : s • x = x), (rfl : gi ⟨X, x, inferInstance⟩ • s = _)⟩ := this
  rw [smul_eq_mul]; rw [mul_smul]; rw [hsmem]
  exact hgi ⟨X, x, inferInstance⟩ x

/--
lemma `isPretransitive_of_surjective` / 引理 `isPretransitive_of_surjective`

English:
lemma isPretransitive_of_surjective
  statement: (h : Function.Surjective (toAut F G)) (X : C)
  proof: by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := h t
    exact ⟨g, ht⟩

中文:
引理 isPretransitive_of_surjective
  结论: (h : Function.Surjective (toAut F G)) (X : C)
  证明: by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := h t
    exact ⟨g, ht⟩

Depends on / 依赖: MulAction, MulAction.exists_smul_eq, exists_smul_eq
-/
lemma isPretransitive_of_surjective (h : Function.Surjective (toAut F G)) (X : C)
    [IsConnected X] : MulAction.IsPretransitive G (F.obj X) where
  exists_smul_eq x y := by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := h t
    exact ⟨g, ht⟩

end

section

variable [GaloisCategory C]
variable (G : Type*) [Group G] [forall (X : C), MulAction G (F.obj X)]

/--
Definition of `IsFundamentalGroup` / `IsFundamentalGroup` 的定义

English:
class IsFundamentalGroup
  parameters: [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  extends: IsNaturalSMul F G
  axioms and operations (3):
    - transitive_of_isGalois((X : C) [IsGalois X]) : MulAction.IsPretransitive G (F.obj X)
    - continuous_smul((X : C)) : ContinuousSMul G (F.obj X)
    - non_trivial'((g : G)) : (forall (X : C) (x : F.obj X), g • x = x) -> g = 1

中文:
类 IsFundamentalGroup
  参数: [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  继承: IsNaturalSMul F G
  公理与运算 (3 个):
    - transitive_of_isGalois((X : C) [IsGalois X]) : MulAction.IsPretransitive G (F.obj X)
    - continuous_smul((X : C)) : ContinuousSMul G (F.obj X)
    - non_trivial'((g : G)) : (对任意 (X : C) (x : F.obj X), g • x = x) -> g = 1
-/
class IsFundamentalGroup [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] : Prop
    extends IsNaturalSMul F G where
  transitive_of_isGalois (X : C) [IsGalois X] : MulAction.IsPretransitive G (F.obj X)
  continuous_smul (X : C) : ContinuousSMul G (F.obj X)
  non_trivial' (g : G) : (forall (X : C) (x : F.obj X), g • x = x) -> g = 1

namespace IsFundamentalGroup

attribute [instance] continuous_smul transitive_of_isGalois

variable {G} [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]

/--
lemma `non_trivial` / 引理 `non_trivial`

English:
lemma non_trivial
  given: (g : G) (h : forall (X : C) (x : F.obj X), g • x = x)
  statement: g = 1
  proof: IsFundamentalGroup.non_trivial' g h

中文:
引理 non_trivial
  条件: (g : G) (h : 对任意 (X : C) (x : F.obj X), g • x = x)
  结论: g = 1
  证明: IsFundamentalGroup.non_trivial' g h

Depends on / 依赖: IsFundamentalGroup, IsFundamentalGroup.non_trivial, non_trivial
-/
lemma non_trivial (g : G) (h : forall (X : C) (x : F.obj X), g • x = x) : g = 1 :=
  IsFundamentalGroup.non_trivial' g h

end IsFundamentalGroup

variable [FiberFunctor F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFundamentalGroup F (Aut F)
  body: (FunctorToFintypeCat.naturality F F g.hom f x).symm
  transitive_of_isGalois X := FiberFunctor.isPretransitive_of_isConnected F X
  continuous_smul X := continuousSMul_aut_fiber F X
  non_trivial' g h := by
    ext X x
    exact h X x

中文:
实例 :
  签名: IsFundamentalGroup F (Aut F)
  定义体: (FunctorToFintypeCat.naturality F F g.hom f x).symm
  transitive_of_isGalois X := FiberFunctor.isPretransitive_of_isConnected F X
  continuous_smul X := continuousSMul_aut_fiber F X
  non_trivial' g h := by
    ext X x
    exact h X x

Depends on / 依赖: FunctorToFintypeCat, FunctorToFintypeCat.naturality, Nonempty, Subsingleton, g.hom, hasCoproduct_unique, naturality
-/
instance : IsFundamentalGroup F (Aut F) where
  naturality g _ _ f x := (FunctorToFintypeCat.naturality F F g.hom f x).symm
  transitive_of_isGalois X := FiberFunctor.isPretransitive_of_isConnected F X
  continuous_smul X := continuousSMul_aut_fiber F X
  non_trivial' g h := by
    ext X x
    exact h X x

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]

/--
lemma `toAut_bijective` / 引理 `toAut_bijective`

English:
lemma toAut_bijective
  statement: Function.Bijective (toAut F G) where
  proof: toAut_injective_of_non_trivial F G IsFundamentalGroup.non_trivial'
  right := toAut_surjective_of_isPretransitive F G IsFundamentalGroup.transitive_of_isGalois

中文:
引理 toAut_bijective
  结论: Function.Bijective (toAut F G) where
  证明: toAut_injective_of_non_trivial F G IsFundamentalGroup.non_trivial'
  right := toAut_surjective_of_isPretransitive F G IsFundamentalGroup.transitive_of_isGalois

Depends on / 依赖: IsFundamentalGroup, IsFundamentalGroup.non_trivial, non_trivial, toAut_injective_of_non_trivial
-/
lemma toAut_bijective : Function.Bijective (toAut F G) where
  left := toAut_injective_of_non_trivial F G IsFundamentalGroup.non_trivial'
  right := toAut_surjective_of_isPretransitive F G IsFundamentalGroup.transitive_of_isGalois

instance (X : C) [IsConnected X] : MulAction.IsPretransitive G (F.obj X) :=
  isPretransitive_of_surjective F G (toAut_bijective F G).surjective X

/--
Definition of `toAutMulEquiv` / `toAutMulEquiv` 的定义

English:
definition toAutMulEquiv
  signature: : G ≃* Aut F
  body: MulEquiv.ofBijective (toAut F G) (toAut_bijective F G)

中文:
定义 toAutMulEquiv
  签名: : G ≃* Aut F
  定义体: MulEquiv.ofBijective (toAut F G) (toAut_bijective F G)

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, ofBijective, toAut_bijective
-/
noncomputable def toAutMulEquiv : G ≃* Aut F :=
  MulEquiv.ofBijective (toAut F G) (toAut_bijective F G)

/--
lemma `toAut_isHomeomorph` / 引理 `toAut_isHomeomorph`

English:
lemma toAut_isHomeomorph
  statement: IsHomeomorph (toAut F G)
  proof: by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨toAut_continuous F G, toAut_bijective F G⟩

中文:
引理 toAut_isHomeomorph
  结论: IsHomeomorph (toAut F G)
  证明: by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨toAut_continuous F G, toAut_bijective F G⟩

Depends on / 依赖: isHomeomorph_iff_continuous_bijective, toAut_bijective, toAut_continuous
-/
lemma toAut_isHomeomorph : IsHomeomorph (toAut F G) := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨toAut_continuous F G, toAut_bijective F G⟩

/--
lemma `toAutMulEquiv_isHomeomorph` / 引理 `toAutMulEquiv_isHomeomorph`

English:
lemma toAutMulEquiv_isHomeomorph
  statement: IsHomeomorph (toAutMulEquiv F G)
  proof: toAut_isHomeomorph F G

中文:
引理 toAutMulEquiv_isHomeomorph
  结论: IsHomeomorph (toAutMulEquiv F G)
  证明: toAut_isHomeomorph F G

Depends on / 依赖: toAut_isHomeomorph
-/
lemma toAutMulEquiv_isHomeomorph : IsHomeomorph (toAutMulEquiv F G) :=
  toAut_isHomeomorph F G

/--
Definition of `toAutHomeo` / `toAutHomeo` 的定义

English:
definition toAutHomeo
  signature: : G ≃ₜ Aut F
  body: (toAut_isHomeomorph F G).homeomorph

中文:
定义 toAutHomeo
  签名: : G ≃ₜ Aut F
  定义体: (toAut_isHomeomorph F G).homeomorph

Depends on / 依赖: homeomorph, toAut_isHomeomorph
-/
noncomputable def toAutHomeo : G ≃ₜ Aut F := (toAut_isHomeomorph F G).homeomorph

variable {G}

@[simp]
/--
lemma `toAutMulEquiv_apply` / 引理 `toAutMulEquiv_apply`

English:
lemma toAutMulEquiv_apply
  given: (g : G)
  statement: toAutMulEquiv F G g = toAut F G g
  proof: rfl

@[simp]

中文:
引理 toAutMulEquiv_apply
  条件: (g : G)
  结论: toAutMulEquiv F G g = toAut F G g
  证明: rfl

@[simp]
-/
lemma toAutMulEquiv_apply (g : G) : toAutMulEquiv F G g = toAut F G g := rfl

@[simp]
/--
lemma `toAutHomeo_apply` / 引理 `toAutHomeo_apply`

English:
lemma toAutHomeo_apply
  given: (g : G)
  statement: toAutHomeo F G g = toAut F G g
  proof: rfl

中文:
引理 toAutHomeo_apply
  条件: (g : G)
  结论: toAutHomeo F G g = toAut F G g
  证明: rfl
-/
lemma toAutHomeo_apply (g : G) : toAutHomeo F G g = toAut F G g := rfl

end

end PreGaloisCategory

end CategoryTheory
