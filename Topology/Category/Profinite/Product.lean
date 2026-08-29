/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.Basic

/-!
# Compact subsets of products as limits in `Profinite`

This file exhibits a compact subset `C` of a product `(i : ι) → X i` of totally disconnected
Hausdorff spaces as a cofiltered limit in `Profinite` indexed by `Finset ι`.

## Main definitions

- `Profinite.indexFunctor` is the functor `(Finset ι)ᵒᵖ ⥤ Profinite` indexing the limit. It maps
  `J` to the restriction of `C` to `J`
- `Profinite.indexCone` is a cone on `Profinite.indexFunctor` with cone point `C`

## Main results

- `Profinite.isIso_indexCone_lift` says that the natural map from the cone point of the explicit
  limit cone in `Profinite` on `indexFunctor` to the cone point of `indexCone` is an
  isomorphism
- `Profinite.asLimitindexConeIso` is the induced isomorphism of cones.
- `Profinite.indexCone_isLimit` says that `indexCone` is a limit cone.

-/

@[expose] public section

universe u

namespace Profinite

variable {ι : Type u} {X : ι -> Type} [forall i, TopologicalSpace (X i)] (C : Set ((i : ι) -> X i))
    (J K : ι -> Prop)

namespace IndexFunctor

open ContinuousMap

/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: : Set ((i : {i : ι // J i}) -> X i)
  body: ContinuousMap.precomp (Subtype.val (p := J)) '' C

中文:
定义 obj
  签名: : Set ((i : {i : ι // J i}) -> X i)
  定义体: ContinuousMap.precomp (Subtype.val (p := J)) '' C

Depends on / 依赖: ContinuousMap, ContinuousMap.precomp, Subtype, Subtype.val, precomp
-/
def obj : Set ((i : {i : ι // J i}) -> X i) := ContinuousMap.precomp (Subtype.val (p := J)) '' C

/--
Definition of `π_app` / `π_app` 的定义

English:
definition π_app
  signature: : C(C, obj C J)
  body: ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

中文:
定义 π_app
  签名: : C(C, obj C J)
  定义体: ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

Depends on / 依赖: Continuous, Continuous.restrict, MapsTo, Pi.continuous_precomp, Set.MapsTo.restrict, Set.mapsTo_image, Subtype, Subtype.val, continuous_precomp, mapsTo_image, precomp, restrict
-/
def π_app : C(C, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

variable {J K}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (h : forall i, J i -> K i)
  body: ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx => by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    exact ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩

中文:
定义 map
  签名: (h : 对任意 i, J i -> K i)
  定义体: ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx => by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    exact ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩

Depends on / 依赖: Continuous, Continuous.restrict, MapsTo, Pi.continuous_precomp, Set.MapsTo.restrict, Set.inclusion, continuous_precomp, inclusion, precomp, restrict
-/
def map (h : forall i, J i -> K i) : C(obj C K, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx => by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    exact ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩

/--
theorem `surjective_π_app` / 定理 `surjective_π_app`

English:
theorem surjective_π_app
  proof: by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  exact ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩

中文:
定理 surjective_π_app
  证明: by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  exact ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩

Depends on / 依赖: Subtype, Subtype.ext, x.prop
-/
theorem surjective_π_app :
    Function.Surjective (π_app C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  exact ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩

/--
theorem `map_comp_π_app` / 定理 `map_comp_π_app`

English:
theorem map_comp_π_app
  given: (h : forall i, J i -> K i)
  statement: map C h ∘ π_app C K = π_app C J
  proof: rfl

中文:
定理 map_comp_π_app
  条件: (h : 对任意 i, J i -> K i)
  结论: map C h ∘ π_app C K = π_app C J
  证明: rfl
-/
theorem map_comp_π_app (h : forall i, J i -> K i) : map C h ∘ π_app C K = π_app C J := rfl

variable {C}

/--
theorem `eq_of_forall_π_app_eq` / 定理 `eq_of_forall_π_app_eq`

English:
theorem eq_of_forall_π_app_eq
  statement: (a b : C)
  proof: by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, ContinuousMap.precomp, ContinuousMap.coe_mk] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

中文:
定理 eq_of_forall_π_app_eq
  结论: (a b : C)
  证明: by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, ContinuousMap.precomp, ContinuousMap.coe_mk] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.precomp, Finset, Finset.mem_singleton.mpr, Subtype, Subtype.ext_iff, coe_mk, congr_fun, ext_iff, mem_singleton, precomp, specialize
-/
theorem eq_of_forall_π_app_eq (a b : C)
    (h : forall (J : Finset ι), π_app C (· in J) a = π_app C (· in J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, ContinuousMap.precomp, ContinuousMap.coe_mk] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

end IndexFunctor

variable [forall i, T2Space (X i)] [forall i, TotallyDisconnectedSpace (X i)]
variable {C}

open CategoryTheory Limits Opposite IndexFunctor

/-- The functor from the poset of finsets of `ι` to `Profinite`, indexing the limit. -/
noncomputable
/--
Definition of `indexFunctor` / `indexFunctor` 的定义

English:
definition indexFunctor
  signature: (hC : IsCompact C)
  body: @Profinite.of (obj C (· in (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := ConcreteCategory.ofHom (map C (leOfHom h.unop))

中文:
定义 indexFunctor
  签名: (hC : IsCompact C)
  定义体: @Profinite.of (obj C (· in (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := ConcreteCategory.ofHom (map C (leOfHom h.unop))

Depends on / 依赖: Profinite, Profinite.of
-/
def indexFunctor (hC : IsCompact C) : (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (obj C (· in (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := ConcreteCategory.ofHom (map C (leOfHom h.unop))

/-- The limit cone on `indexFunctor` -/
noncomputable
/--
Definition of `indexCone` / `indexCone` 的定义

English:
definition indexCone
  signature: (hC : IsCompact C)
  body: @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J => ConcreteCategory.ofHom (π_app C (· in unop J)) }

中文:
定义 indexCone
  签名: (hC : IsCompact C)
  定义体: @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J => ConcreteCategory.ofHom (π_app C (· in unop J)) }

Depends on / 依赖: Profinite, Profinite.of, isCompact_iff_compactSpace
-/
def indexCone (hC : IsCompact C) : Cone (indexFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J => ConcreteCategory.ofHom (π_app C (· in unop J)) }

variable (hC : IsCompact C)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_indexCone_lift` / 实例 `isIso_indexCone_lift`

English:
instance isIso_indexCone_lift
  signature: :
  body: haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine eq_of_forall_π_app_eq a b (fun J => ?_)
        apply_fun fun f : (limitCone.{u, u} (indexFunctor hC)).pt => f.val (op J) at h
      

中文:
实例 isIso_indexCone_lift
  签名: :
  定义体: haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine eq_of_forall_π_app_eq a b (fun J => ?_)
        apply_fun fun f : (limitCone.{u, u} (indexFunctor hC)).pt => f.val (op J) at h
      

Depends on / 依赖: CompHausLike, CompHausLike.isIso_of_bijective, CompactSpace, Finset, IsClosed, Subtype, Subtype.ext, a.val, apply_fun, f.val, indexFunctor, isCompact_iff_compactSpace, isIso_of_bijective, limitCone, rsuffices
-/
instance isIso_indexCone_lift :
    IsIso ((limitConeIsLimit.{u, u} (indexFunctor hC)).lift (indexCone hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  CompHausLike.isIso_of_bijective _
    (by
      refine ⟨fun a b h => ?_, fun a => ?_⟩
      · refine eq_of_forall_π_app_eq a b (fun J => ?_)
        apply_fun fun f : (limitCone.{u, u} (indexFunctor hC)).pt => f.val (op J) at h
        exact h
      · rsuffices ⟨b, hb⟩ : exists (x : C), forall (J : Finset ι), π_app C (· in J) x = a.val (op J)
        · use b
          apply Subtype.ext
          apply funext
          intro J
          exact hb (unop J)
        have hc : forall (J : Finset ι) s, IsClosed ((π_app C (· in J)) ⁻¹' {s}) := by
          intro J s
          refine IsClosed.preimage (π_app C (· in J)).continuous ?_
          exact T1Space.t1 s
        have H₁ : forall (Q₁ Q₂ : Finset ι), Q₁ <= Q₂ ->
            π_app C (· in Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            π_app C (· in Q₂) ⁻¹' {a.val (op Q₂)} := by
          intro J K h x hx
          simp only [Set.mem_preimage] at hx ⊢
          rw [← map_comp_π_app C h]; rw [Function.comp_apply]; rw [hx]; rw [← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), π_app C (· in J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
            (fun J : Finset ι => π_app C (· in J) ⁻¹' {a.val (op J)}) (directed_of_isDirected_le H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_π_app _))
            (fun J => (hc J (a.val (op J))).isCompact) fun J => hc J (a.val (op J))
        exact ⟨x, Set.mem_iInter.1 hx⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from `C` to the explicit limit as an isomorphism. -/
noncomputable
/--
Definition of `isoindexConeLift` / `isoindexConeLift` 的定义

English:
definition isoindexConeLift
  signature: :
  body: asIso (Profinite.limitConeIsLimit.{u, u} _).lift (indexCone hC)

中文:
定义 isoindexConeLift
  签名: :
  定义体: asIso (Profinite.limitConeIsLimit.{u, u} _).lift (indexCone hC)

Depends on / 依赖: Profinite, Profinite.limitConeIsLimit, indexCone, limitConeIsLimit
-/
def isoindexConeLift :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone.{u, u} (indexFunctor hC)).pt :=
asIso (Profinite.limitConeIsLimit.{u, u} _).lift (indexCone hC)

/-- The isomorphism of cones induced by `isoindexConeLift`. -/
noncomputable
/--
Definition of `asLimitindexConeIso` / `asLimitindexConeIso` 的定义

English:
definition asLimitindexConeIso
  signature: : indexCone hC ≅ Profinite.limitCone.{u, u} _
  body: Limits.Cone.ext (isoindexConeLift hC) fun _ => rfl

中文:
定义 asLimitindexConeIso
  签名: : indexCone hC ≅ Profinite.limitCone.{u, u} _
  定义体: Limits.Cone.ext (isoindexConeLift hC) fun _ => rfl

Depends on / 依赖: Limits, Limits.Cone.ext, isoindexConeLift
-/
def asLimitindexConeIso : indexCone hC ≅ Profinite.limitCone.{u, u} _ :=
  Limits.Cone.ext (isoindexConeLift hC) fun _ => rfl

/-- `indexCone` is a limit cone. -/
noncomputable
/--
Definition of `indexCone_isLimit` / `indexCone_isLimit` 的定义

English:
definition indexCone_isLimit
  signature: : CategoryTheory.Limits.IsLimit (indexCone hC)
  body: Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitindexConeIso hC).symm

中文:
定义 indexCone_isLimit
  签名: : CategoryTheory.Limits.IsLimit (indexCone hC)
  定义体: Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitindexConeIso hC).symm

Depends on / 依赖: IsLimit, Limits, Limits.IsLimit.ofIsoLimit, Profinite, Profinite.limitConeIsLimit, asLimitindexConeIso, limitConeIsLimit, ofIsoLimit
-/
def indexCone_isLimit : CategoryTheory.Limits.IsLimit (indexCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitindexConeIso hC).symm

end Profinite
