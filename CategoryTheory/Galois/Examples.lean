/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Limits

/-!
# Examples of Galois categories and fiber functors

We show that for a group `G` the category of finite `G`-sets is a `PreGaloisCategory` and that the
forgetful functor to `FintypeCat` is a `FiberFunctor`.

The connected finite `G`-sets are precisely the ones with transitive `G`-action.

-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits CategoryTheory.Functor PreGaloisCategory

namespace FintypeCat

/--
Definition of `imageComplement` / `imageComplement` 的定义

English:
definition imageComplement
  signature: {X Y : FintypeCat.{u}} (f : X ⟶ Y)
  body: by
  haveI : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact FintypeCat.of (↑(Set.range f)ᶜ)

中文:
定义 imageComplement
  签名: {X Y : FintypeCat.{u}} (f : X ⟶ Y)
  定义体: by
  haveI : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact FintypeCat.of (↑(Set.range f)ᶜ)

Depends on / 依赖: Fintype, Fintype.ofFinite, FintypeCat, FintypeCat.of, Set.range, ofFinite
-/
noncomputable def imageComplement {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    FintypeCat.{u} := by
  haveI : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact FintypeCat.of (↑(Set.range f)ᶜ)

/--
Definition of `imageComplementIncl` / `imageComplementIncl` 的定义

English:
definition imageComplementIncl
  signature: {X Y : FintypeCat.{u}}
  body: FintypeCat.homMk Subtype.val

中文:
定义 imageComplementIncl
  签名: {X Y : FintypeCat.{u}}
  定义体: FintypeCat.homMk Subtype.val

Depends on / 依赖: FintypeCat, FintypeCat.homMk, Subtype, Subtype.val
-/
noncomputable def imageComplementIncl {X Y : FintypeCat.{u}}
    (f : X ⟶ Y) : imageComplement f ⟶ Y :=
  FintypeCat.homMk Subtype.val

variable (G : Type u) [Group G]

/--
Definition of `Action.imageComplement` / `Action.imageComplement` 的定义

English:
definition Action.imageComplement
  signature: {X Y : Action FintypeCat G}
  body: FintypeCat.imageComplement f.hom
  ρ := {
    toFun g := FintypeCat.homMk (fun y => Subtype.mk ((Y.ρ g).hom y.val) <| by
      intro ⟨x, h⟩
      apply y.property
      use (X.ρ g⁻¹).hom x
      calc (X.ρ g⁻¹ ≫ f.hom) x
          = ((Y.ρ g⁻¹ * Y.ρ g)).hom y.val := by rw [f.comm, FintypeCat.comp_appl

中文:
定义 Action.imageComplement
  签名: {X Y : Action FintypeCat G}
  定义体: FintypeCat.imageComplement f.hom
  ρ := {
    toFun g := FintypeCat.homMk (fun y => Subtype.mk ((Y.ρ g).hom y.val) <| by
      intro ⟨x, h⟩
      apply y.property
      use (X.ρ g⁻¹).hom x
      calc (X.ρ g⁻¹ ≫ f.hom) x
          = ((Y.ρ g⁻¹ * Y.ρ g)).hom y.val := by rw [f.comm, FintypeCat.comp_appl

Depends on / 依赖: FintypeCat, FintypeCat.imageComplement, f.hom, imageComplement
-/
noncomputable def Action.imageComplement {X Y : Action FintypeCat G}
    (f : X ⟶ Y) : Action FintypeCat G where
  V := FintypeCat.imageComplement f.hom
  ρ := {
    toFun g := FintypeCat.homMk (fun y => Subtype.mk ((Y.ρ g).hom y.val) <| by
      intro ⟨x, h⟩
      apply y.property
      use (X.ρ g⁻¹).hom x
      calc (X.ρ g⁻¹ ≫ f.hom) x
          = ((Y.ρ g⁻¹ * Y.ρ g)).hom y.val := by rw [f.comm, FintypeCat.comp_apply, h]; rfl
        _ = y.val := by
          simp [← map_mul, inv_mul_cancel, Action.ρ_one, FintypeCat.id_hom])
    map_one' := by aesop
    map_mul' := by aesop
  }

/--
Definition of `Action.imageComplementIncl` / `Action.imageComplementIncl` 的定义

English:
definition Action.imageComplementIncl
  signature: {X Y : Action FintypeCat G} (f : X ⟶ Y)
  body: FintypeCat.imageComplementIncl f.hom
  comm _ := rfl

中文:
定义 Action.imageComplementIncl
  签名: {X Y : Action FintypeCat G} (f : X ⟶ Y)
  定义体: FintypeCat.imageComplementIncl f.hom
  comm _ := rfl

Depends on / 依赖: FintypeCat, FintypeCat.imageComplementIncl, f.hom, imageComplementIncl
-/
noncomputable def Action.imageComplementIncl {X Y : Action FintypeCat G} (f : X ⟶ Y) :
    Action.imageComplement G f ⟶ Y where
  hom := FintypeCat.imageComplementIncl f.hom
  comm _ := rfl

instance {X Y : Action FintypeCat G} (f : X ⟶ Y) :
    Mono (Action.imageComplementIncl G f) := by
  apply Functor.mono_of_mono_map (forget _)
  apply ConcreteCategory.mono_of_injective
  exact Subtype.val_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w}
  body: by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

中文:
实例 [Finite
  签名: G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w}
  定义体: by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

Depends on / 依赖: Finite, Finite.exists_type_univ_nonempty_mulEquiv, Limits, Limits.hasColimitsOfShape_of_equivalence, e.toSingleObjEquiv.symm, exists_type_univ_nonempty_mulEquiv, hasColimitsOfShape_of_equivalence, toSingleObjEquiv
-/
instance [Finite G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w} := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (forget (Action FintypeCat G))
  body: by
  change PreservesFiniteLimits (Action.forget FintypeCat _ ⋙ FintypeCat.incl)
  apply comp_preservesFiniteLimits

中文:
实例 :
  签名: PreservesFiniteLimits (forget (Action FintypeCat G))
  定义体: by
  change PreservesFiniteLimits (Action.forget FintypeCat _ ⋙ FintypeCat.incl)
  apply comp_preservesFiniteLimits

Depends on / 依赖: Action, Action.forget, FintypeCat, FintypeCat.incl, PreservesFiniteLimits, comp_preservesFiniteLimits, forget
-/
noncomputable instance : PreservesFiniteLimits (forget (Action FintypeCat G)) := by
  change PreservesFiniteLimits (Action.forget FintypeCat _ ⋙ FintypeCat.incl)
  apply comp_preservesFiniteLimits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreGaloisCategory (Action FintypeCat G)
  body: inferInstance
  monoInducesIsoOnDirectSummand {_ _} i _ :=
    haveI : Mono ((forget (Action FintypeCat G)).map i) := map_mono (forget _) i
    ⟨Action.imageComplement G i, Action.imageComplementIncl G i,
⟨isColimitOfReflects (Action.forget _ _ ⋙ FintypeCat.incl)
      (isColimitMapCoconeBinaryCofan

中文:
实例 :
  签名: PreGaloisCategory (Action FintypeCat G)
  定义体: inferInstance
  monoInducesIsoOnDirectSummand {_ _} i _ :=
    haveI : Mono ((forget (Action FintypeCat G)).map i) := map_mono (forget _) i
    ⟨Action.imageComplement G i, Action.imageComplementIncl G i,
⟨isColimitOfReflects (Action.forget _ _ ⋙ FintypeCat.incl)
      (isColimitMapCoconeBinaryCofan
-/
instance : PreGaloisCategory (Action FintypeCat G) where
  hasQuotientsByFiniteGroups _ _ _ := inferInstance
  monoInducesIsoOnDirectSummand {_ _} i _ :=
    haveI : Mono ((forget (Action FintypeCat G)).map i) := map_mono (forget _) i
    ⟨Action.imageComplement G i, Action.imageComplementIncl G i,
⟨isColimitOfReflects (Action.forget _ _ ⋙ FintypeCat.incl)
      (isColimitMapCoconeBinaryCofanEquiv (forget _) i _).symm
      (Types.isCoprodOfMono ((forget _).map i))⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiberFunctor (Action.forget FintypeCat G)
  body: ⟨fun _ => inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (_ : IsIso f.hom) => inferInstance⟩

中文:
实例 :
  签名: FiberFunctor (Action.forget FintypeCat G)
  定义体: ⟨fun _ => inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (_ : IsIso f.hom) => inferInstance⟩
-/
noncomputable instance : FiberFunctor (Action.forget FintypeCat G) where
  preservesFiniteCoproducts := ⟨fun _ => inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (_ : IsIso f.hom) => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiberFunctor (forget₂ (Action FintypeCat G) FintypeCat)
  body: inferInstanceAs FiberFunctor (Action.forget FintypeCat G)

中文:
实例 :
  签名: FiberFunctor (forget₂ (Action FintypeCat G) FintypeCat)
  定义体: inferInstanceAs FiberFunctor (Action.forget FintypeCat G)

Depends on / 依赖: Action, Action.forget, FiberFunctor, FintypeCat, cat_disch, forget
-/
noncomputable instance : FiberFunctor (forget₂ (Action FintypeCat G) FintypeCat) :=
inferInstanceAs FiberFunctor (Action.forget FintypeCat G)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GaloisCategory (Action FintypeCat G)
  body: ⟨Action.forget FintypeCat G, ⟨inferInstance⟩⟩

中文:
实例 :
  签名: GaloisCategory (Action FintypeCat G)
  定义体: ⟨Action.forget FintypeCat G, ⟨inferInstance⟩⟩

Depends on / 依赖: Action, Action.forget, FintypeCat, forget
-/
instance : GaloisCategory (Action FintypeCat G) where
  hasFiberFunctor := ⟨Action.forget FintypeCat G, ⟨inferInstance⟩⟩

/--
theorem `Action.pretransitive_of_isConnected` / 定理 `Action.pretransitive_of_isConnected`

English:
theorem Action.pretransitive_of_isConnected
  statement: (X : Action FintypeCat G)
  proof: by
    /- We show that the `G`-orbit of `x` is a non-initial subobject of `X` and hence by
    connectedness, the orbit equals `X.V`. -/
    let T : Set X.V := MulAction.orbit G x
    have : Fintype T := Fintype.ofFinite T
let : MulAction G (FintypeCat.of T) := inferInstanceAs MulAction G
      ↑(Mu

中文:
定理 Action.pretransitive_of_isConnected
  结论: (X : Action FintypeCat G)
  证明: by
    /- We show that the `G`-orbit of `x` is a non-initial subobject of `X` and hence by
    connectedness, the orbit equals `X.V`. -/
    let T : Set X.V := MulAction.orbit G x
    have : Fintype T := Fintype.ofFinite T
let : MulAction G (FintypeCat.of T) := inferInstanceAs MulAction G
      ↑(Mu
-/
theorem Action.pretransitive_of_isConnected (X : Action FintypeCat G)
    [PreGaloisCategory.IsConnected X] : MulAction.IsPretransitive G X.V where
  exists_smul_eq x y := by
    /- We show that the `G`-orbit of `x` is a non-initial subobject of `X` and hence by
    connectedness, the orbit equals `X.V`. -/
    let T : Set X.V := MulAction.orbit G x
    have : Fintype T := Fintype.ofFinite T
let : MulAction G (FintypeCat.of T) := inferInstanceAs MulAction G
      ↑(MulAction.orbit G x)
    let T' : Action FintypeCat G := Action.FintypeCat.ofMulAction G (FintypeCat.of T)
    let i : T' ⟶ X := ⟨FintypeCat.homMk Subtype.val, fun _ => rfl⟩
    have : Mono i := ConcreteCategory.mono_of_injective _ (Subtype.val_injective)
    have : IsIso i := by
      apply IsConnected.noTrivialComponent T' i
      apply (not_initial_iff_fiber_nonempty (Action.forget _ _) T').mpr
      exact Set.Nonempty.coe_sort (MulAction.nonempty_orbit x)
    have hb : Function.Bijective i.hom := by
      apply (ConcreteCategory.isIso_iff_bijective i.hom).mp
      exact map_isIso (forget₂ _ FintypeCat) i
    obtain ⟨⟨y', ⟨g, (hg : g • x = y')⟩⟩, (hy' : y' = y)⟩ := hb.surjective y
    use g
    exact hg.trans hy'

/--
theorem `Action.isConnected_of_transitive` / 定理 `Action.isConnected_of_transitive`

English:
theorem Action.isConnected_of_transitive
  statement: (X : FintypeCat) [MulAction G X]
  proof: not_initial_of_inhabited (Action.forget _ _) h.some
  noTrivialComponent Y i hm hni := by
    /- We show that the induced inclusion `i.hom` of finite sets is surjective, using the
    transitivity of the `G`-action. -/
    obtain ⟨(y : Y.V)⟩ := (not_initial_iff_fiber_nonempty (Action.forget _ _) Y).

中文:
定理 Action.isConnected_of_transitive
  结论: (X : FintypeCat) [MulAction G X]
  证明: not_initial_of_inhabited (Action.forget _ _) h.some
  noTrivialComponent Y i hm hni := by
    /- We show that the induced inclusion `i.hom` of finite sets is surjective, using the
    transitivity of the `G`-action. -/
    obtain ⟨(y : Y.V)⟩ := (not_initial_iff_fiber_nonempty (Action.forget _ _) Y).

Depends on / 依赖: Action, Action.forget, forget, h.some, not_initial_of_inhabited
-/
theorem Action.isConnected_of_transitive (X : FintypeCat) [MulAction G X]
    [MulAction.IsPretransitive G X] [h : Nonempty X] :
    PreGaloisCategory.IsConnected (Action.FintypeCat.ofMulAction G X) where
  notInitial := not_initial_of_inhabited (Action.forget _ _) h.some
  noTrivialComponent Y i hm hni := by
    /- We show that the induced inclusion `i.hom` of finite sets is surjective, using the
    transitivity of the `G`-action. -/
    obtain ⟨(y : Y.V)⟩ := (not_initial_iff_fiber_nonempty (Action.forget _ _) Y).mp hni
    have : IsIso i.hom := by
      refine (ConcreteCategory.isIso_iff_bijective i.hom).mpr ⟨?_, fun x' => ?_⟩
      · have : Mono i.hom := map_mono (forget₂ _ _) i
        exact ConcreteCategory.injective_of_mono_of_preservesPullback i.hom
      · let x : X := i.hom y
        obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G x x'
        use σ • y
        change (Y.ρ σ ≫ i.hom) y = x'
        rw [i.comm]; rw [FintypeCat.comp_apply]
        exact hσ
    apply isIso_of_reflects_iso i (Action.forget _ _)

/--
theorem `Action.isConnected_iff_transitive` / 定理 `Action.isConnected_iff_transitive`

English:
theorem Action.isConnected_iff_transitive
  given: (X : Action FintypeCat G) [Nonempty X.V]
  proof: ⟨fun _ => pretransitive_of_isConnected G X, fun _ => isConnected_of_transitive G X.V⟩

中文:
定理 Action.isConnected_iff_transitive
  条件: (X : Action FintypeCat G) [Nonempty X.V]
  证明: ⟨fun _ => pretransitive_of_isConnected G X, fun _ => isConnected_of_transitive G X.V⟩

Depends on / 依赖: isConnected_of_transitive, pretransitive_of_isConnected
-/
theorem Action.isConnected_iff_transitive (X : Action FintypeCat G) [Nonempty X.V] :
    PreGaloisCategory.IsConnected X ↔ MulAction.IsPretransitive G X.V :=
  ⟨fun _ => pretransitive_of_isConnected G X, fun _ => isConnected_of_transitive G X.V⟩

variable {G}

/--
Definition of `isoQuotientStabilizerOfIsConnected` / `isoQuotientStabilizerOfIsConnected` 的定义

English:
definition isoQuotientStabilizerOfIsConnected
  signature: (X : Action FintypeCat G)
  body: haveI : MulAction.IsPretransitive G X.V := Action.pretransitive_of_isConnected G X
  let e : X.V ≃ G ⧸ MulAction.stabilizer G x :=
(Equiv.Set.univ X.V).symm.trans
(Equiv.setCongr ((MulAction.orbit_eq_univ G x).symm)).trans
      MulAction.orbitEquivQuotientStabilizer G x
Iso.symm Action.mkIso (Finty

中文:
定义 isoQuotientStabilizerOfIsConnected
  签名: (X : Action FintypeCat G)
  定义体: haveI : MulAction.IsPretransitive G X.V := Action.pretransitive_of_isConnected G X
  let e : X.V ≃ G ⧸ MulAction.stabilizer G x :=
(Equiv.Set.univ X.V).symm.trans
(Equiv.setCongr ((MulAction.orbit_eq_univ G x).symm)).trans
      MulAction.orbitEquivQuotientStabilizer G x
Iso.symm Action.mkIso (Finty

Depends on / 依赖: Action, Action.mkIso, Action.pretransitive_of_isConnected, Equiv.Set.univ, Equiv.setCongr, FintypeCat, FintypeCat.equivEquivIso, IsPretransitive, Iso.symm, MulAction, MulAction.IsPretransitive, MulAction.orbitEquivQuotientStabilizer, MulAction.orbit_eq_univ, MulAction.stabilizer, Quotient, Quotient.exists_rep, e.symm, equivEquivIso, exists_rep, mul_smul
-/
noncomputable def isoQuotientStabilizerOfIsConnected (X : Action FintypeCat G)
    [PreGaloisCategory.IsConnected X] (x : X.V) [Fintype (G ⧸ (MulAction.stabilizer G x))] :
    X ≅ G ⧸ₐ MulAction.stabilizer G x :=
  haveI : MulAction.IsPretransitive G X.V := Action.pretransitive_of_isConnected G X
  let e : X.V ≃ G ⧸ MulAction.stabilizer G x :=
(Equiv.Set.univ X.V).symm.trans
(Equiv.setCongr ((MulAction.orbit_eq_univ G x).symm)).trans
      MulAction.orbitEquivQuotientStabilizer G x
Iso.symm Action.mkIso (FintypeCat.equivEquivIso e.symm) fun σ : G => by
    ext (a : G ⧸ MulAction.stabilizer G x)
    obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
    exact mul_smul σ τ x

end FintypeCat

end CategoryTheory
