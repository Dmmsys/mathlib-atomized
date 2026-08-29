/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.ApplyFun

/-!
# Products and coproducts in the category of topological spaces
-/

@[expose] public section

open CategoryTheory Limits Set TopologicalSpace Topology

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

/--
Definition of `piπ` / `piπ` 的定义

English:
abbreviation piπ
  signature: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι)
  body: ofHom ⟨fun f => f i, continuous_apply i⟩

中文:
缩写 piπ
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι)
  定义体: ofHom ⟨fun f => f i, continuous_apply i⟩

Depends on / 依赖: continuous_apply
-/
abbrev piπ {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) : TopCat.of (forall i, α i) ⟶ α i :=
  ofHom ⟨fun f => f i, continuous_apply i⟩

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps! pt π_app]
/--
Definition of `piFan` / `piFan` 的定义

English:
definition piFan
  signature: {ι : Type v} (α : ι -> TopCat.{max v u})
  body: Fan.mk (TopCat.of (forall i, α i)) (piπ.{v, u} α)

中文:
定义 piFan
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u})
  定义体: Fan.mk (TopCat.of (forall i, α i)) (piπ.{v, u} α)

Depends on / 依赖: Fan.mk, TopCat, TopCat.of
-/
def piFan {ι : Type v} (α : ι -> TopCat.{max v u}) : Fan α :=
  Fan.mk (TopCat.of (forall i, α i)) (piπ.{v, u} α)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `piFanIsLimit` / `piFanIsLimit` 的定义

English:
definition piFanIsLimit
  signature: {ι : Type v} (α : ι -> TopCat.{max v u})
  body: ofHom
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).hom.2) }
  uniq := by
    intro S m h
    ext x
    funext i
    simp [ContinuousMap.coe_mk, ← h ⟨i⟩]
  fac _ _ := rfl

中文:
定义 piFanIsLimit
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u})
  定义体: ofHom
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).hom.2) }
  uniq := by
    intro S m h
    ext x
    funext i
    simp [ContinuousMap.coe_mk, ← h ⟨i⟩]
  fac _ _ := rfl
-/
def piFanIsLimit {ι : Type v} (α : ι -> TopCat.{max v u}) : IsLimit (piFan α) where
  lift S := ofHom
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).hom.2) }
  uniq := by
    intro S m h
    ext x
    funext i
    simp [ContinuousMap.coe_mk, ← h ⟨i⟩]
  fac _ _ := rfl

/--
Definition of `piIsoPi` / `piIsoPi` 的定义

English:
definition piIsoPi
  signature: {ι : Type v} (α : ι -> TopCat.{max v u})
  body: (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit.{v, u} α)

中文:
定义 piIsoPi
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u})
  定义体: (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit.{v, u} α)

Depends on / 依赖: conePointUniqueUpToIso, isLimit, limit.isLimit, piFanIsLimit
-/
def piIsoPi {ι : Type v} (α : ι -> TopCat.{max v u}) : ∏ᶜ α ≅ TopCat.of (forall i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit.{v, u} α)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `piIsoPi_inv_π` / 定理 `piIsoPi_inv_π`

English:
theorem piIsoPi_inv_π
  given: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι)
  proof: by simp [piIsoPi]

中文:
定理 piIsoPi_inv_π
  条件: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι)
  证明: by simp [piIsoPi]

Depends on / 依赖: piIsoPi
-/
theorem piIsoPi_inv_π {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [piIsoPi]

/--
theorem `piIsoPi_inv_π_apply` / 定理 `piIsoPi_inv_π_apply`

English:
theorem piIsoPi_inv_π_apply
  given: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : forall i, α i)
  proof: ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x

中文:
定理 piIsoPi_inv_π_apply
  条件: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι) (x : 对任意 i, α i)
  证明: ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
theorem piIsoPi_inv_π_apply {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : forall i, α i) :
    (Pi.π α i :) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x

/--
theorem `piIsoPi_hom_apply` / 定理 `piIsoPi_hom_apply`

English:
theorem piIsoPi_hom_apply
  statement: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι)
  proof: rfl

中文:
定理 piIsoPi_hom_apply
  结论: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι)
  证明: rfl
-/
theorem piIsoPi_hom_apply {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι)
    (x : (∏ᶜ α : TopCat.{max v u})) : (piIsoPi α).hom x i = (Pi.π α i :) x := rfl

/--
Definition of `sigmaι` / `sigmaι` 的定义

English:
abbreviation sigmaι
  signature: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι)
  body: by
  refine ofHom (ContinuousMap.mk ?_ ?_)
  · apply Sigma.mk i
  · continuity

中文:
缩写 sigmaι
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι)
  定义体: by
  refine ofHom (ContinuousMap.mk ?_ ?_)
  · apply Sigma.mk i
  · continuity

Depends on / 依赖: ContinuousMap, ContinuousMap.mk, Sigma.mk, continuity
-/
abbrev sigmaι {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) : α i ⟶ TopCat.of (Σ i, α i) := by
  refine ofHom (ContinuousMap.mk ?_ ?_)
  · apply Sigma.mk i
  · continuity

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps! pt ι_app]
/--
Definition of `sigmaCofan` / `sigmaCofan` 的定义

English:
definition sigmaCofan
  signature: {ι : Type v} (α : ι -> TopCat.{max v u})
  body: Cofan.mk (TopCat.of (Σ i, α i)) (sigmaι α)

中文:
定义 sigmaCofan
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u})
  定义体: Cofan.mk (TopCat.of (Σ i, α i)) (sigmaι α)

Depends on / 依赖: Cofan.mk, TopCat, TopCat.of
-/
def sigmaCofan {ι : Type v} (α : ι -> TopCat.{max v u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σ i, α i)) (sigmaι α)

/--
Definition of `sigmaCofanIsColimit` / `sigmaCofanIsColimit` 的定义

English:
definition sigmaCofanIsColimit
  signature: {ι : Type v} (β : ι -> TopCat.{max v u})
  body: ofHom
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := by continuity }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [← h]
    congr
  fac s j := by
    cases j
    cat_disch

中文:
定义 sigmaCofanIsColimit
  签名: {ι : 类型v} (β : ι -> TopCat.{max v u})
  定义体: ofHom
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := by continuity }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [← h]
    congr
  fac s j := by
    cases j
    cat_disch
-/
def sigmaCofanIsColimit {ι : Type v} (β : ι -> TopCat.{max v u}) : IsColimit (sigmaCofan β) where
  desc S := ofHom
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := by continuity }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [← h]
    congr
  fac s j := by
    cases j
    cat_disch

/--
Definition of `sigmaIsoSigma` / `sigmaIsoSigma` 的定义

English:
definition sigmaIsoSigma
  signature: {ι : Type v} (α : ι -> TopCat.{max v u})
  body: (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit.{v, u} α)

中文:
定义 sigmaIsoSigma
  签名: {ι : 类型v} (α : ι -> TopCat.{max v u})
  定义体: (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit.{v, u} α)

Depends on / 依赖: coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, sigmaCofanIsColimit
-/
def sigmaIsoSigma {ι : Type v} (α : ι -> TopCat.{max v u}) : ∐ α ≅ TopCat.of (Σ i, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit.{v, u} α)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `sigmaIsoSigma_hom_ι` / 定理 `sigmaIsoSigma_hom_ι`

English:
theorem sigmaIsoSigma_hom_ι
  given: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι)
  proof: by simp [sigmaIsoSigma]

中文:
定理 sigmaIsoSigma_hom_ι
  条件: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι)
  证明: by simp [sigmaIsoSigma]

Depends on / 依赖: sigmaIsoSigma
-/
theorem sigmaIsoSigma_hom_ι {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).hom = sigmaι α i := by simp [sigmaIsoSigma]

/--
theorem `sigmaIsoSigma_hom_ι_apply` / 定理 `sigmaIsoSigma_hom_ι_apply`

English:
theorem sigmaIsoSigma_hom_ι_apply
  given: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : α i)
  proof: ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x

中文:
定理 sigmaIsoSigma_hom_ι_apply
  条件: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι) (x : α i)
  证明: ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).hom ((Sigma.ι α i :) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x

/--
theorem `sigmaIsoSigma_inv_apply` / 定理 `sigmaIsoSigma_inv_apply`

English:
theorem sigmaIsoSigma_inv_apply
  given: {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : α i)
  proof: by
  rw [← sigmaIsoSigma_hom_ι_apply]; rw [← comp_app]; rw [← comp_app]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

中文:
定理 sigmaIsoSigma_inv_apply
  条件: {ι : 类型v} (α : ι -> TopCat.{max v u}) (i : ι) (x : α i)
  证明: by
  rw [← sigmaIsoSigma_hom_ι_apply]; rw [← comp_app]; rw [← comp_app]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Iso.hom_inv_id, comp_app, comp_id, hom_inv_id
-/
theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i :) x := by
  rw [← sigmaIsoSigma_hom_ι_apply]; rw [← comp_app]; rw [← comp_app]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

section Prod

/--
Definition of `prodFst` / `prodFst` 的定义

English:
abbreviation prodFst
  signature: {X Y : TopCat.{u}}
  body: ofHom { toFun := Prod.fst }

中文:
缩写 prodFst
  签名: {X Y : TopCat.{u}}
  定义体: ofHom { toFun := Prod.fst }

Depends on / 依赖: Prod.fst
-/
abbrev prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X :=
  ofHom { toFun := Prod.fst }

/--
Definition of `prodSnd` / `prodSnd` 的定义

English:
abbreviation prodSnd
  signature: {X Y : TopCat.{u}}
  body: ofHom { toFun := Prod.snd }

中文:
缩写 prodSnd
  签名: {X Y : TopCat.{u}}
  定义体: ofHom { toFun := Prod.snd }

Depends on / 依赖: Prod.snd
-/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ofHom { toFun := Prod.snd }

/--
Definition of `prodBinaryFan` / `prodBinaryFan` 的定义

English:
definition prodBinaryFan
  signature: (X Y : TopCat.{u})
  body: BinaryFan.mk prodFst prodSnd

中文:
定义 prodBinaryFan
  签名: (X Y : TopCat.{u})
  定义体: BinaryFan.mk prodFst prodSnd

Depends on / 依赖: BinaryFan, BinaryFan.mk, prodFst, prodSnd
-/
def prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd

/--
Definition of `prodBinaryFanIsLimit` / `prodBinaryFanIsLimit` 的定义

English:
definition prodBinaryFanIsLimit
  signature: (X Y : TopCat.{u})
  body: fun S : BinaryFan X Y => ofHom { toFun s := (S.fst s, S.snd s) }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be part of `ext x`
    refine Prod.ext ?_ ?_
   

中文:
定义 prodBinaryFanIsLimit
  签名: (X Y : TopCat.{u})
  定义体: fun S : BinaryFan X Y => ofHom { toFun s := (S.fst s, S.snd s) }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be part of `ext x`
    refine Prod.ext ?_ ?_
   

Depends on / 依赖: BinaryFan, S.fst, S.snd
-/
def prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y) where
  lift := fun S : BinaryFan X Y => ofHom { toFun s := (S.fst s, S.snd s) }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be part of `ext x`
    refine Prod.ext ?_ ?_
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e => e x at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x at h
      exact h

/--
Definition of `prodIsoProd` / `prodIsoProd` 的定义

English:
definition prodIsoProd
  signature: (X Y : TopCat.{u})
  body: (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)

中文:
定义 prodIsoProd
  签名: (X Y : TopCat.{u})
  定义体: (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)

Depends on / 依赖: conePointUniqueUpToIso, isLimit, limit.isLimit, prodBinaryFanIsLimit
-/
def prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `prodIsoProd_hom_fst` / 定理 `prodIsoProd_hom_fst`

English:
theorem prodIsoProd_hom_fst
  given: (X Y : TopCat.{u})
  proof: by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

中文:
定理 prodIsoProd_hom_fst
  条件: (X Y : TopCat.{u})
  证明: by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp, prodIsoProd
-/
theorem prodIsoProd_hom_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodFst = Limits.prod.fst := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `prodIsoProd_hom_snd` / 定理 `prodIsoProd_hom_snd`

English:
theorem prodIsoProd_hom_snd
  given: (X Y : TopCat.{u})
  proof: by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

中文:
定理 prodIsoProd_hom_snd
  条件: (X Y : TopCat.{u})
  证明: by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp, prodIsoProd
-/
theorem prodIsoProd_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodSnd = Limits.prod.snd := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

-- Note that `(x : X ⨯ Y)` would mean `(x : ↑X × ↑Y)` below:
/--
theorem `prodIsoProd_hom_apply` / 定理 `prodIsoProd_hom_apply`

English:
theorem prodIsoProd_hom_apply
  given: {X Y : TopCat.{u}} (x : ↑(X ⨯ Y))
  proof: rfl

@[reassoc (attr := simp), elementwise]

中文:
定理 prodIsoProd_hom_apply
  条件: {X Y : TopCat.{u}} (x : ↑(X ⨯ Y))
  证明: rfl

@[reassoc (attr := simp), elementwise]
-/
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑(X ⨯ Y)) :
    (prodIsoProd X Y).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x,
    (Limits.prod.snd : X ⨯ Y ⟶ _) x) := rfl

@[reassoc (attr := simp), elementwise]
/--
theorem `prodIsoProd_inv_fst` / 定理 `prodIsoProd_inv_fst`

English:
theorem prodIsoProd_inv_fst
  given: (X Y : TopCat.{u})
  proof: by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp), elementwise]

中文:
定理 prodIsoProd_inv_fst
  条件: (X Y : TopCat.{u})
  证明: by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp), elementwise]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem prodIsoProd_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.fst = prodFst := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp), elementwise]
/--
theorem `prodIsoProd_inv_snd` / 定理 `prodIsoProd_inv_snd`

English:
theorem prodIsoProd_inv_snd
  given: (X Y : TopCat.{u})
  proof: by simp [Iso.inv_comp_eq]

中文:
定理 prodIsoProd_inv_snd
  条件: (X Y : TopCat.{u})
  证明: by simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem prodIsoProd_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.snd = prodSnd := by simp [Iso.inv_comp_eq]

/--
theorem `prod_topology` / 定理 `prod_topology`

English:
theorem prod_topology
  given: {X Y : TopCat.{u}}
  proof: by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (_ ⊓ _) = _
  simp [induced_compose]
  rfl

中文:
定理 prod_topology
  条件: {X Y : TopCat.{u}}
  证明: by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (_ ⊓ _) = _
  simp [induced_compose]
  rfl

Depends on / 依赖: eq_induced, homeo.isInducing.eq_induced.trans, homeoOfIso, induced, induced_compose, isInducing, prodIsoProd
-/
theorem prod_topology {X Y : TopCat.{u}} :
    (X ⨯ Y).str =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str := by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (_ ⊓ _) = _
  simp [induced_compose]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `range_prod_map` / 定理 `range_prod_map`

English:
theorem range_prod_map
  given: {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z)
  proof: by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp_rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range, ← ConcreteCategory.comp_apply,
      Limits.prod.map_fst, Limits.prod.map_snd, ConcreteCategory.comp_apply, exists_apply_eq_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    u

中文:
定理 range_prod_map
  条件: {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z)
  证明: by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp_rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range, ← ConcreteCategory.comp_apply,
      Limits.prod.map_fst, Limits.prod.map_snd, ConcreteCategory.comp_apply, exists_apply_eq_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    u

Depends on / 依赖: Concrete, Concrete.limit_ext, ConcreteCategory, ConcreteCategory.comp_apply, Limits, Limits.prod.map_fst, Limits.prod.map_snd, Set.mem_inter_iff, Set.mem_preimage, Set.mem_range, TopCat, TopCat.prodIsoProd_inv_fst_apply, and_self_iff, comp_apply, exists_apply_eq_apply, limit_ext, map_fst, map_snd, mem_inter_iff, mem_preimage
-/
theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f inter
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp_rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range, ← ConcreteCategory.comp_apply,
      Limits.prod.map_fst, Limits.prod.map_snd, ConcreteCategory.comp_apply, exists_apply_eq_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prodIsoProd W X).inv (x₁, x₂)
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · rw [← ConcreteCategory.comp_apply]
      erw [Limits.prod.map_fst]
      rw [ConcreteCategory.comp_apply]; rw [TopCat.prodIsoProd_inv_fst_apply]
      exact hx₁
    · rw [← ConcreteCategory.comp_apply]
      erw [Limits.prod.map_snd]
      rw [ConcreteCategory.comp_apply]; rw [TopCat.prodIsoProd_inv_snd_apply]
      exact hx₂

/--
theorem `isInducing_prodMap` / 定理 `isInducing_prodMap`

English:
theorem isInducing_prodMap
  statement: {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsInducing f)
  proof: by
  constructor
  simp_rw [prod_topology, induced_inf, induced_compose, ← coe_comp,
    prod.map_fst, prod.map_snd, coe_comp, ← induced_compose (g := f), ← induced_compose (g := g)]
  rw [← hf.eq_induced]; rw [← hg.eq_induced]

中文:
定理 isInducing_prodMap
  结论: {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsInducing f)
  证明: by
  constructor
  simp_rw [prod_topology, induced_inf, induced_compose, ← coe_comp,
    prod.map_fst, prod.map_snd, coe_comp, ← induced_compose (g := f), ← induced_compose (g := g)]
  rw [← hf.eq_induced]; rw [← hg.eq_induced]

Depends on / 依赖: coe_comp, eq_induced, hf.eq_induced, hg.eq_induced, induced_compose, induced_inf, map_fst, map_snd, prod.map_fst, prod.map_snd, prod_topology, simp_rw
-/
theorem isInducing_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsInducing f)
    (hg : IsInducing g) : IsInducing (Limits.prod.map f g) := by
  constructor
  simp_rw [prod_topology, induced_inf, induced_compose, ← coe_comp,
    prod.map_fst, prod.map_snd, coe_comp, ← induced_compose (g := f), ← induced_compose (g := g)]
  rw [← hf.eq_induced]; rw [← hg.eq_induced]

/--
theorem `isEmbedding_prodMap` / 定理 `isEmbedding_prodMap`

English:
theorem isEmbedding_prodMap
  statement: {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsEmbedding f)
  proof: ⟨isInducing_prodMap hf.isInducing hg.isInducing, by
    have := (TopCat.mono_iff_injective _).mpr hf.injective
    have := (TopCat.mono_iff_injective _).mpr hg.injective
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩

中文:
定理 isEmbedding_prodMap
  结论: {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsEmbedding f)
  证明: ⟨isInducing_prodMap hf.isInducing hg.isInducing, by
    have := (TopCat.mono_iff_injective _).mpr hf.injective
    have := (TopCat.mono_iff_injective _).mpr hg.injective
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩

Depends on / 依赖: TopCat, TopCat.mono_iff_injective, hf.injective, hf.isInducing, hg.injective, hg.isInducing, injective, isInducing, isInducing_prodMap, mono_iff_injective
-/
theorem isEmbedding_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Limits.prod.map f g) :=
  ⟨isInducing_prodMap hf.isInducing hg.isInducing, by
    have := (TopCat.mono_iff_injective _).mpr hf.injective
    have := (TopCat.mono_iff_injective _).mpr hg.injective
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩

end Prod

/--
Definition of `binaryCofan` / `binaryCofan` 的定义

English:
definition binaryCofan
  signature: (X Y : TopCat.{u})
  body: BinaryCofan.mk (ofHom ⟨Sum.inl, by fun_prop⟩) (ofHom ⟨Sum.inr, by fun_prop⟩)

中文:
定义 binaryCofan
  签名: (X Y : TopCat.{u})
  定义体: BinaryCofan.mk (ofHom ⟨Sum.inl, by fun_prop⟩) (ofHom ⟨Sum.inr, by fun_prop⟩)
-/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (ofHom ⟨Sum.inl, by fun_prop⟩) (ofHom ⟨Sum.inr, by fun_prop⟩)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `binaryCofanIsColimit` / `binaryCofanIsColimit` 的定义

English:
definition binaryCofanIsColimit
  signature: (X Y : TopCat.{u})
  body: by
  refine Limits.BinaryCofan.isColimitMk (fun s => ofHom
    { toFun := Sum.elim s.inl s.inr, continuous_toFun := ?_ }) ?_ ?_ ?_
  · fun_prop
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts [ConcreteCategory.congr_hom h₁ x, ConcreteCategory.co

中文:
定义 binaryCofanIsColimit
  签名: (X Y : TopCat.{u})
  定义体: by
  refine Limits.BinaryCofan.isColimitMk (fun s => ofHom
    { toFun := Sum.elim s.inl s.inr, continuous_toFun := ?_ }) ?_ ?_ ?_
  · fun_prop
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts [ConcreteCategory.congr_hom h₁ x, ConcreteCategory.co

Depends on / 依赖: BinaryCofan, ConcreteCategory, ConcreteCategory.congr_hom, Limits, Limits.BinaryCofan.isColimitMk, Sum.elim, congr_hom, continuous_toFun, exacts, fun_prop, isColimitMk, s.inl, s.inr
-/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) := by
  refine Limits.BinaryCofan.isColimitMk (fun s => ofHom
    { toFun := Sum.elim s.inl s.inr, continuous_toFun := ?_ }) ?_ ?_ ?_
  · fun_prop
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts [ConcreteCategory.congr_hom h₁ x, ConcreteCategory.congr_hom h₂ x]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `binaryCofan_isColimit_iff` / 定理 `binaryCofan_isColimit_iff`

English:
theorem binaryCofan_isColimit_iff
  given: {X Y : TopCat.{u}} (c : BinaryCofan X Y)
  proof: by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.left⟩]; rw [← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.right⟩]
      

中文:
定理 binaryCofan_isColimit_iff
  条件: {X Y : TopCat.{u}} (c : BinaryCofan X Y)
  证明: by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.left⟩]; rw [← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.right⟩]
      

Depends on / 依赖: Set.range_comp, WalkingPair, WalkingPair.left, WalkingPair.right, binaryCofanIsColimit, c.inl, c.inr, classical, coconePointUniqueUpToIso, comp_coconePointUniqueUpToIso_inv, h.coconePointUniqueUpToIso, h.comp_coconePointUniqueUpToIso_inv, homeoOfIso, isOpenEmbedding, range_comp, symm.isOpenEmbedding.comp
-/
theorem binaryCofan_isColimit_iff {X Y : TopCat.{u}} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      IsOpenEmbedding c.inl ∧ IsOpenEmbedding c.inr ∧ IsCompl (range c.inl) (range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.left⟩]; rw [← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.right⟩]
      dsimp
      refine ⟨(homeoOfIso <| h.coconePointUniqueUpToIso
        (binaryCofanIsColimit X Y)).symm.isOpenEmbedding.comp .inl,
          (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.isOpenEmbedding.comp .inr, ?_⟩
      rw [Set.range_comp]; rw [← eq_compl_iff_isCompl]
      conv_rhs => rw [Set.range_comp]
      erw [← Set.image_compl_eq (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.bijective, Set.compl_range_inr, Set.image_comp]
    · rintro ⟨h₁, h₂, h₃⟩
      have : forall x, x in Set.range c.inl ∨ x in Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ofHom (ContinuousMap.mk ?_ ?_)
        · exact fun x =>
            if h : x in Set.range c.inl then f ((Equiv.ofInjective _ h₁.injective).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.injective).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuousAt]
        intro x
        by_cases h : x in Set.range c.inl
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_domRestrict]
            convert_to Continuous (f ∘ h₁.isEmbedding.toHomeomorph.symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            fun_prop
          · exact h₁.isOpen_range
        · revert h x
          simp only [← mem_compl_iff]
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_domRestrict]
            have : forall a, a ∉ Set.range c.inl -> a in Set.range c.inr := by
              rintro a (h : a in (Set.range c.inl)ᶜ)
              rwa [eq_compl_iff_isCompl.mpr h₃.symm]
            convert_to! Continuous
                (g ∘ h₂.isEmbedding.toHomeomorph.symm ∘ Subtype.map _ this)
            · ext ⟨x, hx⟩
              exact dif_neg hx
            apply Continuous.comp
            · exact g.hom.continuous_toFun
            · apply Continuous.comp (by fun_prop)
              rw [IsEmbedding.subtypeVal.isInducing.continuous_iff]
              exact continuous_subtype_val
          · change IsOpen (Set.range c.inl)ᶜ
            rw [← eq_compl_iff_isCompl.mpr h₃.symm]
            exact h₂.isOpen_range
      · intro T f g
        ext x
        simp
      · intro T f g
        ext x
        dsimp
        rw [dif_neg]
        · exact congr_arg g (Equiv.ofInjective_symm_apply _ _)
        · rintro ⟨y, e⟩
          have : c.inr x in Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
          rwa [disjoint_iff.mp h₃.1] at this
      · rintro T _ _ m rfl rfl
        ext x
        change m x = dite _ _ _
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

end TopCat
