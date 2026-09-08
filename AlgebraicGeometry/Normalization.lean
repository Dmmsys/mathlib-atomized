/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Tactic.DepRewrite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Relative Normalization

Given a qcqs morphism `f : X ⟶ Y`, we define the relative normalization `f.normalization`,
along with the maps that `f` factor into:
- `f.toNormalization : X ⟶ f.normalization`: a dominant morphism
- `f.fromNormalization : f.normalization ⟶ Y`: an integral morphism

It satisfies the universal property:
For any factorization `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
The factorization map is `AlgebraicGeometry.Scheme.Hom.normalizationDesc`, and the uniqueness result
is `AlgebraicGeometry.Scheme.Hom.normalization.hom_ext`.

We also show that normalization commutes with disjoint unions and smooth base change.

-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open AffineZariskiSite

set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism `f : X ⟶ Y`, this is the presheaf of integral closure of `Y` in `X`. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalizationDiagram** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationDiagram : Y.Opensᵒᵖ ⥤ CommRingCat where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `f : X ⟶ Y`, this is the presheaf of integral closure of `Y` in
 `X`.
-/
def normalizationDiagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx ↦ by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rfl⟩ := Opposite.op_surjective V
      algebraize [(f.app U).hom, (f.app V).hom, (Y.presheaf.map i).hom,
        (X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom,
        (f.appLE V (f ⁻¹ᵁ U) (f.preimage_mono i.unop.le)).hom]
      have : IsScalarTower Γ(Y, V) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' <| by
        simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]; rfl
      have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
      exact (hx.map (IsScalarTower.toAlgHom Γ(Y, V) _ Γ(X, f ⁻¹ᵁ U))).tower_top)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

/-- The inclusion from the structure presheaf of `Y` to the integral closure of `Y` in `X`. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalizationDiagramMap** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationDiagramMap : Y.presheaf ⟶ f.normalizationDiagram where app U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from the structure presheaf of `Y` to the integral closure of `Y` 
in `X`.
-/
def normalizationDiagramMap : Y.presheaf ⟶ f.normalizationDiagram where
  app U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

variable [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.coequifibered_normalizationDiagramMap** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：coequifibered_normalizationDiagramMap : ((toOpensFunctor Y).op.whiskerLeft
 f.normalizationDiagramMap).Coequifibered
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le`：basicOpen_le (U
 : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f <= U
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLo
calizationAway`：coequifibered_iff_forall_isLocalizationAway {F : X.AffineZariski
Siteᵒᵖ ⥤ CommRingCat} {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presh…
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.Scheme.Hom.preimage_basicOpen`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) {U : Y.Opens} (r : ↑(Y.presheaf.obj (Opposite.op U))),  
 (TopologicalSpace.Opens.map f.base).…
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`：isLocalization_basic
Open_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSepar
ated U.1) (f : Γ(X, U)) : IsLocalization…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isCompact_preimage`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] {U : Y.Opens},   IsCo
mpact ↑U → IsCompact ↑((TopologicalSp…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiSeparated f] {U : Y.Opens
},   IsQuasiSeparated ↑U → IsQuasiSeparated …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isQuasiSeparated`：∀ {X : AlgebraicGeometr
y.Scheme} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsQuasiSeparated ↑U
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.Away.integralClosure`：∀ {R : Type u_1} [inst : CommRing R
] {S : Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S] {Rf : Type u_5}   
{Sf : Type u_6} [inst_3 :…
-/
lemma coequifibered_normalizationDiagramMap :
    ((toOpensFunctor Y).op.whiskerLeft f.normalizationDiagramMap).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) :=
    ((normalizationDiagram f).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    U.2.isLocalization_basicOpen _
  have : IsLocalization.Away ((algebraMap ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ U.1)) r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  change IsLocalization.Away ((algebraMap Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) r)
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
  let : Algebra ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.appLE _ _ (f.preimage_mono (Y.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE, AffineZariskiSite.basicOpen]
  have : IsScalarTower (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
    Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := .of_algebraMap_eq' rfl
  exact IsLocalization.Away.integralClosure r

@[deprecated (since := "2026-02-01")]
alias preservesLocalization_normalizationDiagramMap := coequifibered_normalizationDiagramMap

/-- The diagram of affine schemes that we glue to form the normalization. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalizationGlueData** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationGlueData
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Hom.coequifibered_normalizationDiagramMap`：coeq
uifibered_normalizationDiagramMap : ((toOpensFunctor Y).op.whiskerLeft f.normali
zationDiagramMap).Coequifibered

--- 原说明 ---
The diagram of affine schemes that we glue to form the normalization.
-/
def normalizationGlueData := relativeGluingData f.coequifibered_normalizationDiagramMap
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (f.normalizationGlueData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- Given `f : X ⟶ Y`, `f.normalization` is the relative normalization of `Y` in `X`. -/
@[stacks 035H]
/-
**AlgebraicGeometry.Scheme.Hom.normalization** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：normalization : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X ⟶ Y`, `f.normalization` is the relative normalization of `Y` in `X`
.
-/
def normalization : Scheme := f.normalizationGlueData.glued

/-- This is the open cover of `f.normalization` by `Spec` of integral closures of `Γ(Y, U)`
in `Γ(X, f ⁻¹ U)` where `U` ranges over all affine opens. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalizationOpenCover** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationOpenCover : f.normalization.OpenCover
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the open cover of `f.normalization` by `Spec` of integral closures of `Γ
(Y, U)`
in `Γ(X, f ⁻¹ U)` where `U` ranges over all affine opens.
-/
def normalizationOpenCover : f.normalization.OpenCover :=
  f.normalizationGlueData.cover

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The dominant morphism into the relative normalization. -/
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：toNormalization : X ⟶ f.normalization
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion

--- 原说明 ---
The dominant morphism into the relative normalization.
-/
def toNormalization : X ⟶ f.normalization :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦ letI := (f.app U.1).hom.toAlgebra
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      |>.val.toRingHom) ≫ f.normalizationOpenCover.f U) fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp [normalizationOpenCover]
  rw [← colimit.w f.normalizationGlueData.functor i]
  dsimp [normalizationGlueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_toNormalization (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    (f ⁻¹ᵁ U.1).ι ≫ f.toNormalization = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) |>.val.toRingHom) ≫
        f.normalizationOpenCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ f.toNormalization
  · congr 1; simp
  delta toNormalization
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

/-- The morphism from the relative normalization to itself. This map is integral. -/
/-
**AlgebraicGeometry.Scheme.Hom.fromNormalization** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：fromNormalization : f.normalization ⟶ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from the relative normalization to itself. This map is integral.
-/
def fromNormalization : f.normalization ⟶ Y :=
  f.normalizationGlueData.toBase

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_fromNormalization (U : Y.affineOpens) :
    f.normalizationOpenCover.f U ≫ f.fromNormalization =
      Spec.map (f.normalizationDiagramMap.app (.op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.fromNormalization_preimage** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：fromNormalization_preimage (U : Y.affineOpens) : f.fromNormalization ⁻¹ᵁ U
 = (f.normalizationOpenCover.f U).opensRange
参数：U : Y.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instIsOpenImmersionι`：∀ {J : 
Type w} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J 
AlgebraicGeometry.Scheme)   [inst_1 : ∀ {i j : J} (f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用引理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_ope
nsRange_ι`：toBase_preimage_eq_opensRange_ι (i : 𝒰.I₀) : d.toBase ⁻¹ᵁ (𝒰.f i).ope
nsRange = (colimit.ι d.functor i).opensRange
-/
lemma fromNormalization_preimage (U : Y.affineOpens) :
    f.fromNormalization ⁻¹ᵁ U = (f.normalizationOpenCover.f U).opensRange := by
  simpa using! f.normalizationGlueData.toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：toNormalization_fromNormalization : f.toNormalization ≫ f.fromNormalizatio
n = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用引理 `TopologicalSpace.IsOpenCover.comap`：comap (hv : IsOpenCover v) (f : C(X,
 Y)) : IsOpenCover fun k => (v k).comap f
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ι_toNormalization_assoc`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f]   [inst_1
 : AlgebraicGeometry.QuasiSeparated f] (U …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.ι_fromNormalization`：ι_fromNormalization (U
 : Y.affineOpens) : f.normalizationOpenCover.f U ≫ f.fromNormalization = Spec.ma
p (f.normalizationDiagramMap.app (.op …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality_assoc`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme}   (
h : AlgebraicGeometry.Spec (Y.presheaf.obj (O…
· 使用引理 `AlgebraicGeometry.IsAffineOpen.toSpecΓ_fromSpec`：toSpecΓ_fromSpec : U.to
SpecΓ ≫ hU.fromSpec = U.ι
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalization_fromNormalization :
    f.toNormalization ≫ f.fromNormalization = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (f.ι_toNormalization_assoc _ _).trans ?_
  rw [f.ι_fromNormalization, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegralHom f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsIntegralHom _ U.2.isoSpec.hom]
  have : (f.normalizationDiagramMap.app (.op U)).hom.IsIntegral := by
    let := (f.app U).hom.toAlgebra
    change (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  convert! IsIntegralHom.SpecMap_iff.mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, ι_fromNormalization]

set_option backward.isDefEq.respectTransparency.types false in
/-- The sections of the relative normalization on the preimage of an affine open is isomorphic to
the integral closure. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.normalizationObjIso** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationObjIso {U : Y.Opens} (hU : IsAffineOpen U) : letI
参数：hU : IsAffineOpen U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def normalizationObjIso {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  f.normalization.presheaf.mapIso (eqToIso
    (by simpa using! (f.fromNormalization_preimage ⟨U, hU⟩).symm)).op ≪≫
  (f.normalizationOpenCover.f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization_app_preimage** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：toNormalization_app_preimage (U : Y.affineOpens) : let
参数：U : Y.affineOpens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization`：toNormal
ization_fromNormalization : f.toNormalization ≫ f.fromNormalization = f
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_preimage_self`：ι_preimage_self : U.ι ⁻¹
ᵁ U = ⊤
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.fromNormalization_preimage`：fromNormalizati
on_preimage (U : Y.affineOpens) : f.fromNormalization ⁻¹ᵁ U = (f.normalizationOp
enCover.f U).opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Hom.ι_toNormalization`：ι_toNormalization (U : Y
.affineOpens) : letI
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appLE`：comp_appLE {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (U V e) : (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_appLE`：ι_appLE (V W e) : U.ι.appLE V W 
e = X.presheaf.map (homOfLE (x
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op
（共 44 条，此处仅展示前 30 条）
-/
lemma toNormalization_app_preimage (U : Y.affineOpens) :
    let := (f.app U.1).hom.toAlgebra
    dsimp% f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) =
      (f.normalizationObjIso U.2).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  let := (f.app U.1).hom.toAlgebra
  dsimp [normalizationObjIso]
  change _ = f.normalization.presheaf.map (eqToHom (by simp [fromNormalization_preimage])).op ≫
      ((f.normalizationOpenCover.f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op
  have H : f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ f.toNormalization) ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert! congr($(Scheme.Hom.congr_app (f.ι_toNormalization U) (f.fromNormalization ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H).op) using 1
  · simp [Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← Functor.map_inv, inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.fromNormalization_app** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：fromNormalization_app {U : Y.Opens} (hU : IsAffineOpen U) : f.fromNormaliz
ation.app U = CommRingCat.ofHom (algebraMap _ _) ≫ (f.normalizationObjIso hU).in
v
参数：hU : IsAffineOpen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Hom.isIso_app`：isIso_app (V : Y.Opens) (hV : V 
<= f.opensRange) : IsIso (f.app V)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.Scheme.Hom.ι_fromNormalization`：ι_fromNormalization (U
 : Y.affineOpens) : f.normalizationOpenCover.f U ≫ f.fromNormalization = Spec.ma
p (f.normalizationDiagramMap.app (.op …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
· 使用定理 `CategoryTheory.instIsSplitMonoMap`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {X Y : C} (f : Y ⟶…
· 使用定理 `CategoryTheory.instIsSplitMonoOppositeOpOfIsSplitMono`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} [CategoryTheory
.IsSplitEpi f],   CategoryTheory.IsSplitMon…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`：fromSpec_app_self : hU
.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (e
qToHom hU.fromSpec_preimage_self).op
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
（共 36 条，此处仅展示前 30 条）
-/
lemma fromNormalization_app {U : Y.Opens} (hU : IsAffineOpen U) :
    f.fromNormalization.app U = CommRingCat.ofHom (algebraMap _ _) ≫
      (f.normalizationObjIso hU).inv := by
  let := (f.app U).hom.toAlgebra
  have : IsIso (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)) :=
    Scheme.Hom.isIso_app _ _ (by simp [← fromNormalization_preimage])
  have H : ⊤ = ((normalizationOpenCover f).f ⟨U, hU⟩ ≫ fromNormalization f) ⁻¹ᵁ U := by
    rw [f.ι_fromNormalization]; simp
  rw [← cancel_mono (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)),
    ← Scheme.Hom.comp_app, Scheme.Hom.congr_app (f.ι_fromNormalization ⟨U, hU⟩) U,
    ← cancel_mono (((normalizationOpenCover f).X ⟨U, hU⟩).presheaf.map (eqToHom H).op)]
  dsimp [normalizationObjIso]
  rw [IsAffineOpen.fromSpec_app_self]
  simp only [app_eq_appLE, Category.assoc, map_appLE, appLE_map]
  simp [Scheme.Hom.appLE, ← ΓSpecIso_inv_naturality]
  rfl
/-
**AlgebraicGeometry.Scheme.Hom.normalizationObjIso_hom_val** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationObjIso_hom_val {U : Y.Opens} (hU : IsAffineOpen U) : letI
参数：hU : IsAffineOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.eq_1`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (e : V ≤ (TopologicalSpace.Opens.m
ap f.base).obj U),   Algebrai…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `AlgebraicGeometry.Scheme.Hom.toNormalization_app_preimage`：toNormalizati
on_app_preimage (U : Y.affineOpens) : let
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma normalizationObjIso_hom_val {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom =
    f.toNormalization.appLE _ _ (by simp [← Scheme.Hom.comp_preimage]) := by
  rw [appLE, f.toNormalization_app_preimage ⟨U, hU⟩, Category.assoc]
  simp [← Functor.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[stacks 03GP]
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegralHom f] : IsIso f.toNormalization := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    f.normalizationOpenCover).mpr fun U ↦ ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pullbackFst, ← f.fromNormalization_preimage, ← Scheme.Hom.comp_preimage])
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _)
    (e ≪≫ (U.2.preimage f).isoSpec).inv]
  let := (f.app U.1).hom.toAlgebra
  convert_to! IsIso (Spec.map (CommRingCat.ofHom
      (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom))
  · rw [← cancel_mono (f.normalizationOpenCover.f U), ← cancel_epi (U.2.preimage f).isoSpec.hom]
    simp [e, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom,
      Hom.ι_toNormalization]
  have : integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) = ⊤ := by
    rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact IsIntegralHom.isIntegral_app _ _ U.2
  rw [this]
  exact inferInstanceAs (IsIso (Scheme.Spec.mapIso (Subalgebra.topEquiv
    (R := Γ(Y, U.1)) (A := ↑Γ(X, f ⁻¹ᵁ U.1))).toCommRingCatIso.op).hom)
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAffineHom f] : IsAffineHom f.toNormalization := by
  apply MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiCompact f.toNormalization := by
  apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ f.fromNormalization
  · infer_instance
  · rw [Hom.toNormalization_fromNormalization]
    infer_instance
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiSeparated f.toNormalization := by
  suffices QuasiSeparated (Hom.toNormalization f ≫ Hom.fromNormalization f) from
    .of_comp _ f.fromNormalization
  rw [Hom.toNormalization_fromNormalization]
  infer_instance

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.ker_toNormalization** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：ker_toNormalization : f.toNormalization.ker = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top`：ext_of_iSup_
eq_top {I J : X.IdealSheafData} {ι : Type*} (U : ι -> X.affineOpens) (hU : ⨆ i, 
(U i).1 = ⊤) (H : forall i, I.ideal (U i) = J.id…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsIntegralHom.toIsAffineHom`：∀ {X Y : AlgebraicGeometr
y.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsIntegralHom f],   AlgebraicGeo
metry.IsAffineHom f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用引理 `TopologicalSpace.IsOpenCover.comap`：comap (hv : IsOpenCover v) (f : C(X,
 Y)) : IsOpenCover fun k => (v k).comap f
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instQuasiCompactToNormalization`：∀ {X Y : A
lgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f]  
 [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback`
：mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y) [PreservesLimitsO
fShape WalkingCospan (forget C)] : Mono f ↔ Function.Injectiv…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.eq_1`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] (x x_1 : C) (f : x ⟶ x_1),   CategoryTheory
.MorphismProperty.monomorphisms C f = Ca…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma ker_toNormalization : f.toNormalization.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.fromNormalization ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U ↦ ?_
  simp only [ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot,
    ← ConcreteCategory.mono_iff_injective_of_preservesPullback, ← MorphismProperty.monomorphisms]
  simp only [toNormalization_app_preimage,
    eqToHom_op, MorphismProperty.cancel_left_of_respectsIso,
    MorphismProperty.cancel_right_of_respectsIso]
  rw [MorphismProperty.monomorphisms, @ConcreteCategory.mono_iff_injective_of_preservesPullback]
  exact Subtype.val_injective
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDominant f.toNormalization := by
  have := congr(($(f.ker_toNormalization).support : Set f.normalization))
  rw [IdealSheafData.support_bot, Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[stacks 0AXN]
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsReduced X] : IsReduced f.normalization :=
  have (i : _) : IsReduced ((normalizationOpenCover f).X i) := by
    have : _root_.IsReduced ((normalizationDiagram f).obj (.op i.1)) :=
      let := (f.app i.1).hom.toAlgebra
      isReduced_of_injective (Subalgebra.val _) Subtype.val_injective
    dsimp [normalizationOpenCover, normalizationGlueData, relativeGluingData]
    infer_instance
  .of_openCover _ f.normalizationOpenCover
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegral X] : IsIntegral f.normalization :=
  have : IrreducibleSpace f.normalization := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toNormalization.continuous.continuousOn).closure
    simpa using f.toNormalization.denseRange.closure_range.symm
  isIntegral_of_irreducibleSpace_of_isReduced _

section UniversalProperty

variable {T : Scheme.{u}} (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an qcqs morphism `f : X ⟶ Y`, which factors into `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
(See `normalization.hom_ext` for the uniqueness result) -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.normalizationDesc** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：normalizationDesc (H : f = f₁ ≫ f₂) : f.normalization ⟶ T
参数：H : f = f₁ ≫ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def normalizationDesc (H : f = f₁ ≫ f₂) : f.normalization ⟶ T := by
  refine colimit.desc _
    { pt := _
      ι.app U := Spec.map (CommRingCat.ofHom ((f₁.appLE _ _ (by simp [H])).hom.codRestrict _
        fun x ↦ ?_)) ≫ (U.2.preimage f₂).fromSpec,
      ι.naturality := ?_ }
  · algebraize [(f.app U.1).hom, (f₂.app U.1).hom,
      (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])).hom]
    have : IsScalarTower Γ(Y, U.1) Γ(T, f₂ ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ U.1) := .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Hom.app_eq_appLE, Hom.appLE_comp_appLE, ← H]
    exact .algebraMap (R := Γ(Y, U.1)) (B := Γ(X, f ⁻¹ᵁ U.1)) (f₂.isIntegral_app U.1 U.2 x)
  · intros U V i
    dsimp [normalizationGlueData, relativeGluingData]
    rw [Category.comp_id, ← Spec.map_comp_assoc, ← (V.2.preimage f₂).map_fromSpec (U.2.preimage f₂)
      (homOfLE (f₂.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le))).op,
      ← Spec.map_comp_assoc]
    congr 2
    ext i
    apply Subtype.ext
    dsimp [normalizationDiagram]
    simp only [← CommRingCat.comp_apply, appLE_map, map_appLE]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：toNormalization_normalizationDesc (H : f = f₁ ≫ f₂) : f.toNormalization ≫ 
f.normalizationDesc f₁ f₂ H = f₁
参数：H : f = f₁ ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用引理 `TopologicalSpace.IsOpenCover.comap`：comap (hv : IsOpenCover v) (f : C(X,
 Y)) : IsOpenCover fun k => (v k).comap f
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ι_toNormalization_assoc`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f]   [inst_1
 : AlgebraicGeometry.QuasiSeparated f] (U …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsIntegralHom.toIsAffineHom`：∀ {X Y : AlgebraicGeometr
y.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsIntegralHom f],   AlgebraicGeo
metry.IsAffineHom f
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (hUV : V ≤ (Top
ologicalSpace.Opens.map f.base).obj U) {Z : Alge…
· 使用引理 `AlgebraicGeometry.IsAffineOpen.toSpecΓ_fromSpec`：toSpecΓ_fromSpec : U.to
SpecΓ ≫ hU.fromSpec = U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalization_normalizationDesc (H : f = f₁ ≫ f₂) :
    f.toNormalization ≫ f.normalizationDesc f₁ f₂ H = f₁ := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom)) _ _ fun U ↦ ?_
  let := (f.app U.1).hom.toAlgebra
  refine (Scheme.Hom.ι_toNormalization_assoc ..).trans ?_
  dsimp [normalizationOpenCover, normalizationDesc]
  simp only [colimit.ι_desc, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])) ≫
    (U.2.preimage f₂).fromSpec = (f ⁻¹ᵁ U.1).ι ≫ f₁
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationDesc_comp (H : f = f₁ ≫ f₂) : f.normalizationDesc f₁ f₂ H ≫ f
₂ = f.fromNormalization
参数：H : f = f₁ ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.ι_toBase`：ι_toBase (i 
: 𝒰.I₀) : colimit.ι d.functor i ≫ d.toBase = d.natTrans.app i ≫ 𝒰.f i
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`：SpecMap_appLE_fro
mSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffi
neOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.…
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.congr_simp`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) (U : Y.Opens) (V : X.Opens)   (e : V ≤
 (TopologicalSpace.Opens.map f.base…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normalizationDesc_comp (H : f = f₁ ≫ f₂) :
    f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization := by
  refine colimit.hom_ext fun U ↦ ?_
  dsimp [normalizationDesc, fromNormalization]
  rw [colimit.ι_desc_assoc, (normalizationGlueData f).ι_toBase, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl, ← Spec.map_comp_assoc]
  dsimp [normalizationGlueData, relativeGluingData, restrictIsoSpec]
  rw [Category.assoc]
  congr 2
  ext i
  dsimp [normalizationDiagram, normalizationDiagramMap, RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, Hom.appLE_comp_appLE, app_eq_appLE]
  simp_rw [H]
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : f = f₁ ≫ f₂) : IsIntegralHom (f.normalizationDesc f₁ f₂ H) := by
  have : IsIntegralHom (f.normalizationDesc f₁ f₂ H ≫ f₂) := by
    rw [f.normalizationDesc_comp]; infer_instance
  exact .of_comp _ f₂

set_option backward.isDefEq.respectTransparency false in
/-- The uniqueness part of the universal property for relative normalization.
Suppose `f : X ⟶ Y` is qcqs and factors into `X ⟶ T ⟶ Y` with `T ⟶ Y` affine, then
there is at most one map `f.normalization ⟶ T` that commutes with them. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalization.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom.normalization`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.Q
uasiCompact f]   [inst_1 : AlgebraicGeometry.QuasiSeparated f] {T : AlgebraicGeo
metry.Scheme}   (f₁ f₂ : AlgebraicGeometry.Scheme.Hom.normalization f ⟶ T) (g : 
T ⟶ Y) [AlgebraicGeometry.IsAffineHom g],   CategoryTheory.CategoryStruct.comp (
AlgebraicGeometry.Scheme.Hom.toNormalization f) f₁ =       CategoryTheory.Catego
ryStruct.comp (AlgebraicGeometry.Scheme.Hom.toNormalization f) f₂ →     Category
Theory.CategoryStruct.comp f₁ g = AlgebraicGeometry.Scheme.Hom.fromNormalization
 f →       CategoryTheory.CategoryStruct.comp f₂ g = AlgebraicGeometry.Scheme.Ho
m.fromNormalization f → f₁ = f₂
参数：f : X ⟶ Y；f₁ f₂ : AlgebraicGeometry.Scheme.Hom.normalization f ⟶ T；g : T ⟶ Y；
AlgebraicGeometry.Scheme.Hom.toNormalization f；AlgebraicGeometry.Scheme.Hom.toNo
rmalization f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `AlgebraicGeometry.IsIntegralHom.toIsAffineHom`：∀ {X Y : AlgebraicGeometr
y.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsIntegralHom f],   AlgebraicGeo
metry.IsAffineHom f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineHom.of_comp`：∀ {X Y Z : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.IsAffineHom (CategoryTheory.Cat
egoryStruct.comp f g)] [Alg…
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用引理 `AlgebraicGeometry.eq_of_SpecMap_comp_eq_of_isAffineOpen`：eq_of_SpecMap_c
omp_eq_of_isAffineOpen {R S : CommRingCat} {X : Scheme} (φ : R ⟶ S) (hφ : Functi
on.Injective φ) {f g : Spec R ⟶ X} (U : X.Ope…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.ι_fromNormalization`：ι_fromNormalization (U
 : Y.affineOpens) : f.normalizationOpenCover.f U ≫ f.fromNormalization = Spec.ma
p (f.normalizationDiagramMap.app (.op …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_self`：fromSpec_preimage
_self : hU.fromSpec ⁻¹ᵁ U = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization`：toNormal
ization_fromNormalization : f.toNormalization ≫ f.fromNormalization = f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appLE`：comp_appLE {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (U V e) : (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用引理 `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`：SpecMap_appLE_fro
mSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffi
neOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The uniqueness part of the universal property for relative normalization.
Suppose `f : X ⟶ Y` is qcqs and factors into `X ⟶ T ⟶ Y` with `T ⟶ Y` affine, th
en
there is at most one map `f.normalization ⟶ T` that commutes with them.
-/
lemma normalization.hom_ext (f₁ f₂ : f.normalization ⟶ T) (g : T ⟶ Y) [IsAffineHom g]
    (H₁ : f.toNormalization ≫ f₁ = f.toNormalization ≫ f₂)
    (hf₁ : f₁ ≫ g = f.fromNormalization) (hf₂ : f₂ ≫ g = f.fromNormalization) : f₁ = f₂ := by
  apply f.normalizationOpenCover.hom_ext _ _ fun U ↦ ?_
  let := (f.app U.1).hom.toAlgebra
  have : IsAffineHom f₁ := have : IsAffineHom (f₁ ≫ g) := hf₁ ▸ inferInstance; .of_comp _ g
  have : IsAffineHom f₂ := have : IsAffineHom (f₂ ≫ g) := hf₂ ▸ inferInstance; .of_comp _ g
  let f₀ := toNormalization f ≫ f₁
  have hf₀ : f₀ = toNormalization f ≫ f₂ := H₁
  refine eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom)
    Subtype.val_injective _ (U.2.preimage g) ?_ ?_ ?_
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₁, ι_fromNormalization]; simp
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₂, ι_fromNormalization]; simp
  · have h₁ : f ⁻¹ᵁ U.1 ≤ f₀ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, f₀, Category.assoc,
        hf₁, toNormalization_fromNormalization]; rfl
    have h₁' : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂, toNormalization_fromNormalization]
    have h₂ : fromNormalization f ⁻¹ᵁ U.1 = f₁ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₁]
    have h₂' : fromNormalization f ⁻¹ᵁ U.1 = f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂]
    have h₃ : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ fromNormalization f ⁻¹ᵁ U.1 := by
      simp [← Scheme.Hom.comp_preimage]
    trans Spec.map (f₀.appLE (g ⁻¹ᵁ U.val) (f ⁻¹ᵁ U.val) h₁) ≫ (U.prop.preimage g).fromSpec
    · simp only [AlgHom.toRingHom_eq_coe, comp_appLE, Spec.map_comp, Category.assoc, f₀]
      rw [app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₁ ⁻¹ᵁ g ⁻¹ᵁ U.val) (f ⁻¹ᵁ U.val) h₁ =
        f.normalization.presheaf.map (eqToHom h₂).op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.val) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this, f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top, normalizationObjIso, normalizationDiagram]
      #adaptation_note /-- Before #36613, the following simp call was not needed. -/
      simp [← Spec.map_comp_assoc, -Spec.map_comp]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, hf₀, comp_appLE, Spec.map_comp, Category.assoc,
        app_eq_appLE]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) h₁'.le =
        f.normalization.presheaf.map (eqToHom h₂').op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.1) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this, f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top, normalizationObjIso, normalizationDiagram]
      #adaptation_note /-- Before #36613, the following simp call was not needed. -/
      simp [← Spec.map_comp_assoc, -Spec.map_comp]
      rfl

end UniversalProperty

section Coproduct

variable {U V : Scheme} {iU : U ⟶ X} {iV : V ⟶ X} (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact iU] [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV]

set_option backward.isDefEq.respectTransparency false in
/-- The normalization of `Y` in a coproduct is isomorphic to the coproduct of the normalizations in
each of the components. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationCoprodIso : (iU ≫ f).normalization ⨿ (iV ≫ f).normalization ≅
 f.normalization where hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …

--- 原说明 ---
The normalization of `Y` in a coproduct is isomorphic to the coproduct of the no
rmalizations in
each of the components.
-/
noncomputable def normalizationCoprodIso :
    (iU ≫ f).normalization ⨿ (iV ≫ f).normalization ≅ f.normalization where
  hom := coprod.desc
      ((iU ≫ f).normalizationDesc (iU ≫ f.toNormalization) f.fromNormalization (by simp))
      ((iV ≫ f).normalizationDesc (iV ≫ f.toNormalization) f.fromNormalization (by simp))
  inv := f.normalizationDesc ((e.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
      coprod.map (iU ≫ f).toNormalization (iV ≫ f).toNormalization)
      (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) <| by
    simp only [← Iso.inv_comp_eq, Category.assoc]
    apply coprod.hom_ext <;> simp
  hom_inv_id := by
    ext
    · refine Scheme.Hom.normalization.hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iU ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inl :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.left⟩
      simp [reassoc_of% H]
    · refine Scheme.Hom.normalization.hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iV ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inr :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.right⟩
      simp [reassoc_of% H]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization ?_ (by simp) (by simp)
    rw [← cancel_epi (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).inv]
    apply coprod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization_inl_normalizationCoprodIso_hom** 
是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：toNormalization_inl_normalizationCoprodIso_hom : (iU ≫ f).toNormalization 
≫ coprod.inl ≫ (f.normalizationCoprodIso e).hom = iU ≫ f.toNormalization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc`：toNormal
ization_normalizationDesc (H : f = f₁ ≫ f₂) : f.toNormalization ≫ f.normalizatio
nDesc f₁ f₂ H = f₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalization_inl_normalizationCoprodIso_hom :
    (iU ≫ f).toNormalization ≫ coprod.inl ≫ (f.normalizationCoprodIso e).hom =
      iU ≫ f.toNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization_inr_normalizationCoprodIso_hom** 
是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：toNormalization_inr_normalizationCoprodIso_hom : (iV ≫ f).toNormalization 
≫ coprod.inr ≫ (f.normalizationCoprodIso e).hom = iV ≫ f.toNormalization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc`：toNormal
ization_normalizationDesc (H : f = f₁ ≫ f₂) : f.toNormalization ≫ f.normalizatio
nDesc f₁ f₂ H = f₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalization_inr_normalizationCoprodIso_hom :
    (iV ≫ f).toNormalization ≫ coprod.inr ≫ (f.normalizationCoprodIso e).hom =
      iV ≫ f.toNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.inl_toNormalization_normalizationCoprodIso_inv** 
是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：inl_toNormalization_normalizationCoprodIso_inv : iU ≫ f.toNormalization ≫ 
(f.normalizationCoprodIso e).inv = (iU ≫ f).toNormalization ≫ coprod.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toNormalization_inl_normalizationCoprodIso_
hom_assoc`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeome
try.QuasiCompact f]   [inst_1 : AlgebraicGeometry.QuasiSeparated f] {U …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_toNormalization_normalizationCoprodIso_inv :
    iU ≫ f.toNormalization ≫ (f.normalizationCoprodIso e).inv =
      (iU ≫ f).toNormalization ≫ coprod.inl := by
  simp [← toNormalization_inl_normalizationCoprodIso_hom_assoc f e]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.inr_toNormalization_normalizationCoprodIso_inv** 
是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：inr_toNormalization_normalizationCoprodIso_inv : iV ≫ f.toNormalization ≫ 
(f.normalizationCoprodIso e).inv = (iV ≫ f).toNormalization ≫ coprod.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toNormalization_inr_normalizationCoprodIso_
hom_assoc`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeome
try.QuasiCompact f]   [inst_1 : AlgebraicGeometry.QuasiSeparated f] {U …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_toNormalization_normalizationCoprodIso_inv :
    iV ≫ f.toNormalization ≫ (f.normalizationCoprodIso e).inv =
      (iV ≫ f).toNormalization ≫ coprod.inr := by
  simp [← toNormalization_inr_normalizationCoprodIso_hom_assoc f e]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.inl_normalizationCoprodIso_hom_fromNormalization*
* 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：inl_normalizationCoprodIso_hom_fromNormalization : coprod.inl ≫ (f.normali
zationCoprodIso e).hom ≫ f.fromNormalization = (iU ≫ f).fromNormalization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp`：normalizationDesc_c
omp (H : f = f₁ ≫ f₂) : f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_normalizationCoprodIso_hom_fromNormalization :
    coprod.inl ≫ (f.normalizationCoprodIso e).hom ≫ f.fromNormalization =
      (iU ≫ f).fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.inr_normalizationCoprodIso_hom_fromNormalization*
* 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：inr_normalizationCoprodIso_hom_fromNormalization : coprod.inr ≫ (f.normali
zationCoprodIso e).hom ≫ f.fromNormalization = (iV ≫ f).fromNormalization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiCompact f
]   [inst_1 : AlgebraicGeometry.QuasiSeparated f],   …
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp`：normalizationDesc_c
omp (H : f = f₁ ≫ f₂) : f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_normalizationCoprodIso_hom_fromNormalization :
    coprod.inr ≫ (f.normalizationCoprodIso e).hom ≫ f.fromNormalization =
      (iV ≫ f).fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

@[reassoc, simp]
/-
**AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso_inv_coprodDesc_fromNormali
zation** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationCoprodIso_inv_coprodDesc_fromNormalization : (f.normalization
CoprodIso e).inv ≫ coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormaliza
tion = f.fromNormalization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp`：normalizationDesc_c
omp (H : f = f₁ ≫ f₂) : f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normalizationCoprodIso_inv_coprodDesc_fromNormalization :
    (f.normalizationCoprodIso e).inv ≫
      coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization =
    f.fromNormalization := by
  simp [Scheme.Hom.normalizationCoprodIso]

end Coproduct

section Smooth

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison lemma between the normalization of the pullback to the pullback of the
normalization. This is an isomorphism when `g` is smooth. -/
/-
**AlgebraicGeometry.Scheme.Hom.normalizationPullback** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationPullback : (pullback.snd f g).normalization ⟶ pullback f.from
Normalization g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instQuasiCompactSndScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.QuasiCompact f],   Algebrai
cGeometry.QuasiCompact (CategoryT…
· 使用定理 `AlgebraicGeometry.instQuasiSeparatedSndScheme`：∀ {X Y S : AlgebraicGeome
try.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.QuasiSeparated f],   Alge
braicGeometry.QuasiSeparated (Categ…

--- 原说明 ---
The comparison lemma between the normalization of the pullback to the pullback o
f the
normalization. This is an isomorphism when `g` is smooth.
-/
noncomputable def normalizationPullback :
    (pullback.snd f g).normalization ⟶ pullback f.fromNormalization g :=
  (pullback.snd f g).normalizationDesc (pullback.map _ _ _ _ f.toNormalization
    (𝟙 _) (𝟙 _) (by simp) (by simp)) (pullback.snd _ _) (by simp)
  deriving IsIntegralHom

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.normalizationPullback_snd** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：normalizationPullback_snd : f.normalizationPullback g ≫ pullback.snd _ _ =
 (pullback.snd f g).fromNormalization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp`：normalizationDesc_c
omp (H : f = f₁ ≫ f₂) : f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instQuasiCompactSndScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.QuasiCompact f],   Algebrai
cGeometry.QuasiCompact (CategoryT…
· 使用定理 `AlgebraicGeometry.instQuasiSeparatedSndScheme`：∀ {X Y S : AlgebraicGeome
try.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.QuasiSeparated f],   Alge
braicGeometry.QuasiSeparated (Categ…
-/
lemma normalizationPullback_snd :
    f.normalizationPullback g ≫ pullback.snd _ _ = (pullback.snd f g).fromNormalization :=
  (pullback.snd f g).normalizationDesc_comp ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationPullback_fst** 是 Mat
hlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：toNormalization_normalizationPullback_fst : (pullback.snd f g).toNormaliza
tion ≫ f.normalizationPullback g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.toNor
malization
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instQuasiCompactSndScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.QuasiCompact f],   Algebrai
cGeometry.QuasiCompact (CategoryT…
· 使用定理 `AlgebraicGeometry.instQuasiSeparatedSndScheme`：∀ {X Y S : AlgebraicGeome
try.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.QuasiSeparated f],   Alge
braicGeometry.QuasiSeparated (Categ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc_assoc`：∀ 
{X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.QuasiComp
act f]   [inst_1 : AlgebraicGeometry.QuasiSeparated f] {T …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalization_normalizationPullback_fst :
    (pullback.snd f g).toNormalization ≫ f.normalizationPullback g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f.toNormalization := by
  simp [normalizationPullback]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-- Normalization commutes with smooth base change. -/
@[stacks 03GV]
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normalization commutes with smooth base change.
-/
instance [Smooth g] : IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd _ g ≫ g) x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ g ⁻¹ᵁ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := pullback.snd _ g x) hxU (g ⁻¹ᵁ U).2
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  have : (g.appLE U V hVU).hom.Smooth := g.smooth_appLE hU hV hVU
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    TensorProduct.toIntegralClosure_bijective_of_smooth
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

end Smooth

end AlgebraicGeometry.Scheme.Hom

