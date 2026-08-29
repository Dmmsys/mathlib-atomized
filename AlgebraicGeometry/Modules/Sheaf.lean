/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.Topology.Sheaves.Module

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`, and study its basic functoriality.

-/

@[expose] public section

universe t u

open CategoryTheory Limits TopologicalSpace SheafOfModules Bicategory

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

variable (X) in
/--
Definition of `Modules` / `Modules` 的定义

English:
definition Modules
  body: SheafOfModules.{u} X.ringCatSheaf

中文:
定义 Modules
  定义体: SheafOfModules.{u} X.ringCatSheaf

Depends on / 依赖: SheafOfModules, X.ringCatSheaf, ringCatSheaf
-/
def Modules := SheafOfModules.{u} X.ringCatSheaf

namespace Modules

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: (M N : X.Modules)
  body: SheafOfModules.Hom M N

中文:
定义 态射
  签名: (M N : X.Modules)
  定义体: SheafOfModules.Hom M N

Depends on / 依赖: SheafOfModules, SheafOfModules.Hom
-/
def Hom (M N : X.Modules) : Type u := SheafOfModules.Hom M N

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category X.Modules
  body: Modules.Hom
  __ := (inferInstance : Category (SheafOfModules.{u} X.ringCatSheaf))

中文:
实例 :
  签名: 范畴 X.Modules
  定义体: Modules.Hom
  __ := (inferInstance : Category (SheafOfModules.{u} X.ringCatSheaf))

Depends on / 依赖: Modules, Modules.Hom
-/
instance : Category X.Modules where
  Hom := Modules.Hom
  __ := (inferInstance : Category (SheafOfModules.{u} X.ringCatSheaf))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian X.Modules
  body: inferInstanceAs Abelian (SheafOfModules.{u} X.ringCatSheaf)

中文:
实例 :
  签名: 交换 X.Modules
  定义体: inferInstanceAs Abelian (SheafOfModules.{u} X.ringCatSheaf)

Depends on / 依赖: Abelian, SheafOfModules, X.ringCatSheaf, ringCatSheaf
-/
noncomputable instance : Abelian X.Modules :=
inferInstanceAs Abelian (SheafOfModules.{u} X.ringCatSheaf)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits X.Modules
  body: inferInstanceAs (HasLimits (SheafOfModules X.ringCatSheaf))

中文:
实例 :
  签名: 有极限 X.Modules
  定义体: inferInstanceAs (HasLimits (SheafOfModules X.ringCatSheaf))

Depends on / 依赖: HasLimits, SheafOfModules, X.ringCatSheaf, ringCatSheaf
-/
instance : HasLimits X.Modules := inferInstanceAs (HasLimits (SheafOfModules X.ringCatSheaf))
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits X.Modules
  body: inferInstanceAs (HasColimits (SheafOfModules X.ringCatSheaf))

中文:
实例 :
  签名: 有余极限 X.Modules
  定义体: inferInstanceAs (HasColimits (SheafOfModules X.ringCatSheaf))

Depends on / 依赖: HasColimits, SheafOfModules, X.ringCatSheaf, ringCatSheaf
-/
instance : HasColimits X.Modules := inferInstanceAs (HasColimits (SheafOfModules X.ringCatSheaf))

section Functor

variable (X) in
/--
Definition of `toPresheafOfModules` / `toPresheafOfModules` 的定义

English:
definition toPresheafOfModules
  signature: : X.Modules ⥤ X.PresheafOfModules
  body: SheafOfModules.forget _

中文:
定义 toPresheafOfModules
  签名: : X.Modules ⥤ X.预模层
  定义体: SheafOfModules.forget _

Depends on / 依赖: SheafOfModules, SheafOfModules.forget, forget
-/
def toPresheafOfModules : X.Modules ⥤ X.PresheafOfModules := SheafOfModules.forget _

/--
Definition of `fullyFaithfulToPresheafOfModules` / `fullyFaithfulToPresheafOfModules` 的定义

English:
definition fullyFaithfulToPresheafOfModules
  signature: : (Modules.toPresheafOfModules X).FullyFaithful
  body: SheafOfModules.fullyFaithfulForget _

中文:
定义 fullyFaithfulToPresheafOfModules
  签名: : (Modules.toPresheafOfModules X).满忠实
  定义体: SheafOfModules.fullyFaithfulForget _

Depends on / 依赖: SheafOfModules, SheafOfModules.fullyFaithfulForget, fullyFaithfulForget
-/
def fullyFaithfulToPresheafOfModules : (Modules.toPresheafOfModules X).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheafOfModules X).Full
  body: fullyFaithfulToPresheafOfModules.full

中文:
实例 :
  签名: (toPresheafOfModules X).满
  定义体: fullyFaithfulToPresheafOfModules.full

Depends on / 依赖: fullyFaithfulToPresheafOfModules, fullyFaithfulToPresheafOfModules.full
-/
instance : (toPresheafOfModules X).Full := fullyFaithfulToPresheafOfModules.full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheafOfModules X).Faithful
  body: fullyFaithfulToPresheafOfModules.faithful

中文:
实例 :
  签名: (toPresheafOfModules X).忠实
  定义体: fullyFaithfulToPresheafOfModules.faithful

Depends on / 依赖: faithful, fullyFaithfulToPresheafOfModules, fullyFaithfulToPresheafOfModules.faithful
-/
instance : (toPresheafOfModules X).Faithful := fullyFaithfulToPresheafOfModules.faithful
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheafOfModules X).IsRightAdjoint
  body: (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isRightAdjoint

中文:
实例 :
  签名: (toPresheafOfModules X).是右伴随
  定义体: (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isRightAdjoint

Depends on / 依赖: PresheafOfModules, PresheafOfModules.sheafificationAdjunction, X.ringCatSheaf.obj, isRightAdjoint, ringCatSheaf, sheafificationAdjunction
-/
instance : (toPresheafOfModules X).IsRightAdjoint :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isRightAdjoint

variable (X) in
/--
Definition of `toPresheaf` / `toPresheaf` 的定义

English:
definition toPresheaf
  signature: : X.Modules ⥤ TopCat.Presheaf Ab X
  body: toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf _

中文:
定义 toPresheaf
  签名: : X.Modules ⥤ 顶元素范畴.预层 Ab X
  定义体: toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf _

Depends on / 依赖: PresheafOfModules, PresheafOfModules.toPresheaf, toPresheaf, toPresheafOfModules
-/
noncomputable def toPresheaf : X.Modules ⥤ TopCat.Presheaf Ab X :=
  toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheaf X).Faithful
  body: .comp _ (PresheafOfModules.toPresheaf _)

中文:
实例 :
  签名: (toPresheaf X).忠实
  定义体: .comp _ (PresheafOfModules.toPresheaf _)

Depends on / 依赖: Finset, Finset.card_compl, PresheafOfModules, PresheafOfModules.toPresheaf, boundary_eq_iSup, card_compl, hasDimensionLT_face, hasDimensionLT_iSup_iff, stdSimplex, stdSimplex.hasDimensionLT_face, toPresheaf
-/
instance : (toPresheaf X).Faithful := .comp _ (PresheafOfModules.toPresheaf _)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimits (toPresheaf X)
  body: comp_preservesLimits _ (PresheafOfModules.toPresheaf _)

中文:
实例 :
  签名: PreservesLimits (toPresheaf X)
  定义体: comp_preservesLimits _ (PresheafOfModules.toPresheaf _)

Depends on / 依赖: PresheafOfModules, PresheafOfModules.toPresheaf, comp_preservesLimits, toPresheaf
-/
instance : PreservesLimits (toPresheaf X) := comp_preservesLimits _ (PresheafOfModules.toPresheaf _)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheaf X).ReflectsIsomorphisms
  body: reflectsIsomorphisms_comp _ (PresheafOfModules.toPresheaf _)

中文:
实例 :
  签名: (toPresheaf X).反映同构
  定义体: reflectsIsomorphisms_comp _ (PresheafOfModules.toPresheaf _)

Depends on / 依赖: PresheafOfModules, PresheafOfModules.toPresheaf, reflectsIsomorphisms_comp, toPresheaf
-/
instance : (toPresheaf X).ReflectsIsomorphisms :=
  reflectsIsomorphisms_comp _ (PresheafOfModules.toPresheaf _)

end Functor

variable {M N K : X.Modules} {φ : M ⟶ N} {U V : X.Opens}

section Presheaf

/--
Definition of `presheaf` / `presheaf` 的定义

English:
definition presheaf
  signature: (M : X.Modules)
  body: M.1.presheaf

中文:
定义 presheaf
  签名: (M : X.Modules)
  定义体: M.1.presheaf

Depends on / 依赖: presheaf
-/
noncomputable def presheaf (M : X.Modules) : TopCat.Presheaf Ab X := M.1.presheaf

/-- Notation for sections of a presheaf of module. -/
scoped[AlgebraicGeometry] notation3 "Γ(" M ", " U ")" => (Scheme.Modules.presheaf M).obj (.op U)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Γ(X, U) Γ(M, U)
  body: (M.val.obj (.op U)).isModule

中文:
实例 :
  签名: 模 Γ(X, U) Γ(M, U)
  定义体: (M.val.obj (.op U)).isModule

Depends on / 依赖: M.val.obj, isModule
-/
instance : Module Γ(X, U) Γ(M, U) := (M.val.obj (.op U)).isModule

variable (M) in
/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  given: (i : U ⟶ V) (r : Γ(X, V)) (x : Γ(M, V))
  proof: M.val.map_smul _ _ _

中文:
引理 map_smul
  条件: (i : U ⟶ V) (r : Γ(X, V)) (x : Γ(M, V))
  证明: M.val.map_smul _ _ _
-/
@[simp] lemma map_smul (i : U ⟶ V) (r : Γ(X, V)) (x : Γ(M, V)) :
    M.presheaf.map i.op (r • x) = X.presheaf.map i.op r • M.presheaf.map i.op x :=
  M.val.map_smul _ _ _

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: : Γ(X, U) ->+* End Γ(M, U)
  body: (M.val.obj (.op U)).smul

@[simp]

中文:
定义 smul
  签名: : Γ(X, U) ->+* End Γ(M, U)
  定义体: (M.val.obj (.op U)).smul

@[simp]

Depends on / 依赖: M.val.obj
-/
def smul : Γ(X, U) ->+* End Γ(M, U) :=
  (M.val.obj (.op U)).smul

@[simp]
/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (r : Γ(X, U)) (x : Γ(M, U))
  statement: (M.smul r).hom x = r • x
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 smul_apply
  条件: (r : Γ(X, U)) (x : Γ(M, U))
  结论: (M.smul r).hom x = r • x
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma smul_apply (r : Γ(X, U)) (x : Γ(M, U)) : (M.smul r).hom x = r • x := rfl

@[reassoc (attr := simp)]
/--
lemma `map_comp_smul` / 引理 `map_comp_smul`

English:
lemma map_comp_smul
  given: (i : U ⟶ V) (r : Γ(X, V))
  proof: by
  ext
  simp

中文:
引理 map_comp_smul
  条件: (i : U ⟶ V) (r : Γ(X, V))
  证明: by
  ext
  simp
-/
lemma map_comp_smul (i : U ⟶ V) (r : Γ(X, V)) :
    M.smul r ≫ M.presheaf.map i.op = M.presheaf.map i.op ≫ M.smul (X.presheaf.map i.op r) := by
  ext
  simp

/--
Definition of `Hom.mapPresheaf` / `Hom.mapPresheaf` 的定义

English:
definition Hom.mapPresheaf
  signature: (φ : M ⟶ N)
  body: (toPresheaf X).map φ

中文:
定义 态射.mapPresheaf
  签名: (φ : M ⟶ N)
  定义体: (toPresheaf X).map φ

Depends on / 依赖: toPresheaf
-/
noncomputable def Hom.mapPresheaf (φ : M ⟶ N) : M.presheaf ⟶ N.presheaf :=
  (toPresheaf X).map φ

/--
Definition of `Hom.app` / `Hom.app` 的定义

English:
definition Hom.app
  signature: (φ : M ⟶ N) (U : X.Opens)
  body: (forget₂ _ _).map (φ.val.app (.op U))

中文:
定义 态射.app
  签名: (φ : M ⟶ N) (U : X.Opens)
  定义体: (forget₂ _ _).map (φ.val.app (.op U))

Depends on / 依赖: val.app
-/
def Hom.app (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) ⟶ Γ(N, U) :=
  (forget₂ _ _).map (φ.val.app (.op U))

/--
lemma `mapPresheaf_app` / 引理 `mapPresheaf_app`

English:
lemma mapPresheaf_app
  given: (φ : M ⟶ N) (U)
  statement: φ.mapPresheaf.app U = φ.app U.unop
  proof: rfl

@[simp]

中文:
引理 mapPresheaf_app
  条件: (φ : M ⟶ N) (U)
  结论: φ.mapPresheaf.app U = φ.app U.unop
  证明: rfl

@[simp]
-/
@[simp] lemma mapPresheaf_app (φ : M ⟶ N) (U) : φ.mapPresheaf.app U = φ.app U.unop := rfl

@[simp]
/--
lemma `Hom.app_smul` / 引理 `Hom.app_smul`

English:
lemma Hom.app_smul
  given: (φ : M ⟶ N) (r : Γ(X, U)) (x : Γ(M, U))
  proof: (φ.val.app (.op U)).hom.map_smul r x

中文:
引理 态射.app_smul
  条件: (φ : M ⟶ N) (r : Γ(X, U)) (x : Γ(M, U))
  证明: (φ.val.app (.op U)).hom.map_smul r x

Depends on / 依赖: hom.map_smul, infer_instance, map_smul, val.app
-/
lemma Hom.app_smul (φ : M ⟶ N) (r : Γ(X, U)) (x : Γ(M, U)) :
    φ.app U (r • x) = r • φ.app U x :=
  (φ.val.app (.op U)).hom.map_smul r x

/--
lemma `Hom.add_app` / 引理 `Hom.add_app`

English:
lemma Hom.add_app
  given: (φ ψ : M ⟶ N)
  statement: (φ + ψ).app U = φ.app U + ψ.app U
  proof: rfl

中文:
引理 态射.add_app
  条件: (φ ψ : M ⟶ N)
  结论: (φ + ψ).app U = φ.app U + ψ.app U
  证明: rfl
-/
@[simp] lemma Hom.add_app (φ ψ : M ⟶ N) : (φ + ψ).app U = φ.app U + ψ.app U := rfl
/--
lemma `Hom.sub_app` / 引理 `Hom.sub_app`

English:
lemma Hom.sub_app
  given: (φ ψ : M ⟶ N)
  statement: (φ - ψ).app U = φ.app U - ψ.app U
  proof: rfl

中文:
引理 态射.sub_app
  条件: (φ ψ : M ⟶ N)
  结论: (φ - ψ).app U = φ.app U - ψ.app U
  证明: rfl
-/
@[simp] lemma Hom.sub_app (φ ψ : M ⟶ N) : (φ - ψ).app U = φ.app U - ψ.app U := rfl
/--
lemma `Hom.zero_app` / 引理 `Hom.zero_app`

English:
lemma Hom.zero_app
  statement: (0 : M ⟶ N).app U = 0
  proof: rfl

中文:
引理 态射.zero_app
  结论: (0 : M ⟶ N).app U = 0
  证明: rfl
-/
@[simp] lemma Hom.zero_app : (0 : M ⟶ N).app U = 0 := rfl
/--
lemma `Hom.id_app` / 引理 `Hom.id_app`

English:
lemma Hom.id_app
  given: (M : X.Modules)
  statement: (𝟙 M :).app U = 𝟙 _
  proof: rfl

中文:
引理 态射.id_app
  条件: (M : X.Modules)
  结论: (𝟙 M :).app U = 𝟙 _
  证明: rfl
-/
@[simp] lemma Hom.id_app (M : X.Modules) : (𝟙 M :).app U = 𝟙 _ := rfl
/--
lemma `Hom.comp_app` / 引理 `Hom.comp_app`

English:
lemma Hom.comp_app
  given: (φ : M ⟶ N) (ψ : N ⟶ K)
  statement: (φ ≫ ψ).app U = φ.app U ≫ ψ.app U
  proof: rfl

@[ext]

中文:
引理 态射.comp_app
  条件: (φ : M ⟶ N) (ψ : N ⟶ K)
  结论: (φ ≫ ψ).app U = φ.app U ≫ ψ.app U
  证明: rfl

@[ext]

Depends on / 依赖: faceSingletonComplIso, infer_instance, mono_comp_iff_of_isIso, stdSimplex, stdSimplex.faceSingletonComplIso
-/
@[simp] lemma Hom.comp_app (φ : M ⟶ N) (ψ : N ⟶ K) : (φ ≫ ψ).app U = φ.app U ≫ ψ.app U := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: (f g : M ⟶ N) (H : forall U, f.app U = g.app U)
  statement: f = g
  proof: by
  apply SheafOfModules.hom_ext
  ext U x
  exact congr($(H U.unop) x)

中文:
引理 hom_ext
  条件: (f g : M ⟶ N) (H : 对任意 U, f.app U = g.app U)
  结论: f = g
  证明: by
  apply SheafOfModules.hom_ext
  ext U x
  exact congr($(H U.unop) x)

Depends on / 依赖: SheafOfModules, SheafOfModules.hom_ext, U.unop, hom_ext, infer_instance
-/
lemma hom_ext (f g : M ⟶ N) (H : forall U, f.app U = g.app U) : f = g := by
  apply SheafOfModules.hom_ext
  ext U x
  exact congr($(H U.unop) x)

/--
lemma `isSheaf` / 引理 `isSheaf`

English:
lemma isSheaf
  given: (M : X.Modules)
  statement: M.presheaf.IsSheaf
  proof: SheafOfModules.isSheaf M

中文:
引理 isSheaf
  条件: (M : X.Modules)
  结论: M.presheaf.是层
  证明: SheafOfModules.isSheaf M

Depends on / 依赖: SheafOfModules, SheafOfModules.isSheaf, isSheaf
-/
lemma isSheaf (M : X.Modules) : M.presheaf.IsSheaf := SheafOfModules.isSheaf M

/--
lemma `toPresheaf_obj` / 引理 `toPresheaf_obj`

English:
lemma toPresheaf_obj
  statement: (toPresheaf X).obj M = M.presheaf
  proof: rfl

中文:
引理 toPresheaf_obj
  结论: (toPresheaf X).obj M = M.presheaf
  证明: rfl
-/
@[simp] lemma toPresheaf_obj : (toPresheaf X).obj M = M.presheaf := rfl
/--
lemma `toPresheaf_map` / 引理 `toPresheaf_map`

English:
lemma toPresheaf_map
  statement: (toPresheaf X).map φ = φ.mapPresheaf
  proof: rfl

中文:
引理 toPresheaf_map
  结论: (toPresheaf X).map φ = φ.mapPresheaf
  证明: rfl
-/
@[simp] lemma toPresheaf_map : (toPresheaf X).map φ = φ.mapPresheaf := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.isIso_iff_isIso_app` / 引理 `Hom.isIso_iff_isIso_app`

English:
lemma Hom.isIso_iff_isIso_app
  given: {M N : X.Modules} {φ : M ⟶ N}
  proof: by
  rw [← isIso_iff_of_reflects_iso _ (toPresheaf X)]; rw [NatTrans.isIso_iff_isIso_app]
  simp [Opposite.op_surjective.forall]

中文:
引理 态射.isIso_iff_isIso_app
  条件: {M N : X.Modules} {φ : M ⟶ N}
  证明: by
  rw [← isIso_iff_of_reflects_iso _ (toPresheaf X)]; rw [NatTrans.isIso_iff_isIso_app]
  simp [Opposite.op_surjective.forall]

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, Opposite, Opposite.op_surjective.forall, isIso_iff_isIso_app, isIso_iff_of_reflects_iso, op_surjective, toPresheaf
-/
lemma Hom.isIso_iff_isIso_app {M N : X.Modules} {φ : M ⟶ N} :
    IsIso φ ↔ forall U, IsIso (φ.app U) := by
  rw [← isIso_iff_of_reflects_iso _ (toPresheaf X)]; rw [NatTrans.isIso_iff_isIso_app]
  simp [Opposite.op_surjective.forall]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: φ] : IsIso (φ.app U)
  body: Hom.isIso_iff_isIso_app.mp ‹_› _

@[simp, push ←]

中文:
实例 [是同构
  签名: φ] : 是同构 (φ.app U)
  定义体: Hom.isIso_iff_isIso_app.mp ‹_› _

@[simp, push ←]

Depends on / 依赖: Hom.isIso_iff_isIso_app.mp, isIso_iff_isIso_app
-/
instance [IsIso φ] : IsIso (φ.app U) := Hom.isIso_iff_isIso_app.mp ‹_› _

@[simp, push ←]
/--
lemma `inv_app` / 引理 `inv_app`

English:
lemma inv_app
  given: [IsIso φ]
  statement: (inv φ).app U = inv (φ.app U)
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← Hom.comp_app]

中文:
引理 inv_app
  条件: [是同构 φ]
  结论: (inv φ).app U = inv (φ.app U)
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← Hom.comp_app]

Depends on / 依赖: Hom.comp_app, IsIso.eq_inv_of_hom_inv_id, comp_app, eq_inv_of_hom_inv_id
-/
lemma inv_app [IsIso φ] : (inv φ).app U = inv (φ.app U) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← Hom.comp_app]

end Presheaf

noncomputable section Functorial

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: : X.Modules ⥤ Y.Modules
  body: SheafOfModules.pushforward f.toRingCatSheafHom

@[simp]

中文:
定义 pushforward
  签名: : X.Modules ⥤ Y.Modules
  定义体: SheafOfModules.pushforward f.toRingCatSheafHom

@[simp]

Depends on / 依赖: SheafOfModules, SheafOfModules.pushforward, f.toRingCatSheafHom, pushforward, toRingCatSheafHom
-/
def pushforward : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward f.toRingCatSheafHom

@[simp]
/--
lemma `pushforward_obj_obj` / 引理 `pushforward_obj_obj`

English:
lemma pushforward_obj_obj
  given: (M : X.Modules) (U : Y.Opens)
  proof: rfl

@[simp]

中文:
引理 pushforward_obj_obj
  条件: (M : X.Modules) (U : Y.Opens)
  证明: rfl

@[simp]
-/
lemma pushforward_obj_obj (M : X.Modules) (U : Y.Opens) :
    Γ((pushforward f).obj M, U) = Γ(M, f ⁻¹ᵁ U) := rfl

@[simp]
/--
lemma `pushforward_obj_presheaf_map` / 引理 `pushforward_obj_presheaf_map`

English:
lemma pushforward_obj_presheaf_map
  given: {U V : Y.Opens} (i : U ⟶ V)
  proof: rfl

@[simp]

中文:
引理 pushforward_obj_presheaf_map
  条件: {U V : Y.Opens} (i : U ⟶ V)
  证明: rfl

@[simp]
-/
lemma pushforward_obj_presheaf_map {U V : Y.Opens} (i : U ⟶ V) :
    ((pushforward f).obj M).presheaf.map i.op = M.presheaf.map ((Opens.map f.base).map i).op := rfl

@[simp]
/--
lemma `pushforward_map_app` / 引理 `pushforward_map_app`

English:
lemma pushforward_map_app
  given: (φ : M ⟶ N) (U : Y.Opens)
  proof: rfl

中文:
引理 pushforward_map_app
  条件: (φ : M ⟶ N) (U : Y.Opens)
  证明: rfl
-/
lemma pushforward_map_app (φ : M ⟶ N) (U : Y.Opens) :
    ((pushforward f).map φ).app U = φ.app (f ⁻¹ᵁ U) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: : Y.Modules ⥤ X.Modules
  body: SheafOfModules.pullback f.toRingCatSheafHom

中文:
定义 pullback
  签名: : Y.Modules ⥤ X.Modules
  定义体: SheafOfModules.pullback f.toRingCatSheafHom

Depends on / 依赖: SheafOfModules, SheafOfModules.pullback, f.toRingCatSheafHom, pullback, toRingCatSheafHom
-/
def pullback : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pullbackPushforwardAdjunction` / `pullbackPushforwardAdjunction` 的定义

English:
definition pullbackPushforwardAdjunction
  signature: : pullback f ⊣ pushforward f
  body: SheafOfModules.pullbackPushforwardAdjunction _

中文:
定义 pullbackPushforwardAdjunction
  签名: : pullback f ⊣ pushforward f
  定义体: SheafOfModules.pullbackPushforwardAdjunction _

Depends on / 依赖: SheafOfModules, SheafOfModules.pullbackPushforwardAdjunction, pullbackPushforwardAdjunction
-/
def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pullback f).IsLeftAdjoint
  body: (pullbackPushforwardAdjunction f).isLeftAdjoint

中文:
实例 :
  签名: (pullback f).是左伴随
  定义体: (pullbackPushforwardAdjunction f).isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, pullbackPushforwardAdjunction
-/
instance : (pullback f).IsLeftAdjoint := (pullbackPushforwardAdjunction f).isLeftAdjoint
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward f).IsRightAdjoint
  body: (pullbackPushforwardAdjunction f).isRightAdjoint

中文:
实例 :
  签名: (pushforward f).是右伴随
  定义体: (pullbackPushforwardAdjunction f).isRightAdjoint

Depends on / 依赖: isRightAdjoint, pullbackPushforwardAdjunction
-/
instance : (pushforward f).IsRightAdjoint := (pullbackPushforwardAdjunction f).isRightAdjoint
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward f).Additive
  body: Functor.additive_of_preservesBinaryBiproducts _

中文:
实例 :
  签名: (pushforward f).加性
  定义体: Functor.additive_of_preservesBinaryBiproducts _

Depends on / 依赖: Functor, Functor.additive_of_preservesBinaryBiproducts, additive_of_preservesBinaryBiproducts
-/
instance : (pushforward f).Additive := Functor.additive_of_preservesBinaryBiproducts _
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pullback f).Additive
  body: Functor.additive_of_preservesBinaryBiproducts _

中文:
实例 :
  签名: (pullback f).加性
  定义体: Functor.additive_of_preservesBinaryBiproducts _

Depends on / 依赖: Functor, Functor.additive_of_preservesBinaryBiproducts, additive_of_preservesBinaryBiproducts
-/
instance : (pullback f).Additive := Functor.additive_of_preservesBinaryBiproducts _

end

variable (X) in
/--
Definition of `pushforwardId` / `pushforwardId` 的定义

English:
definition pushforwardId
  signature: : pushforward (𝟙 X) ≅ 𝟭 _
  body: SheafOfModules.pushforwardId _

中文:
定义 pushforwardId
  签名: : pushforward (𝟙 X) ≅ 𝟭 _
  定义体: SheafOfModules.pushforwardId _

Depends on / 依赖: SheafOfModules, SheafOfModules.pushforwardId, pushforwardId
-/
def pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

/--
lemma `pushforwardId_hom_app_app` / 引理 `pushforwardId_hom_app_app`

English:
lemma pushforwardId_hom_app_app
  statement: ((pushforwardId X).hom.app M).app U = 𝟙 _
  proof: rfl

中文:
引理 pushforwardId_hom_app_app
  结论: ((pushforwardId X).hom.app M).app U = 𝟙 _
  证明: rfl
-/
@[simp] lemma pushforwardId_hom_app_app : ((pushforwardId X).hom.app M).app U = 𝟙 _ := rfl
/--
lemma `pushforwardId_inv_app_app` / 引理 `pushforwardId_inv_app_app`

English:
lemma pushforwardId_inv_app_app
  statement: ((pushforwardId X).inv.app M).app U = 𝟙 _
  proof: rfl

中文:
引理 pushforwardId_inv_app_app
  结论: ((pushforwardId X).inv.app M).app U = 𝟙 _
  证明: rfl
-/
@[simp] lemma pushforwardId_inv_app_app : ((pushforwardId X).inv.app M).app U = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: : pullback (𝟙 X) ≅ 𝟭 _
  body: SheafOfModules.pullbackId _

中文:
定义 pullbackId
  签名: : pullback (𝟙 X) ≅ 𝟭 _
  定义体: SheafOfModules.pullbackId _

Depends on / 依赖: SheafOfModules, SheafOfModules.pullbackId, fibration_iff, pullbackId, rlp_of_isIso
-/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/--
lemma `conjugateEquiv_pullbackId_hom` / 引理 `conjugateEquiv_pullbackId_hom`

English:
lemma conjugateEquiv_pullbackId_hom
  proof: SheafOfModules.conjugateEquiv_pullbackId_hom _

中文:
引理 conjugateEquiv_pullbackId_hom
  证明: SheafOfModules.conjugateEquiv_pullbackId_hom _

Depends on / 依赖: SheafOfModules, SheafOfModules.conjugateEquiv_pullbackId_hom, conjugateEquiv_pullbackId_hom
-/
lemma conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom =
      (pushforwardId X).inv :=
  SheafOfModules.conjugateEquiv_pullbackId_hom _

/--
Definition of `pushforwardComp` / `pushforwardComp` 的定义

English:
definition pushforwardComp
  signature: :
  body: SheafOfModules.pushforwardComp _ _

中文:
定义 pushforwardComp
  签名: :
  定义体: SheafOfModules.pushforwardComp _ _

Depends on / 依赖: SheafOfModules, SheafOfModules.pushforwardComp, pushforwardComp
-/
def pushforwardComp :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp _ _

/--
lemma `pushforwardComp_hom_app_app` / 引理 `pushforwardComp_hom_app_app`

English:
lemma pushforwardComp_hom_app_app
  given: (U)
  statement: ((pushforwardComp f g).hom.app M).app U = 𝟙 _
  proof: rfl

中文:
引理 pushforwardComp_hom_app_app
  条件: (U)
  结论: ((pushforwardComp f g).hom.app M).app U = 𝟙 _
  证明: rfl
-/
@[simp] lemma pushforwardComp_hom_app_app (U) : ((pushforwardComp f g).hom.app M).app U = 𝟙 _ := rfl
/--
lemma `pushforwardComp_inv_app_app` / 引理 `pushforwardComp_inv_app_app`

English:
lemma pushforwardComp_inv_app_app
  given: (U)
  statement: ((pushforwardComp f g).inv.app M).app U = 𝟙 _
  proof: rfl

中文:
引理 pushforwardComp_inv_app_app
  条件: (U)
  结论: ((pushforwardComp f g).inv.app M).app U = 𝟙 _
  证明: rfl
-/
@[simp] lemma pushforwardComp_inv_app_app (U) : ((pushforwardComp f g).inv.app M).app U = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: :
  body: SheafOfModules.pullbackComp _ _

中文:
定义 pullbackComp
  签名: :
  定义体: SheafOfModules.pullbackComp _ _

Depends on / 依赖: SheafOfModules, SheafOfModules.pullbackComp, pullbackComp
-/
def pullbackComp :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pushforwardCongr` / `pushforwardCongr` 的定义

English:
definition pushforwardCongr
  signature: {f g : X ⟶ Y} (hf : f = g)
  body: pushforwardNatIso _ (Opens.mapIso _ _ (hf ▸ rfl)) ≪≫
      SheafOfModules.pushforwardCongr (by cat_disch)

中文:
定义 pushforwardCongr
  签名: {f g : X ⟶ Y} (hf : f = g)
  定义体: pushforwardNatIso _ (Opens.mapIso _ _ (hf ▸ rfl)) ≪≫
      SheafOfModules.pushforwardCongr (by cat_disch)

Depends on / 依赖: Opens.mapIso, SheafOfModules, SheafOfModules.pushforwardCongr, cat_disch, mapIso, pushforwardCongr, pushforwardNatIso
-/
def pushforwardCongr {f g : X ⟶ Y} (hf : f = g) : pushforward f ≅ pushforward g :=
    pushforwardNatIso _ (Opens.mapIso _ _ (hf ▸ rfl)) ≪≫
      SheafOfModules.pushforwardCongr (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pushforwardCongr_hom_app_app` / 引理 `pushforwardCongr_hom_app_app`

English:
lemma pushforwardCongr_hom_app_app
  given: {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens)
  proof: rfl

中文:
引理 pushforwardCongr_hom_app_app
  条件: {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens)
  证明: rfl
-/
@[simp] lemma pushforwardCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens) :
    ((pushforwardCongr hf).hom.app M).app U = M.presheaf.map (eqToHom (hf ▸ rfl)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pushforwardCongr_inv_app_app` / 引理 `pushforwardCongr_inv_app_app`

English:
lemma pushforwardCongr_inv_app_app
  given: {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens)
  proof: rfl

中文:
引理 pushforwardCongr_inv_app_app
  条件: {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens)
  证明: rfl
-/
@[simp] lemma pushforwardCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens) :
    ((pushforwardCongr hf).inv.app M).app U = M.presheaf.map (eqToHom (hf ▸ rfl)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `pullbackCongr` / `pullbackCongr` 的定义

English:
definition pullbackCongr
  signature: {f g : X ⟶ Y} (hf : f = g)
  body: eqToIso (hf ▸ rfl)

中文:
定义 pullbackCongr
  签名: {f g : X ⟶ Y} (hf : f = g)
  定义体: eqToIso (hf ▸ rfl)

Depends on / 依赖: eqToIso
-/
def pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g :=
  eqToIso (hf ▸ rfl)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `conjugateEquiv_pullbackComp_inv` / 引理 `conjugateEquiv_pullbackComp_inv`

English:
lemma conjugateEquiv_pullbackComp_inv
  proof: SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

中文:
引理 conjugateEquiv_pullbackComp_inv
  证明: SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

Depends on / 依赖: SheafOfModules, SheafOfModules.conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackComp_inv
-/
lemma conjugateEquiv_pullbackComp_inv :
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv =
    (pushforwardComp f g).hom :=
  SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pseudofunctor_associativity` / 引理 `pseudofunctor_associativity`

English:
lemma pseudofunctor_associativity
  proof: by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.

中文:
引理 pseudofunctor_associativity
  证明: by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Iso.hom, SheafOfModules, SheafOfModules.pullback_assoc, associator, congr_arg, f.toRingCatSheafHom, g.toRingCatSheafHom, h.toRingCatSheafHom, isoWhiskerLeft, isoWhiskerRight, pullback, pullbackComp, pullback_assoc, toRingCatSheafHom
-/
lemma pseudofunctor_associativity :
    (pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
    eqToHom (by simp) := by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_assoc.{u}
      h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)
  simp [this]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pseudofunctor_left_unitality` / 引理 `pseudofunctor_left_unitality`

English:
lemma pseudofunctor_left_unitality
  proof: by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)
  simp [←

中文:
引理 pseudofunctor_left_unitality
  证明: by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)
  simp [←

Depends on / 依赖: Functor, Functor.isoWhiskerRight, Iso.hom, SheafOfModules, SheafOfModules.pullback_id_comp, congr_arg, f.toRingCatSheafHom, isoWhiskerRight, leftUnitor, pullback, pullbackComp, pullbackId, pullback_id_comp, toRingCatSheafHom
-/
lemma pseudofunctor_left_unitality :
    (pullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)
  simp [← this]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pseudofunctor_right_unitality` / 引理 `pseudofunctor_right_unitality`

English:
lemma pseudofunctor_right_unitality
  proof: by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)
  simp [←

中文:
引理 pseudofunctor_right_unitality
  证明: by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)
  simp [←

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Iso.hom, SheafOfModules, SheafOfModules.pullback_comp_id, congr_arg, f.toRingCatSheafHom, isoWhiskerLeft, pullback, pullbackComp, pullbackId, pullback_comp_id, rightUnitor, toRingCatSheafHom
-/
lemma pseudofunctor_right_unitality :
    (pullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)
  simp [← this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] pseudofunctor_associativity pseudofunctor_left_unitality
  pseudofunctor_right_unitality Bicategory.toNatTrans_conjugateEquiv
  conjugateEquiv_pullbackId_hom Adjunction.ofCat_comp conjugateEquiv_pullbackComp_inv in
/-- The pseudofunctor from `Schemeᵒᵖ` to the bicategory of adjunctions which sends
a scheme `X` to the category `X.Modules` of sheaves of modules over `X`.
(This contains both the covariant and the contravariant functorialities of
these categories.) -/
@[simps! obj_obj map_l map_r map_adj
  mapId_hom_τl mapId_hom_τr mapId_inv_τl mapId_inv_τr
  mapComp_hom_τl mapComp_hom_τr mapComp_inv_τl mapComp_inv_τr]
/--
Definition of `pseudofunctor` / `pseudofunctor` 的定义

English:
definition pseudofunctor
  signature: :
  body: LocallyDiscrete.mkPseudofunctor
    (fun X => Adj.mk (Cat.of X.unop.Modules))
    (fun f => .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun _ => Adj.iso₂Mk (Cat.Hom.isoMk (pullbackId _))
        (Cat.Hom.isoMk (pushforwardId _).symm))
    (fun _ _ => Adj.iso₂Mk (Cat.Hom.isoMk (pullbackCom

中文:
定义 pseudofunctor
  签名: :
  定义体: LocallyDiscrete.mkPseudofunctor
    (fun X => Adj.mk (Cat.of X.unop.Modules))
    (fun f => .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun _ => Adj.iso₂Mk (Cat.Hom.isoMk (pullbackId _))
        (Cat.Hom.isoMk (pushforwardId _).symm))
    (fun _ _ => Adj.iso₂Mk (Cat.Hom.isoMk (pullbackCom

Depends on / 依赖: Adj.iso, Adj.mk, Cat.Hom.isoMk, Cat.of, LocallyDiscrete, LocallyDiscrete.mkPseudofunctor, Modules, X.unop.Modules, f.unop, mkPseudofunctor, pullbackComp, pullbackId, pullbackPushforwardAdjunction, pushforwardComp, pushforwardId
-/
def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat) :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Adj.mk (Cat.of X.unop.Modules))
    (fun f => .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun _ => Adj.iso₂Mk (Cat.Hom.isoMk (pullbackId _))
        (Cat.Hom.isoMk (pushforwardId _).symm))
    (fun _ _ => Adj.iso₂Mk (Cat.Hom.isoMk (pullbackComp _ _).symm)
        (Cat.Hom.isoMk (pushforwardComp _ _)))

end Functorial

noncomputable section Restriction

variable (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `restrictFunctor` / `restrictFunctor` 的定义

English:
definition restrictFunctor
  signature: : Y.Modules ⥤ X.Modules
  body: letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  SheafOfModules.pushforward (F := f.opensFunctor)
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

中文:
定义 restrictFunctor
  签名: : Y.Modules ⥤ X.Modules
  定义体: letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  SheafOfModules.pushforward (F := f.opensFunctor)
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

Depends on / 依赖: CommRingCat, Functor, Functor.whiskerRight, RingCat, SheafOfModules, SheafOfModules.pushforward, U.unop, X.presheaf, Y.presheaf, appIso, f.appIso, f.opensFunctor, f.opensFunctor.op, opensFunctor, presheaf, pushforward, whiskerRight
-/
def restrictFunctor : Y.Modules ⥤ X.Modules :=
  letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  SheafOfModules.pushforward (F := f.opensFunctor)
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/--
Definition of `restrict` / `restrict` 的定义

English:
abbreviation restrict
  signature: (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f]
  body: (restrictFunctor f).obj M

中文:
缩写 restrict
  签名: (M : Y.Modules) (f : X ⟶ Y) [是开浸入 f]
  定义体: (restrictFunctor f).obj M

Depends on / 依赖: restrictFunctor
-/
abbrev restrict (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] : X.Modules :=
  (restrictFunctor f).obj M

/--
Definition of `restrictAppIso` / `restrictAppIso` 的定义

English:
definition restrictAppIso
  signature: (M : Y.Modules) (U : X.Opens)
  body: Iso.refl _

@[elementwise (attr := simp), reassoc (attr := simp)]

中文:
定义 restrictAppIso
  签名: (M : Y.Modules) (U : X.Opens)
  定义体: Iso.refl _

@[elementwise (attr := simp), reassoc (attr := simp)]

Depends on / 依赖: Iso.refl
-/
def restrictAppIso (M : Y.Modules) (U : X.Opens) : Γ(M.restrict f, U) ≅ Γ(M, f ''ᵁ U) :=
  Iso.refl _

@[elementwise (attr := simp), reassoc (attr := simp)]
/--
lemma `smul_restrictAppIso_hom` / 引理 `smul_restrictAppIso_hom`

English:
lemma smul_restrictAppIso_hom
  given: (M : Y.Modules) (U : X.Opens) (r : Γ(X, U))
  proof: rfl

@[elementwise (attr := simp), reassoc (attr := simp)]

中文:
引理 smul_restrictAppIso_hom
  条件: (M : Y.Modules) (U : X.Opens) (r : Γ(X, U))
  证明: rfl

@[elementwise (attr := simp), reassoc (attr := simp)]
-/
lemma smul_restrictAppIso_hom (M : Y.Modules) (U : X.Opens) (r : Γ(X, U)) :
    dsimp% (M.restrict f).smul r ≫ (M.restrictAppIso f U).hom =
      (M.restrictAppIso f U).hom ≫ M.smul ((f.appIso U).inv r) :=
  rfl

@[elementwise (attr := simp), reassoc (attr := simp)]
/--
lemma `smul_restrictAppIso_inv` / 引理 `smul_restrictAppIso_inv`

English:
lemma smul_restrictAppIso_inv
  given: (M : Y.Modules) (U : X.Opens) (r : Γ(Y, f ''ᵁ U))
  proof: by
  simp [← cancel_mono (M.restrictAppIso f U).hom]

@[elementwise (attr := simp), reassoc (attr := simp)]

中文:
引理 smul_restrictAppIso_inv
  条件: (M : Y.Modules) (U : X.Opens) (r : Γ(Y, f ''ᵁ U))
  证明: by
  simp [← cancel_mono (M.restrictAppIso f U).hom]

@[elementwise (attr := simp), reassoc (attr := simp)]

Depends on / 依赖: M.restrictAppIso, cancel_mono, restrictAppIso
-/
lemma smul_restrictAppIso_inv (M : Y.Modules) (U : X.Opens) (r : Γ(Y, f ''ᵁ U)) :
    M.smul r ≫ (M.restrictAppIso f U).inv =
      (M.restrictAppIso f U).inv ≫ (M.restrict f).smul ((f.appIso U).hom r) := by
  simp [← cancel_mono (M.restrictAppIso f U).hom]

@[elementwise (attr := simp), reassoc (attr := simp)]
/--
lemma `map_restrictAppIso_hom` / 引理 `map_restrictAppIso_hom`

English:
lemma map_restrictAppIso_hom
  statement: (M : Y.Modules) {U V : X.Opens}
  proof: by
  rfl

@[elementwise (attr := simp), reassoc (attr := simp)]

中文:
引理 map_restrictAppIso_hom
  结论: (M : Y.Modules) {U V : X.Opens}
  证明: by
  rfl

@[elementwise (attr := simp), reassoc (attr := simp)]
-/
lemma map_restrictAppIso_hom (M : Y.Modules) {U V : X.Opens}
    (hUV : Opposite.op V ⟶ .op U) :
    (M.restrict f).presheaf.map hUV ≫ (M.restrictAppIso f U).hom =
      (M.restrictAppIso f V).hom ≫
      M.presheaf.map (.op <| homOfLE <| Scheme.Hom.image_mono _ (leOfHom hUV.unop)) := by
  rfl

@[elementwise (attr := simp), reassoc (attr := simp)]
/--
lemma `restrictAppIso_inv_map` / 引理 `restrictAppIso_inv_map`

English:
lemma restrictAppIso_inv_map
  given: (M : Y.Modules) {U V : X.Opens} (hUV : .op V ⟶ .op U)
  proof: rfl

中文:
引理 restrictAppIso_inv_map
  条件: (M : Y.Modules) {U V : X.Opens} (hUV : .op V ⟶ .op U)
  证明: rfl
-/
lemma restrictAppIso_inv_map (M : Y.Modules) {U V : X.Opens} (hUV : .op V ⟶ .op U) :
    (M.restrictAppIso f V).inv ≫ (M.restrict f).presheaf.map hUV =
      M.presheaf.map (.op <| homOfLE <| Scheme.Hom.image_mono _ (leOfHom hUV.unop)) ≫
      (M.restrictAppIso f U).inv :=
  rfl

/--
lemma `restrict_obj` / 引理 `restrict_obj`

English:
lemma restrict_obj
  given: (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] (U)
  proof: rfl

中文:
引理 restrict_obj
  条件: (M : Y.Modules) (f : X ⟶ Y) [是开浸入 f] (U)
  证明: rfl
-/
lemma restrict_obj (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] (U) :
    Γ(M.restrict f, U) = Γ(M, f ''ᵁ U) := rfl

/--
lemma `restrict_map` / 引理 `restrict_map`

English:
lemma restrict_map
  given: (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] {U V} (i : U ⟶ V)
  proof: rfl

中文:
引理 restrict_map
  条件: (M : Y.Modules) (f : X ⟶ Y) [是开浸入 f] {U V} (i : U ⟶ V)
  证明: rfl
-/
lemma restrict_map (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] {U V} (i : U ⟶ V) :
    (M.restrict f).presheaf.map i.op = M.presheaf.map (f.opensFunctor.map i).op := rfl

/--
Definition of `restrictUnitIso` / `restrictUnitIso` 的定义

English:
definition restrictUnitIso
  signature: (f : X ⟶ Y) [IsOpenImmersion f]
  body: by
refine (fullyFaithfulForget _).preimageIso PresheafOfModules.isoMk (fun U => ?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ Ab).mapIso (f.appIso U.unop)) ?_
    intro (r : Γ(X, U.unop))
    ext (x : Γ(Y, f ''ᵁ U.unop))
    change r * (f.appIso U.unop).hom x = (f

中文:
定义 restrictUnitIso
  签名: (f : X ⟶ Y) [是开浸入 f]
  定义体: by
refine (fullyFaithfulForget _).preimageIso PresheafOfModules.isoMk (fun U => ?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ Ab).mapIso (f.appIso U.unop)) ?_
    intro (r : Γ(X, U.unop))
    ext (x : Γ(Y, f ''ᵁ U.unop))
    change r * (f.appIso U.unop).hom x = (f

Depends on / 依赖: CommRingCat, Hom.appIso_hom, ModuleCat, ModuleCat.isoMk, PresheafOfModules, PresheafOfModules.isoMk, RingCat, U.unop, X.presheaf.map, Y.presheaf.map, appIso, appIso_hom, f.appIso, fullyFaithfulForget, g.unop, homOfLE, leOfHom, mapIso, preimageIso, presheaf
-/
def restrictUnitIso (f : X ⟶ Y) [IsOpenImmersion f] :
    restrict (.unit <| Y.ringCatSheaf) f ≅ .unit X.ringCatSheaf := by
refine (fullyFaithfulForget _).preimageIso PresheafOfModules.isoMk (fun U => ?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ Ab).mapIso (f.appIso U.unop)) ?_
    intro (r : Γ(X, U.unop))
    ext (x : Γ(Y, f ''ᵁ U.unop))
    change r * (f.appIso U.unop).hom x = (f.appIso U.unop).hom ((f.appIso U.unop).inv r * x)
    simp
  · intro U V g
    have : Y.presheaf.map (homOfLE (by grw [leOfHom g.unop])).op ≫
        (f.appIso _).hom = (f.appIso U.unop).hom ≫ X.presheaf.map g := by
      simp [Hom.appIso_hom']
    ext x
    exact congr($(this) x)

/--
Definition of `restrictFunctorAdjCounitIso` / `restrictFunctorAdjCounitIso` 的定义

English:
definition restrictFunctorAdjCounitIso
  signature: : pushforward f ⋙ restrictFunctor f ≅ 𝟭 _
  body: letI := CategoryTheory.Functor.isContinuous_comp.{u} f.opensFunctor (Opens.map f.base)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  (SheafOfModules.pushforwardComp _ _) ≪≫ pushforwardNatIso _ (NatIso.ofComponents
      (fun U => eqToIso (f.preima

中文:
定义 restrictFunctorAdjCounitIso
  签名: : pushforward f ⋙ restrictFunctor f ≅ 𝟭 _
  定义体: letI := CategoryTheory.Functor.isContinuous_comp.{u} f.opensFunctor (Opens.map f.base)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  (SheafOfModules.pushforwardComp _ _) ≪≫ pushforwardNatIso _ (NatIso.ofComponents
      (fun U => eqToIso (f.preima

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.isContinuous_comp, Functor, NatIso, NatIso.ofComponents, Opens.grothendieckTopology, Opens.map, SheafOfModules, SheafOfModules.pushforwardComp, SheafOfModules.pushforwardCongr, SheafOfModules.pushforwardId, U.unop, appIso_inv_app_presheafMap, eqToIso, f.appIso_inv_app_presheafMap, f.base, f.opensFunctor, f.preimage_image_eq, grothendieckTopology, isContinuous_comp
-/
def restrictFunctorAdjCounitIso : pushforward f ⋙ restrictFunctor f ≅ 𝟭 _ :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} f.opensFunctor (Opens.map f.base)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  (SheafOfModules.pushforwardComp _ _) ≪≫ pushforwardNatIso _ (NatIso.ofComponents
      (fun U => eqToIso (f.preimage_image_eq U).symm) fun _ => rfl) ≪≫
    SheafOfModules.pushforwardCongr (by ext U x; exact
      congr($(f.appIso_inv_app_presheafMap U.unop) x)) ≪≫ SheafOfModules.pushforwardId _

/--
Definition of `restrictAdjunction` / `restrictAdjunction` 的定义

English:
definition restrictAdjunction
  signature: : restrictFunctor f ⊣ pushforward f
  body: by
  refine pushforwardPushforwardAdj (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x; exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have : (f.appIso U.unop).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
    

中文:
定义 restrictAdjunction
  签名: : restrictFunctor f ⊣ pushforward f
  定义体: by
  refine pushforwardPushforwardAdj (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x; exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have : (f.appIso U.unop).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
    

Depends on / 依赖: Functor, Functor.map_comp, Scheme, Scheme.Hom.appIso_inv_app_assoc, U.unop, X.presheaf.map, X.presheaf.map_id, adjunction, appIso, appIso_inv_app_assoc, app_appIso_inv, eqToHom, f.app, f.appIso, f.app_appIso_inv, f.isOpenEmbedding.isOpenMap.adjunction, f.preimage_image_eq, isOpenEmbedding, isOpenMap, map_comp
-/
def restrictAdjunction : restrictFunctor f ⊣ pushforward f := by
  refine pushforwardPushforwardAdj (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x; exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have : (f.appIso U.unop).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc]; rw [← Functor.map_comp]; rw [← X.presheaf.map_id]; rfl
    exact congr($this x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (restrictAdjunction f).counit
  body: inferInstanceAs (IsIso <| (restrictFunctorAdjCounitIso f).hom)

中文:
实例 :
  签名: 是同构 (restrictAdjunction f).counit
  定义体: inferInstanceAs (IsIso <| (restrictFunctorAdjCounitIso f).hom)

Depends on / 依赖: restrictFunctorAdjCounitIso
-/
instance : IsIso (restrictAdjunction f).counit :=
  inferInstanceAs (IsIso <| (restrictFunctorAdjCounitIso f).hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (restrictFunctor f).IsLeftAdjoint
  body: (restrictAdjunction f).isLeftAdjoint

中文:
实例 :
  签名: (restrictFunctor f).是左伴随
  定义体: (restrictAdjunction f).isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, restrictAdjunction
-/
instance : (restrictFunctor f).IsLeftAdjoint := (restrictAdjunction f).isLeftAdjoint
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward f).Full
  body: (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.full

中文:
实例 :
  签名: (pushforward f).满
  定义体: (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.full

Depends on / 依赖: fullyFaithfulROfIsIsoCounit, fullyFaithfulROfIsIsoCounit.full, restrictAdjunction
-/
instance : (pushforward f).Full := (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward f).Faithful
  body: (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.faithful

@[simp]

中文:
实例 :
  签名: (pushforward f).忠实
  定义体: (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.faithful

@[simp]

Depends on / 依赖: faithful, fullyFaithfulROfIsIsoCounit, fullyFaithfulROfIsIsoCounit.faithful, restrictAdjunction
-/
instance : (pushforward f).Faithful := (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.faithful

@[simp]
/--
lemma `restrictAdjunction_unit_app_app` / 引理 `restrictAdjunction_unit_app_app`

English:
lemma restrictAdjunction_unit_app_app
  given: (M : Y.Modules) (U : Y.Opens)
  proof: rfl

@[simp]

中文:
引理 restrictAdjunction_unit_app_app
  条件: (M : Y.Modules) (U : Y.Opens)
  证明: rfl

@[simp]
-/
lemma restrictAdjunction_unit_app_app (M : Y.Modules) (U : Y.Opens) :
    ((restrictAdjunction f).unit.app M).app U =
      M.presheaf.map (homOfLE (f.image_preimage_le U)).op := rfl

@[simp]
/--
lemma `restrictAdjunction_counit_app_app` / 引理 `restrictAdjunction_counit_app_app`

English:
lemma restrictAdjunction_counit_app_app
  given: (M : X.Modules) (U : X.Opens)
  proof: rfl

中文:
引理 restrictAdjunction_counit_app_app
  条件: (M : X.Modules) (U : X.Opens)
  证明: rfl
-/
lemma restrictAdjunction_counit_app_app (M : X.Modules) (U : X.Opens) :
    ((restrictAdjunction f).counit.app M).app U =
      M.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `restrictFunctorIsoPullback` / `restrictFunctorIsoPullback` 的定义

English:
definition restrictFunctorIsoPullback
  signature: : restrictFunctor f ≅ pullback f
  body: (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

中文:
定义 restrictFunctorIsoPullback
  签名: : restrictFunctor f ≅ pullback f
  定义体: (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

Depends on / 依赖: leftAdjointUniq, pullbackPushforwardAdjunction, restrictAdjunction
-/
def restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `restrictFunctorId` / `restrictFunctorId` 的定义

English:
definition restrictFunctorId
  signature: : restrictFunctor (𝟙 X) ≅ 𝟭 _
  body: SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents (fun _ => eqToIso (by simp))) ≪≫
    SheafOfModules.pushforwardCongr
      (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    SheafOfModules.pushforwardId _

@[simp]

中文:
定义 restrictFunctorId
  签名: : restrictFunctor (𝟙 X) ≅ 𝟭 _
  定义体: SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents (fun _ => eqToIso (by simp))) ≪≫
    SheafOfModules.pushforwardCongr
      (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    SheafOfModules.pushforwardId _

@[simp]

Depends on / 依赖: Functor, Functor.map_comp, NatIso, NatIso.ofComponents, SheafOfModules, SheafOfModules.pushforwardCongr, SheafOfModules.pushforwardId, SheafOfModules.pushforwardNatIso, SheafedSpace, SheafedSpace.sheaf, eqToIso, map_comp, ofComponents, pushforwardCongr, pushforwardId, pushforwardNatIso
-/
def restrictFunctorId : restrictFunctor (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents (fun _ => eqToIso (by simp))) ≪≫
    SheafOfModules.pushforwardCongr
      (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    SheafOfModules.pushforwardId _

@[simp]
/--
lemma `restrictFunctorId_hom_app_app` / 引理 `restrictFunctorId_hom_app_app`

English:
lemma restrictFunctorId_hom_app_app
  proof: rfl

@[simp]

中文:
引理 restrictFunctorId_hom_app_app
  证明: rfl

@[simp]
-/
lemma restrictFunctorId_hom_app_app :
    (restrictFunctorId.hom.app M).app U =
      M.presheaf.map (eqToHom (show U = 𝟙 X ''ᵁ U by simp)).op := rfl

@[simp]
/--
lemma `restrictFunctorId_inv_app_app` / 引理 `restrictFunctorId_inv_app_app`

English:
lemma restrictFunctorId_inv_app_app
  proof: rfl

中文:
引理 restrictFunctorId_inv_app_app
  证明: rfl
-/
lemma restrictFunctorId_inv_app_app :
    (restrictFunctorId.inv.app M).app U =
      M.presheaf.map (eqToHom (show 𝟙 X ''ᵁ U = U by simp)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `restrictFunctorComp` / `restrictFunctorComp` 的定义

English:
definition restrictFunctorComp
  signature: : restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restrictFunctor f
  body: SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ => eqToIso (by simp)) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

@[simp]

中文:
定义 restrictFunctorComp
  签名: : restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restrictFunctor f
  定义体: SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ => eqToIso (by simp)) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

@[simp]

Depends on / 依赖: Functor, Functor.map_comp, NatIso, NatIso.ofComponents, SheafOfModules, SheafOfModules.pushforwardComp, SheafOfModules.pushforwardCongr, SheafOfModules.pushforwardNatIso, SheafedSpace, SheafedSpace.sheaf, eqToIso, map_comp, ofComponents, pushforwardComp, pushforwardCongr, pushforwardNatIso
-/
def restrictFunctorComp : restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restrictFunctor f :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ => eqToIso (by simp)) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

@[simp]
/--
lemma `restrictFunctorComp_hom_app_app` / 引理 `restrictFunctorComp_hom_app_app`

English:
lemma restrictFunctorComp_hom_app_app
  given: (M : Z.Modules)
  proof: rfl

@[simp]

中文:
引理 restrictFunctorComp_hom_app_app
  条件: (M : Z.Modules)
  证明: rfl

@[simp]
-/
lemma restrictFunctorComp_hom_app_app (M : Z.Modules) :
    ((restrictFunctorComp f g).hom.app M).app U = M.presheaf.map (eqToHom (by simp)).op := rfl

@[simp]
/--
lemma `restrictFunctorComp_inv_app_app` / 引理 `restrictFunctorComp_inv_app_app`

English:
lemma restrictFunctorComp_inv_app_app
  given: (M : Z.Modules)
  proof: rfl

中文:
引理 restrictFunctorComp_inv_app_app
  条件: (M : Z.Modules)
  证明: rfl
-/
lemma restrictFunctorComp_inv_app_app (M : Z.Modules) :
    ((restrictFunctorComp f g).inv.app M).app U = M.presheaf.map (eqToHom (by simp)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `restrictFunctorCongr` / `restrictFunctorCongr` 的定义

English:
definition restrictFunctorCongr
  signature: {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f] [IsOpenImmersion g]
  body: SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ => eqToIso (by simp [hf])) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; subst hf; simp)

@[simp]

中文:
定义 restrictFunctorCongr
  签名: {f g : X ⟶ Y} (hf : f = g) [是开浸入 f] [是开浸入 g]
  定义体: SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ => eqToIso (by simp [hf])) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; subst hf; simp)

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, SheafOfModules, SheafOfModules.pushforwardCongr, SheafOfModules.pushforwardNatIso, eqToIso, ofComponents, pushforwardCongr, pushforwardNatIso
-/
def restrictFunctorCongr {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctor f ≅ restrictFunctor g :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ => eqToIso (by simp [hf])) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; subst hf; simp)

@[simp]
/--
lemma `restrictFunctorCongr_hom_app_app` / 引理 `restrictFunctorCongr_hom_app_app`

English:
lemma restrictFunctorCongr_hom_app_app
  statement: {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
  proof: rfl

@[simp]

中文:
引理 restrictFunctorCongr_hom_app_app
  结论: {f g : X ⟶ Y} (hf : f = g) [是开浸入 f]
  证明: rfl

@[simp]
-/
lemma restrictFunctorCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    ((restrictFunctorCongr hf).hom.app M).app U = M.presheaf.map (eqToHom (by simp [hf])).op := rfl

@[simp]
/--
lemma `restrictFunctorCongr_inv_app_app` / 引理 `restrictFunctorCongr_inv_app_app`

English:
lemma restrictFunctorCongr_inv_app_app
  statement: {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
  proof: rfl

中文:
引理 restrictFunctorCongr_inv_app_app
  结论: {f g : X ⟶ Y} (hf : f = g) [是开浸入 f]
  证明: rfl
-/
lemma restrictFunctorCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    ((restrictFunctorCongr hf).inv.app M).app U = M.presheaf.map (eqToHom (by simp [hf])).op := rfl

/--
Definition of `restrictStalkNatIso` / `restrictStalkNatIso` 的定义

English:
definition restrictStalkNatIso
  signature: (x : X)
  body: haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  (toPresheaf _ ⋙ (Functor.whiskeringLeft (OpenNhds (f x))ᵒᵖ Y.Opensᵒᵖ Ab).obj
      (OpenNhds.inclusion (f x)).op).isoWhiskerLeft
      (Functor.Final.colimIso (f.isOpenEmbedding.functorNhds x).op)

@[simp]

中文:
定义 restrictStalk自然数Iso
  签名: (x : X)
  定义体: haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  (toPresheaf _ ⋙ (Functor.whiskeringLeft (OpenNhds (f x))ᵒᵖ Y.Opensᵒᵖ Ab).obj
      (OpenNhds.inclusion (f x)).op).isoWhiskerLeft
      (Functor.Final.colimIso (f.isOpenEmbedding.functorNhds x).op)

@[simp]

Depends on / 依赖: Functor, Functor.Final.colimIso, Functor.initial_of_adjunction, Functor.whiskeringLeft, OpenNhds, OpenNhds.inclusion, Y.Opens, adjunctionNhds, colimIso, f.isOpenEmbedding.adjunctionNhds, f.isOpenEmbedding.functorNhds, functorNhds, inclusion, initial_of_adjunction, isOpenEmbedding, isoWhiskerLeft, toPresheaf, whiskeringLeft
-/
def restrictStalkNatIso (x : X) :
    restrictFunctor f ⋙ toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ x ≅
    toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ (f x) :=
  haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  (toPresheaf _ ⋙ (Functor.whiskeringLeft (OpenNhds (f x))ᵒᵖ Y.Opensᵒᵖ Ab).obj
      (OpenNhds.inclusion (f x)).op).isoWhiskerLeft
      (Functor.Final.colimIso (f.isOpenEmbedding.functorNhds x).op)

@[simp]
/--
lemma `germ_restrictStalkNatIso_hom_app` / 引理 `germ_restrictStalkNatIso_hom_app`

English:
lemma germ_restrictStalkNatIso_hom_app
  given: (x : X) (M : Y.Modules) (hxU : x in U)
  proof: haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  Functor.Final.ι_colimitIso_hom
    (f.isOpenEmbedding.functorNhds x).op
    ((OpenNhds.inclusion ((ConcreteCategory.hom f.base) x)).op ⋙ M.presheaf) _

中文:
引理 germ_restrictStalk自然数Iso_hom_app
  条件: (x : X) (M : Y.Modules) (hxU : x in U)
  证明: haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  Functor.Final.ι_colimitIso_hom
    (f.isOpenEmbedding.functorNhds x).op
    ((OpenNhds.inclusion ((ConcreteCategory.hom f.base) x)).op ⋙ M.presheaf) _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, Functor, Functor.Final, Functor.initial_of_adjunction, M.presheaf, OpenNhds, OpenNhds.inclusion, adjunctionNhds, f.base, f.isOpenEmbedding.adjunctionNhds, f.isOpenEmbedding.functorNhds, functorNhds, inclusion, initial_of_adjunction, isOpenEmbedding, presheaf
-/
lemma germ_restrictStalkNatIso_hom_app (x : X) (M : Y.Modules) (hxU : x in U) :
    ((restrictFunctor f).obj M).presheaf.germ U _ hxU ≫
      (restrictStalkNatIso f x).hom.app M = M.presheaf.germ _ _ (by simpa) :=
  haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  Functor.Final.ι_colimitIso_hom
    (f.isOpenEmbedding.functorNhds x).op
    ((OpenNhds.inclusion ((ConcreteCategory.hom f.base) x)).op ⋙ M.presheaf) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `germ_restrictStalkNatIso_inv_app` / 引理 `germ_restrictStalkNatIso_inv_app`

English:
lemma germ_restrictStalkNatIso_inv_app
  given: (x : X) (M : Y.Modules) (hxU : x in U)
  proof: by
  rw [← germ_restrictStalkNatIso_hom_app f x M hxU]; rw [Category.assoc]; rw [← NatTrans.comp_app]; rw [Iso.hom_inv_id]
  simp

中文:
引理 germ_restrictStalk自然数Iso_inv_app
  条件: (x : X) (M : Y.Modules) (hxU : x in U)
  证明: by
  rw [← germ_restrictStalkNatIso_hom_app f x M hxU]; rw [Category.assoc]; rw [← NatTrans.comp_app]; rw [Iso.hom_inv_id]
  simp

Depends on / 依赖: Category, Category.assoc, Iso.hom_inv_id, NatTrans, NatTrans.comp_app, comp_app, germ_restrictStalkNatIso_hom_app, hom_inv_id
-/
lemma germ_restrictStalkNatIso_inv_app (x : X) (M : Y.Modules) (hxU : x in U) :
    M.presheaf.germ _ _ (by simpa) ≫ (restrictStalkNatIso f x).inv.app M =
      ((restrictFunctor f).obj M).presheaf.germ U _ hxU := by
  rw [← germ_restrictStalkNatIso_hom_app f x M hxU]; rw [Category.assoc]; rw [← NatTrans.comp_app]; rw [Iso.hom_inv_id]
  simp

end Restriction

/--
Definition of `sheafComposePushforwardComp` / `sheafComposePushforwardComp` 的定义

English:
definition sheafComposePushforwardComp
  signature: {R S : CommRingCat.{u}} (φ : R ⟶ S)
  body: by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp φ.hom ((Scheme.ΓSpecIso S).inv).hom).app _
      rw [← CommRingCat.hom_co

中文:
定义 sheafComposePushforwardComp
  签名: {R S : 交换环范畴.{u}} (φ : R ⟶ S)
  定义体: by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp φ.hom ((Scheme.ΓSpecIso S).inv).hom).app _
      rw [← CommRingCat.hom_co

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, ModuleCat, ModuleCat.restrictScalarsComp, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.isoMk, Scheme, cat_disch, hom_comp, ofComponents, restrictScalarsComp
-/
noncomputable def sheafComposePushforwardComp {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    sheafCompose (Opens.grothendieckTopology (Spec S))
      (ModuleCat.restrictScalars (Spec.map φ).appTop.hom) ⋙
      TopCat.Sheaf.pushforward _ (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom) ≅
    sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso S).inv.hom) ⋙
      TopCat.Sheaf.pushforward _ (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars φ.hom) := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp φ.hom ((Scheme.ΓSpecIso S).inv).hom).app _
      rw [← CommRingCat.hom_comp]; rw [Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.hom_comp]
    · cat_disch
  · cat_disch

/-- Sheaves of modules on `𝒪_X` restricted to `U` are equivalent to sheaves of `𝒪_U`-modules. -/
noncomputable
/--
Definition of `overEquiv` / `overEquiv` 的定义

English:
definition overEquiv
  signature: {X : Scheme.{u}} (U : X.Opens)
  body: TopologicalSpace.Opens.sheafOfModulesEquivOver _ _

中文:
定义 overEquiv
  签名: {X : 概形.{u}} (U : X.Opens)
  定义体: TopologicalSpace.Opens.sheafOfModulesEquivOver _ _

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.sheafOfModulesEquivOver, sheafOfModulesEquivOver
-/
def overEquiv {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules (X.ringCatSheaf.over U) ≌ (U : Scheme.{u}).Modules :=
  TopologicalSpace.Opens.sheafOfModulesEquivOver _ _

set_option backward.isDefEq.respectTransparency false in
/-- Up to `Scheme.Modules.overEquiv`, `SheafOfModules.overMap` is isomorphic to
`Scheme.Modules.restrictFunctor`. -/
noncomputable
/--
Definition of `overMapCompOverEquiv` / `overMapCompOverEquiv` 的定义

English:
definition overMapCompOverEquiv
  signature: {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U)
  body: by
  haveI : (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology U.carrier) :=
inferInstanceAs
      (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous _
      (Opens.grothendieckTopology U.toScheme)
  haveI := U.in

中文:
定义 overMapCompOverEquiv
  签名: {X : 概形.{u}} {U V : X.Opens} (f : V ⟶ U)
  定义体: by
  haveI : (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology U.carrier) :=
inferInstanceAs
      (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous _
      (Opens.grothendieckTopology U.toScheme)
  haveI := U.in

Depends on / 依赖: Hom.opensFunctor, IsContinuous, Opens.grothendieckTopology, U.carrier, U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence, U.toScheme, V.toScheme, X.homOfLE, carrier, grothendieckTopology, homOfLE, instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence, leOfHom, opensFunctor, toScheme
-/
def overMapCompOverEquiv {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) :
    overMap X.ringCatSheaf f ⋙ (overEquiv V).functor ≅
      (overEquiv U).functor ⋙ restrictFunctor (X.homOfLE <| leOfHom f) := by
  haveI : (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology U.carrier) :=
inferInstanceAs
      (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous _
      (Opens.grothendieckTopology U.toScheme)
  haveI := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  haveI : (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous
      (Opens.grothendieckTopology ↥V) (Opens.grothendieckTopology U.toScheme) :=
inferInstanceAs (X.homOfLE <| leOfHom f).opensFunctor.IsContinuous
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology U.toScheme)
  haveI : ((Opens.overEquivalence V).symm.functor ⋙ Over.map f).IsContinuous
      (Opens.grothendieckTopology ↥V) ((Opens.grothendieckTopology X).over U) :=
    Functor.isContinuous_comp _ _ _ (.over (Opens.grothendieckTopology _) _) _
  haveI : (Opens.overEquivalence U).symm.functor.IsContinuous (Opens.grothendieckTopology U)
      ((Opens.grothendieckTopology X).over U) :=
inferInstanceAs U.overEquivalence.inverse.IsContinuous (Opens.grothendieckTopology U.carrier)
      ((Opens.grothendieckTopology X).over U)
  haveI : ((X.homOfLE (leOfHom f)).opensFunctor ⋙
        (Opens.overEquivalence U).symm.functor).IsContinuous (Opens.grothendieckTopology ↥V)
      ((Opens.grothendieckTopology ↥X).over U) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology _) _
  refine (SheafOfModules.pushforwardComp _ _) ≪≫ ?_ ≪≫ (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · refine NatIso.ofComponents (fun W => Over.isoMk (eqToIso ?_) ?_) ?_
    · suffices U.ι ''ᵁ ((X.homOfLE (leOfHom f)) ''ᵁ W) = V.ι ''ᵁ W by simpa
      simp [← Scheme.Hom.comp_image]
    · cat_disch
    · cat_disch
  · ext W x
    suffices X.presheaf.map _ x = ((X.homOfLE <| leOfHom f).appIso _).inv x by simpa
    rw [Scheme.Hom.appIso_homOfLE_inv]
    rfl

/-- Up to `Scheme.Modules.overEquiv`, `SheafOfModules.overFunctor` is isomorphic to
`Scheme.Modules.restrictFunctor`. -/
noncomputable
/--
Definition of `overFunctorEquiv` / `overFunctorEquiv` 的定义

English:
definition overFunctorEquiv
  signature: {X : Scheme.{u}} (U : X.Opens)
  body: by
  have : ((Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology ↥U) (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp _ _ _ (.over (Opens.grothendieckTopology _) U) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.push

中文:
定义 overFunctorEquiv
  签名: {X : 概形.{u}} (U : X.Opens)
  定义体: by
  have : ((Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology ↥U) (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp _ _ _ (.over (Opens.grothendieckTopology _) U) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.push

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, Functor.isContinuous_comp, IsContinuous, Iso.refl_inv, Opens.grothendieckTopology, Opens.overEquivalence, Opposite, Opposite.op_unop, Over.forget, SheafOfModules, SheafOfModules.pushforwardComp, SheafOfModules.pushforwardCongr, forget, functor, grothendieckTopology, isContinuous_comp, map_id, op_unop
-/
def overFunctorEquiv {X : Scheme.{u}} (U : X.Opens) :
    overFunctor X.ringCatSheaf U ⋙ (overEquiv U).functor ≅ restrictFunctor U.ι := by
  have : ((Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology ↥U) (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp _ _ _ (.over (Opens.grothendieckTopology _) U) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr ?_
  simp only [CategoryTheory.Functor.map_id, Opposite.op_unop, Opens.ι_appIso, Iso.refl_inv]
  rfl

end AlgebraicGeometry.Scheme.Modules
