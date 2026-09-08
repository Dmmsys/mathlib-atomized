/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `ΓSpec.adjunction : Γ ⊣ Spec` by defining the unit (`toΓSpec`,
in multiple steps in this file) and counit (done in `Spec.lean`) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`
extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `AlgebraicGeometry.identityToΓSpec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `AlgebraicGeometry.ΓSpec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open TopCat.Presheaf

open TopCat.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the underlying set to the prime spectrum of `Γ(X)`.
-/
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyRingedSpace.notMem_prime_iff_unit_in_stalk** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) : r ∉ (X.toΓSpec
Fun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r)
参数：r : Γ.obj (op X)；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r) := by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

set_option backward.isDefEq.respectTransparency false in
/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets).
-/
theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' basicOpen r = SetLike.coe (X.toRingedSpace.basicOpen r) := by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

/-- `toΓSpecFun` is continuous. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toΓSpecFun` is continuous.
-/
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections.
-/
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) :=
  TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebraic
Geometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set).
-/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage is the basic open in `X` defined by the same element `r`.
-/
theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.toTo** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra
icGeometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the global sections `Γ(X)` to the sections on the (preimage of) a b
asic open.
-/
abbrev toToΓSpecMapBasicOpen :
    X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

set_option backward.isDefEq.respectTransparency false in
/-- `r` is a unit as a section on the basic open defined by `r`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.isUnit_res_to** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`r` is a unit as a section on the basic open defined by `r`.
-/
theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert!
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr

set_option backward.isDefEq.respectTransparency.types false in
/-- Define the sheaf hom on individual basic opens for the unit. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the sheaf hom on individual basic opens for the unit.
-/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
  CommRingCat.ofHom <|
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).obj.obj (op (basicOpen r)))
      r
      (isUnit_res_toΓSpecMapBasicOpen _ r)

set_option backward.isDefEq.respectTransparency false in
/-- Characterization of the sheaf hom on basic opens,
direction ← (next lemma) is used at various places, but → is not used in this file. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of the sheaf hom on basic opens,
direction ← (next lemma) is used at various places, but → is not used in this fi
le.
-/
theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
        X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ f = X.toToΓSpecMapBasicOpen r ↔
      f = X.toΓSpecCApp r := by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Submonoid.powers r) h
  apply congr_arg
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toΓSpecCApp_spec :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf hom on all basic opens, commuting with restrictions. -/
@[simps app]
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf hom on all basic opens, commuting with restrictions.
-/
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((TopCat.Sheaf.pushforward _ X.toΓSpecBase).obj X.𝒪).1 where
  app r := X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    simp only [← Category.assoc]
    rw [show algebraMap (Γ.obj (op X)) ((structureSheaf (Γ.obj (op X))).obj.obj _) = algebraMap _
      ((structureSheafInType (Γ.obj (op X)) (Γ.obj (op X))).obj.obj _) from rfl,
      X.toΓSpecCApp_spec r.unop]
    convert! X.toΓSpecCApp_spec s.unop
    symm
    apply X.presheaf.map_comp

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps! -isSimp]
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism of sheafed spaces from `X` to the spectrum of its global 
sections.
-/
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) :=
  InducedCategory.homMk
    { base := X.toΓSpecBase
      c :=
        TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
          X.toΓSpecCBasicOpens }
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) = X.toΓSpecCApp r := by
  apply TopCat.Sheaf.extend_hom_app _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc] theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫
        X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r

set_option backward.isDefEq.respectTransparency false in
/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
stalks (in `Spec Γ(X)` and in `X`). -/
/-
**AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_to** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on stalks induced by the unit commutes with maps from `Γ(X)` to
stalks (in `Spec Γ(X)` and in `X`).
-/
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ _ ≫ X.toΓSpecSheafedSpace.hom.stalkMap x = X.presheaf.Γgerm x := by
  rw [PresheafedSpace.Hom.stalkMap,
    ← algebraMap_germ (basicOpen (1 : Γ.obj (op X))) _ (by rw [basicOpen_one]; trivial),
    ← Category.assoc, Category.assoc (CommRingCat.ofHom _), stalkFunctor_map_germ, ← Category.assoc,
    X.toΓSpecSheafedSpace_app_eq, X.toΓSpecCApp_spec, Γgerm,
    ← dsimp% stalkPushforward_germ _ _ X.presheaf ⊤]
  congr 1
  exact (X.toΓSpecBase _* X.presheaf).germ_res le_top.hom _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps! base]
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from `X` to the spectrum of its global sections.
-/
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) :=
  LocallyRingedSpace.homMk (X.toΓSpecSheafedSpace) (fun x ↦ by
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdeal.primeCompl t
    dsimp at he
    set t' := _
    change t * t' = _ at he
    apply isUnit_of_mul_isUnit_left (y := t')
    rw [he]
    refine IsLocalization.map_units S (⟨r, ?_⟩ : p.asIdeal.primeCompl)
    apply (notMem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← toStalk_stalkMap_toΓSpec, CommRingCat.comp_apply]
    erw [← he]
    rw [map_mul]
    exact ht.mul <| (IsLocalization.map_units (R := Γ.obj (op X)) S s).map _)

set_option backward.isDefEq.respectTransparency false in
/-- On a locally ringed space `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `toΓSpec` agrees with the associated zero locus on `X`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.to** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a locally ringed space `X`, the preimage of the zero locus of the prime spect
rum
of `Γ(X, ⊤)` under `toΓSpec` agrees with the associated zero locus on `X`.
-/
lemma toΓSpec_preimage_zeroLocus_eq {X : LocallyRingedSpace.{u}}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpec.base ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i ∈ s) :
      (SetLike.coe (X.toRingedSpace.basicOpen i))ᶜ =
        X.toΓSpec.base ⁻¹' ((PrimeSpectrum.basicOpen i).carrier)ᶜ := by
    symm
    rw [Set.preimage_compl, Opens.carrier_eq_coe]
    erw [X.toΓSpec_preimage_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  simp_rw [← Set.preimage_iInter₂, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.LocallyRingedSpace.comp_ring_hom_ext** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : 
R ⟶ Γ.obj (op X)} {β : X ⟶ Spec.locallyRingedSpaceObj R} (w : X.toΓSpec.base ≫ (
Spec.locallyRingedSpaceMap f).base = β.base) (h : forall r : R, f ≫ X.presheaf.m
ap (homOfLE le_top : (Opens.map β.base).obj (basicOpen r) ⟶ _).op = CommRingCat.
ofHom (algebraMap _ _) ≫ β.c.app (op (basicOpen r))) : X.toΓSpec ≫ Spec.locallyR
ingedSpaceMap f = β
参数：op X；w : X.toΓSpec.base ≫ (Spec.locallyRingedSpaceMap f).base = β.base；h : fo
rall r : R, f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.base).obj (basicOp
en r) ⟶ _).op = CommRingCat.ofHom (algebraMap _ _) ≫ β.c.app (op (basicOpen r))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instFaithfulSheafedSpaceCommRingCat
ForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace.
Faithful
· 使用定理 `AlgebraicGeometry.Spec.basicOpen_hom_ext`：∀ {X : AlgebraicGeometry.Ringe
dSpace} {R : CommRingCat} {α β : X ⟶ AlgebraicGeometry.Spec.sheafedSpaceObj R}  
 (w : α.hom.base = β.hom.base)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.SheafedSpace.comp_hom_c_app`：comp_hom_c_app {X Y Z : S
heafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α ≫ β).hom.c.app U = β.hom.c.app U
 ≫ α.hom.c.app (op ((Opens.map β.ho…
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用定理 `AlgebraicGeometry.StructureSheaf.toOpen_comp_comap_assoc`：∀ {R : Type u}
 [inst : CommRing R] {S : Type u} [inst_1 : CommRing S] (f : R →+* S)   (U : Top
ologicalSpace.Opens ↑(AlgebraicGeometry.PrimeS…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_app_spec`：∀ (X 
: AlgebraicGeometry.LocallyRingedSpace) (r : ↑(AlgebraicGeometry.LocallyRingedSp
ace.Γ.obj (Opposite.op X))),   CategoryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.base ≫ (Spec.locallyRingedSpaceMap f).base = β.base)
    (h :
      ∀ r : R,
        f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.base).obj (basicOpen r) ⟶ _).op =
          CommRingCat.ofHom (algebraMap _ _) ≫ β.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  refine LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (Spec.basicOpen_hom_ext w ?_)
  intro r U
  erw [SheafedSpace.comp_hom_c_app, toOpen_comp_comap_assoc]
  dsimp
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

set_option backward.isDefEq.respectTransparency.types false in
/-- `toSpecΓ _` is an isomorphism so these are mutually two-sided inverses. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toSpecΓ _` is an isomorphism so these are mutually two-sided inverses.
-/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _ := by
  unfold toSpecΓ
  have := X.toΓSpecSheafedSpace_app_spec 1
  unfold toToΓSpecMapBasicOpen toΓSpecMapBasicOpen at this
  rw! [basicOpen_one] at this
  convert! this
  exact (X.presheaf.map_id ..).symm

end LocallyRingedSpace

set_option backward.isDefEq.respectTransparency false in
/-- The unit as a natural transformation. -/
/-
**AlgebraicGeometry.identityTo** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit as a natural transformation.
-/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp
      change PrimeSpectrum.comap (f.c.app (op ⊤)).hom (X.toΓSpecFun x) = Y.toΓSpecFun (f.base x)
      dsimp [toΓSpecFun]
      rw [← IsLocalRing.comap_closedPoint (f.stalkMap x).hom, ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
        ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 2
      exact (PresheafedSpace.stalkMap_germ f.1 ⊤ x trivial).symm
    · intro r
      rw [LocallyRingedSpace.comp_c_app, ← Category.assoc]
      erw [Y.toΓSpecSheafedSpace_app_spec, f.c.naturality]
      rfl

namespace ΓSpec

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ΓSpec.left_triangle** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.ΓSpec`。
形式化陈述：left_triangle (X : LocallyRingedSpace) : SpecΓIdentity.inv.app (Γ.obj (op 
X)) ≫ (identityToΓSpec.app X).c.app (op ⊤) = 𝟙 _
参数：X : LocallyRingedSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Γ_Spec_left_triangle`：Γ_Spec_left_t
riangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _
-/
theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `SpecΓIdentity` is iso so these are mutually two-sided inverses. -/
/-
**AlgebraicGeometry.ΓSpec.right_triangle** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.ΓSpec`。
形式化陈述：right_triangle (R : CommRingCat) : identityToΓSpec.app (Spec.toLocallyRing
edSpace.obj <| op R) ≫ Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).o
p = 𝟙 _
参数：R : CommRingCat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.comp_ring_hom_ext`：comp_ring_hom_ex
t {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)} {β :
 X ⟶ Spec.locallyRingedSpaceObj R} (w : X.to…
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
`SpecΓIdentity` is iso so these are mutually two-sided inverses.
-/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ := by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps]
/-
**AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.ΓSpec`。
形式化陈述：locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} w
here unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`.
-/
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  unit := identityToΓSpec
  counit := (NatIso.op SpecΓIdentity).inv
  left_triangle_components X := by
    simp only [Functor.id_obj, Γ_obj, Functor.rightOp_map, Γ_map,
      Quiver.Hom.unop_op, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact congr_arg Quiver.Hom.op (left_triangle X)
  right_triangle_components R := by
    simp only [Functor.id_obj, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact right_triangle R.unop


set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ΓSpec.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.ΓS
pec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecΓ_unop (R : CommRingCatᵒᵖ) :
    AlgebraicGeometry.toSpecΓ (Opposite.unop R) = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `locallyRingedSpaceAdjunction_counit_app'`. -/
@[simp]
/-
**AlgebraicGeometry.ΓSpec.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.ΓS
pec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`@[simp]`-normal form of `locallyRingedSpaceAdjunction_counit_app'`.
-/
lemma toSpecΓ_of (R : Type u) [CommRing R] :
    AlgebraicGeometry.toSpecΓ (CommRingCat.of R) = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction_counit_app** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：locallyRingedSpaceAdjunction_counit_app (R : CommRingCatᵒᵖ) : locallyRinge
dSpaceAdjunction.counit.app R = (CommRingCat.ofHom (algebraMap _ _)).op
参数：R : CommRingCatᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma locallyRingedSpaceAdjunction_counit_app (R : CommRingCatᵒᵖ) :
    locallyRingedSpaceAdjunction.counit.app R =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction_counit_app'** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] : local
lyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R) = (CommRingCat.ofHom
 (algebraMap _ _)).op
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R) =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ΓSpec.unop_locallyRingedSpaceAdjunction_counit_app'** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：unop_locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] : 
(locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R)).unop = (CommR
ingCat.ofHom (algebraMap _ _))
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    (locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R)).unop =
      (CommRingCat.ofHom (algebraMap _ _)) := rfl
/-
**AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：locallyRingedSpaceAdjunction_homEquiv_apply {X : LocallyRingedSpace} {R : 
CommRingCatᵒᵖ} (f : Γ.rightOp.obj X ⟶ R) : locallyRingedSpaceAdjunction.homEquiv
 X R f = identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f.unop
参数：f : Γ.rightOp.obj X ⟶ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma locallyRingedSpaceAdjunction_homEquiv_apply
    {X : LocallyRingedSpace} {R : CommRingCatᵒᵖ}
    (f : Γ.rightOp.obj X ⟶ R) :
    locallyRingedSpaceAdjunction.homEquiv X R f =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f.unop := rfl
/-
**AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply'** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：locallyRingedSpaceAdjunction_homEquiv_apply' {X : LocallyRingedSpace} {R :
 Type u} [CommRing R] (f : CommRingCat.of R ⟶ Γ.obj <| op X) : locallyRingedSpac
eAdjunction.homEquiv X (op <| CommRingCat.of R) (op f) = identityToΓSpec.app X ≫
 Spec.locallyRingedSpaceMap f
参数：f : CommRingCat.of R ⟶ Γ.obj <| op X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma locallyRingedSpaceAdjunction_homEquiv_apply'
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : CommRingCat.of R ⟶ Γ.obj <| op X) :
    locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) (op f) =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app*
* 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app {X : LocallyRingedSp
ace} {R : Type u} [CommRing R] (f : Γ.rightOp.obj X ⟶ op (CommRingCat.of R)) (U)
 : CommRingCat.ofHom (algebraMap R _) ≫ (locallyRingedSpaceAdjunction.homEquiv X
 (op <| CommRingCat.of R) f).c.app U = f.unop ≫ X.presheaf.map (homOfLE le_top).
op
参数：f : Γ.rightOp.obj X ⟶ op (CommRingCat.of R)；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.StructureSheaf.algebraMap_self_map`：algebraMap_self_ma
p (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U) : CommRingCat.ofHom (algeb
raMap R _) ≫ (Spec.structureSheaf R).1.map…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `AlgebraicGeometry.ΓSpec.unop_locallyRingedSpaceAdjunction_counit_app'`：u
nop_locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] : (locall
yRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R))…
· 使用引理 `CategoryTheory.Functor.rightOp_map_unop`：rightOp_map_unop {F : Cᵒᵖ ⥤ D} 
{X Y} (f : X ⟶ Y) : (F.rightOp.map f).unop = F.map f.op
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : Γ.rightOp.obj X ⟶ op (CommRingCat.of R)) (U) :
    CommRingCat.ofHom (algebraMap R _) ≫
      (locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) f).c.app U =
    f.unop ≫ X.presheaf.map (homOfLE le_top).op := by
  dsimp
  rw [← StructureSheaf.algebraMap_self_map _ U _ (homOfLE le_top).op, Category.assoc,
    NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op,
    ← unop_locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop, ← Category.assoc, ← unop_comp]
  erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
/-
**AlgebraicGeometry.ΓSpec.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.ΓSpec`。
形式化陈述：adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`.
-/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  unit :=
  { app := fun X ↦ ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun _ _ f ↦
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
  left_triangle_components Y :=
    locallyRingedSpaceAdjunction.left_triangle_components Y.toLocallyRingedSpace
  right_triangle_components R :=
    Scheme.Hom.ext' <| locallyRingedSpaceAdjunction.right_triangle_components R

/-- Given `f, g : X ⟶ Spec(R)`, if the two induced maps `R ⟶ Γ(X)` are equal, then `f = g`. -/
/-
**AlgebraicGeometry.ΓSpec._root_.AlgebraicGeometry.ext_to_Spec** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.ΓSpec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f, g : X ⟶ Spec(R)`, if the two induced maps `R ⟶ Γ(X)` are equal, then `
f = g`.
-/
lemma _root_.AlgebraicGeometry.ext_to_Spec {X : Scheme} {R : Type*} [CommRing R]
    {f g : X ⟶ Spec (.of R)}
    (h : (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map f.op =
      (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map g.op) :
    f = g :=
  (ΓSpec.adjunction.homEquiv X (.op <| .of R)).symm.injective <| Opposite.unop_injective h
/-
**AlgebraicGeometry.ΓSpec.adjunction_homEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.ΓSpec`。
形式化陈述：adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ} (f : (op <| Sch
eme.Γ.obj <| op X) ⟶ R) : ΓSpec.adjunction.homEquiv X R f = ⟨locallyRingedSpaceA
djunction.homEquiv X.1 R f⟩
参数：f : (op <| Scheme.Γ.obj <| op X) ⟶ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = ⟨locallyRingedSpaceAdjunction.homEquiv X.1 R f⟩ := rfl
/-
**AlgebraicGeometry.ΓSpec.adjunction_homEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ} (f : X ⟶ S
cheme.Spec.obj R) : (ΓSpec.adjunction.homEquiv X R).symm f = (locallyRingedSpace
Adjunction.homEquiv X.1 R).symm f.toLRSHom
参数：f : X ⟶ Scheme.Spec.obj R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.Spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f =
      (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f.toLRSHom := rfl
/-
**AlgebraicGeometry.ΓSpec.adjunction_counit_app'** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.ΓSpec`。
形式化陈述：adjunction_counit_app' {R : CommRingCatᵒᵖ} : ΓSpec.adjunction.counit.app R
 = locallyRingedSpaceAdjunction.counit.app R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjunction_counit_app' {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := rfl

@[simp]
/-
**AlgebraicGeometry.ΓSpec.adjunction_counit_app** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.ΓSpec`。
形式化陈述：adjunction_counit_app {R : CommRingCatᵒᵖ} : ΓSpec.adjunction.counit.app R 
= (Scheme.ΓSpecIso (unop R)).inv.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = (Scheme.ΓSpecIso (unop R)).inv.op := rfl

/-- The canonical map `X ⟶ Spec Γ(X, ⊤)`. This is the unit of the `Γ-Spec` adjunction. -/
/-
**AlgebraicGeometry.ΓSpec._root_.AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.ΓSpec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `X ⟶ Spec Γ(X, ⊤)`. This is the unit of the `Γ-Spec` adjunctio
n.
-/
def _root_.AlgebraicGeometry.Scheme.toSpecΓ (X : Scheme.{u}) : X ⟶ Spec Γ(X, ⊤) :=
  ΓSpec.adjunction.unit.app X

@[simp]
/-
**AlgebraicGeometry.ΓSpec.adjunction_unit_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.ΓSpec`。
形式化陈述：adjunction_unit_app {X : Scheme} : ΓSpec.adjunction.unit.app X = X.toSpecΓ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.unit.app X = X.toSpecΓ := rfl
/-
**AlgebraicGeometry.ΓSpec.isIso_locallyRingedSpaceAdjunction_counit** 是 Mathlib 
中的一个实例，位于命名空间 `AlgebraicGeometry.ΓSpec`。
形式化陈述：isIso_locallyRingedSpaceAdjunction_counit : IsIso.{u + 1, u + 1} locallyRi
ngedSpaceAdjunction.counit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance isIso_locallyRingedSpaceAdjunction_counit :
    IsIso.{u + 1, u + 1} locallyRingedSpaceAdjunction.counit :=
  (NatIso.op SpecΓIdentity).isIso_inv

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.ΓSpec.isIso_adjunction_counit** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.ΓSpec`。
形式化陈述：isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.ΓSpec.adjunction_counit_app`：adjunction_counit_app {R 
: CommRingCatᵒᵖ} : ΓSpec.adjunction.counit.app R = (Scheme.ΓSpecIso (unop R)).in
v.op
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply +allowSynthFailures NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

end ΓSpec

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Scheme.toSpecΓ_apply (X : Scheme.{u}) (x) :
    Scheme.toSpecΓ X x = Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _) := rfl

@[reassoc]
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Scheme.toSpecΓ_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map f.appTop :=
  ΓSpec.adjunction.unit.naturality f

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Scheme.toSpecΓ_appTop (X : Scheme.{u}) :
    X.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff, this, ← op_inv, IsIso.Iso.inv_inv]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.SpecMap_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SpecMap_ΓSpecIso_hom (R : CommRingCat.{u}) :
    Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ := by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.SpecMap_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SpecMap_ΓSpecIso_inv_toSpecΓ (R : CommRingCat.{u}) :
    Spec.map (Scheme.ΓSpecIso R).inv ≫ (Spec R).toSpecΓ = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.toSpec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSpecΓ_SpecMap_ΓSpecIso_inv (R : CommRingCat.{u}) :
    (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
/-
**AlgebraicGeometry.Scheme.toSpec** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.toSpecΓ_preimage_basicOpen (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen r := by
  rw [← basicOpen_eq_of_affine, Scheme.preimage_basicOpen, ← Scheme.Hom.appTop]
  congr
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓSpecIso_inv_ΓSpec_adjunction_homEquiv {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = φ := by
  simp only [Adjunction.homEquiv_apply, Scheme.Spec_map, Opens.map_top, Scheme.Hom.comp_app]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓSpec_adjunction_homEquiv_eq {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [← Iso.inv_comp_eq, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ΓSpecIso_obj_hom {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).hom = (Spec.map U.topIso.inv).appTop ≫
      U.toScheme.toSpecΓ.appTop ≫ U.topIso.hom := by simp

/-! Immediate consequences of the adjunction. -/

/-- The functor `Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace`
is fully faithful. -/
/-
**AlgebraicGeometry.Spec.fullyFaithfulToLocallyRingedSpace** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Spec`。
形式化陈述：AlgebraicGeometry.Spec.toLocallyRingedSpace.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace`
is fully faithful.
-/
def Spec.fullyFaithfulToLocallyRingedSpace : Spec.toLocallyRingedSpace.FullyFaithful :=
  ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Spec is a full functor.
-/
instance : Spec.toLocallyRingedSpace.Full :=
  Spec.fullyFaithfulToLocallyRingedSpace.full

/-- Spec is a faithful functor. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Spec is a faithful functor.
-/
instance : Spec.toLocallyRingedSpace.Faithful :=
  Spec.fullyFaithfulToLocallyRingedSpace.faithful

/-- The functor `Spec : CommRingCatᵒᵖ ⥤ Scheme` is fully faithful. -/
/-
**AlgebraicGeometry.Spec.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Spec`。
形式化陈述：AlgebraicGeometry.Scheme.Spec.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Spec : CommRingCatᵒᵖ ⥤ Scheme` is fully faithful.
-/
def Spec.fullyFaithful : Scheme.Spec.FullyFaithful :=
  ΓSpec.adjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor. -/
/-
**AlgebraicGeometry.Spec.full** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Spec`
。
形式化陈述：AlgebraicGeometry.Scheme.Spec.Full
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive

--- 原说明 ---
Spec is a full functor.
-/
instance Spec.full : Scheme.Spec.Full :=
  Spec.fullyFaithful.full

/-- Spec is a faithful functor. -/
/-
**AlgebraicGeometry.Spec.faithful** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
pec`。
形式化陈述：AlgebraicGeometry.Scheme.Spec.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective

--- 原说明 ---
Spec is a faithful functor.
-/
instance Spec.faithful : Scheme.Spec.Faithful :=
  Spec.fullyFaithful.faithful

section

variable {R S : CommRingCat.{u}} {φ ψ : R ⟶ S} (f : Spec S ⟶ Spec R)

/-
**AlgebraicGeometry.Spec.map_inj** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Sp
ec`。
形式化陈述：∀ {R S : CommRingCat} {φ ψ : R ⟶ S}, AlgebraicGeometry.Spec.map φ = Algebr
aicGeometry.Spec.map ψ ↔ φ = ψ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AlgebraicGeometry.Spec.faithful`：AlgebraicGeometry.Scheme.Spec.Faithful
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Spec.map_inj : Spec.map φ = Spec.map ψ ↔ φ = ψ := by
  rw [iff_comm, ← Quiver.Hom.op_inj.eq_iff, ← Scheme.Spec.map_injective.eq_iff]
  rfl
/-
**AlgebraicGeometry.Spec.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Spec`。
形式化陈述：∀ {R S : CommRingCat}, Function.Injective AlgebraicGeometry.Spec.map
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Spec.map_inj`：∀ {R S : CommRingCat} {φ ψ : R ⟶ S}, Alg
ebraicGeometry.Spec.map φ = AlgebraicGeometry.Spec.map ψ ↔ φ = ψ
-/
lemma Spec.map_injective {R S : CommRingCat} : Function.Injective (Spec.map : (R ⟶ S) → _) :=
  fun _ _ ↦ Spec.map_inj.mp

@[simp]
/-
**AlgebraicGeometry.Spec.map_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Spec`。
形式化陈述：∀ {R : CommRingCat} {ϕ : R ⟶ R},   AlgebraicGeometry.Spec.map ϕ = Category
Theory.CategoryStruct.id (AlgebraicGeometry.Spec R) ↔     ϕ = CategoryTheory.Cat
egoryStruct.id R
参数：AlgebraicGeometry.Spec R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Spec.map_eq_id {R : CommRingCat} {ϕ : R ⟶ R} : Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R := by
  simp [← map_inj]

/-- The preimage under Spec. -/
/-
**AlgebraicGeometry.Spec.preimage** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
pec`。
形式化陈述：{R S : CommRingCat} → (AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R
) → (R ⟶ S)
参数：AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R；R ⟶ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full

--- 原说明 ---
The preimage under Spec.
-/
def Spec.preimage : R ⟶ S := (Scheme.Spec.preimage f).unop
/-
**AlgebraicGeometry.Spec.map_preimage** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Spec`。
形式化陈述：∀ {R S : CommRingCat} (f : AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Sp
ec R),   AlgebraicGeometry.Spec.map (AlgebraicGeometry.Spec.preimage f) = f
参数：f : AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R；AlgebraicGeometry.Spe
c.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full
-/
@[simp] lemma Spec.map_preimage : Spec.map (Spec.preimage f) = f := Scheme.Spec.map_preimage f
/-
**AlgebraicGeometry.Spec.map_preimage_unop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Spec`。
形式化陈述：∀ {R S : CommRingCat} (f : AlgebraicGeometry.Spec R ⟶ AlgebraicGeometry.Sp
ec S),   AlgebraicGeometry.Spec.map (AlgebraicGeometry.Spec.fullyFaithful.preima
ge f).unop = f
参数：f : AlgebraicGeometry.Spec R ⟶ AlgebraicGeometry.Spec S；AlgebraicGeometry.Spe
c.fullyFaithful.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
-/
@[simp] lemma Spec.map_preimage_unop (f : Spec R ⟶ Spec S) :
    Spec.map (Spec.fullyFaithful.preimage f).unop = f := Spec.fullyFaithful.map_preimage _

variable (φ) in
/-
**AlgebraicGeometry.Spec.preimage_map** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Spec`。
形式化陈述：∀ {R S : CommRingCat} (φ : R ⟶ S), AlgebraicGeometry.Spec.preimage (Algebr
aicGeometry.Spec.map φ) = φ
参数：φ : R ⟶ S；AlgebraicGeometry.Spec.map φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_injective`：∀ {R S : CommRingCat}, Function.In
jective AlgebraicGeometry.Spec.map
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
-/
@[simp] lemma Spec.preimage_map : Spec.preimage (Spec.map φ) = φ :=
  Spec.map_injective (Spec.map_preimage (Spec.map φ))

/-- Useful for replacing `f` by `Spec.map φ` everywhere in proofs. -/
/-
**AlgebraicGeometry.Spec.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Spec`。
形式化陈述：∀ {R S : CommRingCat}, Function.Surjective AlgebraicGeometry.Spec.map
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Useful for replacing `f` by `Spec.map φ` everywhere in proofs.
-/
lemma Spec.map_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) → _) := by
  intro f
  use Spec.preimage f
  simp

/-- Spec is fully faithful -/
@[simps]
/-
**AlgebraicGeometry.Spec.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
pec`。
形式化陈述：{R S : CommRingCat} → (AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R
) ≃ (R ⟶ S)
参数：AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R；R ⟶ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `AlgebraicGeometry.Spec.preimage_map`：∀ {R S : CommRingCat} (φ : R ⟶ S), 
AlgebraicGeometry.Spec.preimage (AlgebraicGeometry.Spec.map φ) = φ

--- 原说明 ---
Spec is fully faithful
-/
def Spec.homEquiv {R S : CommRingCat} : (Spec S ⟶ Spec R) ≃ (R ⟶ S) where
  toFun := Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

@[simp]
/-
**AlgebraicGeometry.Spec.preimage_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.Spec`。
形式化陈述：∀ {R : CommRingCat},   AlgebraicGeometry.Spec.preimage (CategoryTheory.Cat
egoryStruct.id (AlgebraicGeometry.Spec R)) =     CategoryTheory.CategoryStruct.i
d R
参数：CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_injective`：∀ {R S : CommRingCat}, Function.In
jective AlgebraicGeometry.Spec.map
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Spec.preimage_id {R : CommRingCat} : Spec.preimage (𝟙 (Spec R)) = 𝟙 R :=
  Spec.map_injective (by simp)

@[simp, reassoc]
/-
**AlgebraicGeometry.Spec.preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Spec`。
形式化陈述：∀ {R S T : CommRingCat} (f : AlgebraicGeometry.Spec R ⟶ AlgebraicGeometry.
Spec S)   (g : AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec T),   Algebraic
Geometry.Spec.preimage (CategoryTheory.CategoryStruct.comp f g) =     CategoryTh
eory.CategoryStruct.comp (AlgebraicGeometry.Spec.preimage g) (AlgebraicGeometry.
Spec.preimage f)
参数：f : AlgebraicGeometry.Spec R ⟶ AlgebraicGeometry.Spec S；g : AlgebraicGeometry
.Spec S ⟶ AlgebraicGeometry.Spec T；CategoryTheory.CategoryStruct.comp f g；Algebr
aicGeometry.Spec.preimage g；AlgebraicGeometry.Spec.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_injective`：∀ {R S : CommRingCat}, Function.In
jective AlgebraicGeometry.Spec.map
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Spec.preimage_comp {R S T : CommRingCat} (f : Spec R ⟶ Spec S) (g : Spec S ⟶ Spec T) :
    Spec.preimage (f ≫ g) = Spec.preimage g ≫ Spec.preimage f :=
  Spec.map_injective (by simp)

end

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Reflective Spec.toLocallyRingedSpace where
  L := Γ.rightOp
  adj := ΓSpec.locallyRingedSpaceAdjunction
/-
**AlgebraicGeometry.Spec.reflective** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.Spec`。
形式化陈述：CategoryTheory.Reflective AlgebraicGeometry.Scheme.Spec
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full
· 使用定理 `AlgebraicGeometry.Spec.faithful`：AlgebraicGeometry.Scheme.Spec.Faithful
-/
instance Spec.reflective : Reflective Scheme.Spec where
  L := Scheme.Γ.rightOp
  adj := ΓSpec.adjunction
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyRingedSpace.Γ.IsRightAdjoint :=
  ΓSpec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Scheme.Γ.IsRightAdjoint := ΓSpec.adjunction.rightOp.isRightAdjoint

end AlgebraicGeometry

