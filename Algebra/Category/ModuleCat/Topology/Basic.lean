/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The category `TopModuleCat R` of topological modules

We define `TopModuleCat R`, the category of topological modules, and show that
it has all limits and colimits.

We also provide various adjunctions:
- `TopModuleCat.withModuleTopologyAdj`:
  equipping the module topology is left adjoint to the forgetful functor into `ModuleCat R`.
- `TopModuleCat.indiscreteAdj`:
  equipping the indiscrete topology is right adjoint to the forgetful functor into `ModuleCat R`.
- `TopModuleCat.freeAdj`:
  the free-forgetful adjunction between `TopModuleCat R` and `TopCat`.

## Future projects
Show that the forgetful functor to `TopCat` preserves filtered colimits.
-/

@[expose] public section

universe v u

variable (R : Type u) [Ring R] [TopologicalSpace R]

open CategoryTheory ConcreteCategory

/--
Definition of `TopModuleCat` / `TopModuleCat` 的定义

English:
structure TopModuleCat
  parameters: extends ModuleCat.{v} R
  extends: ModuleCat.{v} R
  axioms and operations (3):
    - [topologicalSpace : TopologicalSpace carrier]
    - [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
    - [continuousSMul : ContinuousSMul R carrier]

中文:
结构 TopModuleCat
  参数: extends ModuleCat.{v} R
  继承: ModuleCat.{v} R
  公理与运算 (3 个):
    - [topologicalSpace : TopologicalSpace carrier]
    - [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
    - [continuousSMul : ContinuousSMul R carrier]
-/
structure TopModuleCat extends ModuleCat.{v} R where
  /-- The underlying topological space. -/
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [continuousSMul : ContinuousSMul R carrier]

namespace TopModuleCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (TopModuleCat.{v} R) (Type v)
  body: ⟨fun M => M.toModuleCat⟩

中文:
实例 :
  签名: CoeSort (TopModuleCat.{v} R) (类型v)
  定义体: ⟨fun M => M.toModuleCat⟩

Depends on / 依赖: M.toModuleCat, toModuleCat
-/
noncomputable instance : CoeSort (TopModuleCat.{v} R) (Type v) := ⟨fun M => M.toModuleCat⟩

attribute [instance] topologicalSpace isTopologicalAddGroup continuousSMul

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
  body: have : ContinuousNeg M := ⟨by convert! continuous_const_smul (-1 : R) (T := M); ext; simp⟩
  have : IsTopologicalAddGroup M := ⟨⟩
  ⟨.of R M⟩

中文:
缩写 of
  签名: (M : 类型v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
  定义体: have : ContinuousNeg M := ⟨by convert! continuous_const_smul (-1 : R) (T := M); ext; simp⟩
  have : IsTopologicalAddGroup M := ⟨⟩
  ⟨.of R M⟩

Depends on / 依赖: ContinuousNeg, IsTopologicalAddGroup, continuous_const_smul, convert
-/
abbrev of (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : TopModuleCat R :=
  have : ContinuousNeg M := ⟨by convert! continuous_const_smul (-1 : R) (T := M); ext; simp⟩
  have : IsTopologicalAddGroup M := ⟨⟩
  ⟨.of R M⟩

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  statement: (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
  proof: rfl

中文:
引理 coe_of
  结论: (M : 类型v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
  证明: rfl
-/
lemma coe_of (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : (of R M) = M := rfl

variable {R} in
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : TopModuleCat.{v} R)
  axioms and operations (2):
    - private(ofHom') : :
    - hom' : X ->L[R] Y

中文:
结构 Hom
  参数: (X Y : TopModuleCat.{v} R)
  公理与运算 (2 个):
    - private(ofHom') : :
    - hom' : X ->L[R] Y
-/
structure Hom (X Y : TopModuleCat.{v} R) where
  -- use `ofHom` instead
  private ofHom' ::
  /-- The underlying continuous linear map. Use `hom` instead. -/
  hom' : X ->L[R] Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (TopModuleCat R)
  body: Hom
  id M := ⟨ContinuousLinearMap.id R M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩

中文:
实例 :
  签名: Category (TopModuleCat R)
  定义体: Hom
  id M := ⟨ContinuousLinearMap.id R M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩
-/
instance : Category (TopModuleCat R) where
  Hom := Hom
  id M := ⟨ContinuousLinearMap.id R M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (TopModuleCat R) (· ->L[R] ·)
  body: Hom.hom'
  ofHom := Hom.ofHom'

中文:
实例 :
  签名: ConcreteCategory (TopModuleCat R) (· ->L[R] ·)
  定义体: Hom.hom'
  ofHom := Hom.ofHom'

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (TopModuleCat R) (· ->L[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.ofHom'

variable {R} in
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : TopModuleCat R} (f : X.Hom Y)
  body: ConcreteCategory.hom (C := TopModuleCat R) f

中文:
缩写 Hom.hom
  签名: {X Y : TopModuleCat R} (f : X.Hom Y)
  定义体: ConcreteCategory.hom (C := TopModuleCat R) f
-/
abbrev Hom.hom {X Y : TopModuleCat R} (f : X.Hom Y) : X ->L[R] Y :=
  ConcreteCategory.hom (C := TopModuleCat R) f

variable {R} in
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type v}
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: {X Y : 类型v}
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X ->L[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f

/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {X Y : Type v}
  proof: rfl

中文:
引理 hom_ofHom
  结论: {X Y : 类型v}
  证明: rfl
-/
@[simp] lemma hom_ofHom {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X ->L[R] Y) :
    (ofHom f).hom = f := rfl

/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : TopModuleCat R} (f : X.Hom Y)
  statement: ofHom f.hom = f
  proof: rfl

中文:
引理 ofHom_hom
  条件: {X Y : TopModuleCat R} (f : X.Hom Y)
  结论: ofHom f.hom = f
  证明: rfl
-/
@[simp] lemma ofHom_hom {X Y : TopModuleCat R} (f : X.Hom Y) : ofHom f.hom = f := rfl

/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : TopModuleCat R} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : TopModuleCat R} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
@[simp] lemma hom_comp {X Y Z : TopModuleCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: (X : TopModuleCat R)
  statement: hom (𝟙 X) = .id _ _
  proof: rfl

中文:
引理 hom_id
  条件: (X : TopModuleCat R)
  结论: hom (𝟙 X) = .id _ _
  证明: rfl
-/
@[simp] lemma hom_id (X : TopModuleCat R) : hom (𝟙 X) = .id _ _ := rfl

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (A B : TopModuleCat.{v} R) (f : A.Hom B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (A B : TopModuleCat.{v} R) (f : A.Hom B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (A B : TopModuleCat.{v} R) (f : A.Hom B) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

variable {R} in
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {X Y : TopModuleCat R} (e : X ≃L[R] Y)
  body: ⟨ofHom e.toContinuousLinearMap, ofHom e.symm.toContinuousLinearMap,
    by ext; exact e.symm_apply_apply _, by ext; exact e.apply_symm_apply _⟩

中文:
定义 ofIso
  签名: {X Y : TopModuleCat R} (e : X ≃L[R] Y)
  定义体: ⟨ofHom e.toContinuousLinearMap, ofHom e.symm.toContinuousLinearMap,
    by ext; exact e.symm_apply_apply _, by ext; exact e.apply_symm_apply _⟩

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.symm.toContinuousLinearMap, e.symm_apply_apply, e.toContinuousLinearMap, symm_apply_apply, toContinuousLinearMap
-/
def ofIso {X Y : TopModuleCat R} (e : X ≃L[R] Y) : X ≅ Y :=
  ⟨ofHom e.toContinuousLinearMap, ofHom e.symm.toContinuousLinearMap,
    by ext; exact e.symm_apply_apply _, by ext; exact e.apply_symm_apply _⟩

variable {R} in
/--
Definition of `_root_.CategoryTheory.Iso.toContinuousLinearEquiv` / `_root_.CategoryTheory.Iso.toContinuousLinearEquiv` 的定义

English:
definition _root_.CategoryTheory.Iso.toContinuousLinearEquiv
  body: e.hom.hom
  invFun := e.inv.hom
  left_inv x := by cat_disch
  right_inv x := by cat_disch

中文:
定义 _root_.CategoryTheory.Iso.toContinuousLinearEquiv
  定义体: e.hom.hom
  invFun := e.inv.hom
  left_inv x := by cat_disch
  right_inv x := by cat_disch

Depends on / 依赖: e.hom.hom
-/
def _root_.CategoryTheory.Iso.toContinuousLinearEquiv
    {X Y : TopModuleCat R} (e : X ≅ Y) : X ≃L[R] Y where
  __ := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by cat_disch
  right_inv x := by cat_disch

instance {X Y : TopModuleCat R} : AddCommGroup (X ⟶ Y) where
  add f g := ofHom (f.hom + g.hom)
  zero := ofHom 0
  __ := Equiv.addCommGroup CategoryTheory.ConcreteCategory.homEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (TopModuleCat R)
  body: ConcreteCategory.ext (ContinuousLinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.add_comp _ _ _)

中文:
实例 :
  签名: Preadditive (TopModuleCat R)
  定义体: ConcreteCategory.ext (ContinuousLinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.add_comp _ _ _)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, ContinuousLinearMap, ContinuousLinearMap.comp_add, comp_add
-/
instance : Preadditive (TopModuleCat R) where
  add_comp _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.add_comp _ _ _)

section

variable {M₁ M₂ : TopModuleCat R}

/--
lemma `hom_zero` / 引理 `hom_zero`

English:
lemma hom_zero
  statement: (0 : M₁ ⟶ M₂).hom = 0
  proof: rfl

中文:
引理 hom_zero
  结论: (0 : M₁ ⟶ M₂).hom = 0
  证明: rfl
-/
@[simp] lemma hom_zero : (0 : M₁ ⟶ M₂).hom = 0 := rfl
/--
lemma `hom_zero_apply` / 引理 `hom_zero_apply`

English:
lemma hom_zero_apply
  given: (m : M₁)
  statement: (0 : M₁ ⟶ M₂).hom m = 0
  proof: rfl

中文:
引理 hom_zero_apply
  条件: (m : M₁)
  结论: (0 : M₁ ⟶ M₂).hom m = 0
  证明: rfl
-/
lemma hom_zero_apply (m : M₁) : (0 : M₁ ⟶ M₂).hom m = 0 := rfl
/--
lemma `hom_add` / 引理 `hom_add`

English:
lemma hom_add
  given: (φ₁ φ₂ : M₁ ⟶ M₂)
  statement: (φ₁ + φ₂).hom = φ₁.hom + φ₂.hom
  proof: rfl

中文:
引理 hom_add
  条件: (φ₁ φ₂ : M₁ ⟶ M₂)
  结论: (φ₁ + φ₂).hom = φ₁.hom + φ₂.hom
  证明: rfl
-/
@[simp] lemma hom_add (φ₁ φ₂ : M₁ ⟶ M₂) : (φ₁ + φ₂).hom = φ₁.hom + φ₂.hom := rfl
/--
lemma `hom_neg` / 引理 `hom_neg`

English:
lemma hom_neg
  given: (φ : M₁ ⟶ M₂)
  statement: (-φ).hom = -φ.hom
  proof: rfl

中文:
引理 hom_neg
  条件: (φ : M₁ ⟶ M₂)
  结论: (-φ).hom = -φ.hom
  证明: rfl
-/
@[simp] lemma hom_neg (φ : M₁ ⟶ M₂) : (-φ).hom = -φ.hom := rfl
/--
lemma `hom_sub` / 引理 `hom_sub`

English:
lemma hom_sub
  given: (φ₁ φ₂ : M₁ ⟶ M₂)
  statement: (φ₁ - φ₂).hom = φ₁.hom - φ₂.hom
  proof: rfl

中文:
引理 hom_sub
  条件: (φ₁ φ₂ : M₁ ⟶ M₂)
  结论: (φ₁ - φ₂).hom = φ₁.hom - φ₂.hom
  证明: rfl
-/
@[simp] lemma hom_sub (φ₁ φ₂ : M₁ ⟶ M₂) : (φ₁ - φ₂).hom = φ₁.hom - φ₂.hom := rfl
/--
lemma `hom_nsmul` / 引理 `hom_nsmul`

English:
lemma hom_nsmul
  given: (n : Nat) (φ : M₁ ⟶ M₂)
  statement: (n • φ).hom = n • φ.hom
  proof: rfl

中文:
引理 hom_nsmul
  条件: (n : 自然数) (φ : M₁ ⟶ M₂)
  结论: (n • φ).hom = n • φ.hom
  证明: rfl
-/
@[simp] lemma hom_nsmul (n : Nat) (φ : M₁ ⟶ M₂) : (n • φ).hom = n • φ.hom := rfl
/--
lemma `hom_zsmul` / 引理 `hom_zsmul`

English:
lemma hom_zsmul
  given: (n : Int) (φ : M₁ ⟶ M₂)
  statement: (n • φ).hom = n • φ.hom
  proof: rfl

中文:
引理 hom_zsmul
  条件: (n : 整数) (φ : M₁ ⟶ M₂)
  结论: (n • φ).hom = n • φ.hom
  证明: rfl
-/
@[simp] lemma hom_zsmul (n : Int) (φ : M₁ ⟶ M₂) : (n • φ).hom = n • φ.hom := rfl

end

section CommRing

variable {S : Type*} [CommRing S] [TopologicalSpace S]

instance {X Y : TopModuleCat S} : Module S (X ⟶ Y) where
  smul r f := ofHom (r • f.hom)
  __ := Equiv.module _ CategoryTheory.ConcreteCategory.homEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear S (TopModuleCat S)
  body: ConcreteCategory.ext (ContinuousLinearMap.comp_smul _ _ _)
  comp_smul _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.smul_comp _ _ _)

@[simp]

中文:
实例 :
  签名: Linear S (TopModuleCat S)
  定义体: ConcreteCategory.ext (ContinuousLinearMap.comp_smul _ _ _)
  comp_smul _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.smul_comp _ _ _)

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, ContinuousLinearMap, ContinuousLinearMap.comp_smul, comp_smul
-/
instance : Linear S (TopModuleCat S) where
  smul_comp _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.comp_smul _ _ _)
  comp_smul _ _ _ _ _ _ := ConcreteCategory.ext (ContinuousLinearMap.smul_comp _ _ _)

@[simp]
/--
lemma `hom_smul` / 引理 `hom_smul`

English:
lemma hom_smul
  given: {M₁ M₂ : TopModuleCat S} (s : S) (φ : M₁ ⟶ M₂)
  statement: (s • φ).hom = s • φ.hom
  proof: rfl

中文:
引理 hom_smul
  条件: {M₁ M₂ : TopModuleCat S} (s : S) (φ : M₁ ⟶ M₂)
  结论: (s • φ).hom = s • φ.hom
  证明: rfl

Depends on / 依赖: CommRingCat, CommRingCat.KaehlerDifferential, KaehlerDifferential
-/
lemma hom_smul {M₁ M₂ : TopModuleCat S} (s : S) (φ : M₁ ⟶ M₂) : (s • φ).hom = s • φ.hom := rfl

end CommRing

instance (M : TopModuleCat R) : TopologicalSpace M := M.2
instance (M : TopModuleCat R) : IsTopologicalAddGroup M := M.3

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (TopModuleCat R) (ModuleCat R)
  body: { obj M := ModuleCat.of R M
    map φ := ModuleCat.ofHom φ.hom }

中文:
实例 :
  签名: HasForget₂ (TopModuleCat R) (ModuleCat R)
  定义体: { obj M := ModuleCat.of R M
    map φ := ModuleCat.ofHom φ.hom }

Depends on / 依赖: ModuleCat, ModuleCat.of, ModuleCat.ofHom
-/
instance : HasForget₂ (TopModuleCat R) (ModuleCat R) where
  forget₂ :=
  { obj M := ModuleCat.of R M
    map φ := ModuleCat.ofHom φ.hom }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (TopModuleCat R) TopCat
  body: { obj M := .of M
    map φ := TopCat.ofHom ⟨φ, φ.1.2⟩ }

中文:
实例 :
  签名: HasForget₂ (TopModuleCat R) TopCat
  定义体: { obj M := .of M
    map φ := TopCat.ofHom ⟨φ, φ.1.2⟩ }

Depends on / 依赖: TopCat, TopCat.ofHom
-/
instance : HasForget₂ (TopModuleCat R) TopCat where
  forget₂ :=
  { obj M := .of M
    map φ := TopCat.ofHom ⟨φ, φ.1.2⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (TopModuleCat R) TopCat).ReflectsIsomorphisms
  body: by
    let e : X ≃L[R] Y :=
      { __ := f.hom, __ := TopCat.homeoOfIso (asIso ((forget₂ (TopModuleCat R) TopCat).map f)) }
    change IsIso (ofIso e).hom
    infer_instance

@[simp]

中文:
实例 :
  签名: (forget₂ (TopModuleCat R) TopCat).ReflectsIsomorphisms
  定义体: by
    let e : X ≃L[R] Y :=
      { __ := f.hom, __ := TopCat.homeoOfIso (asIso ((forget₂ (TopModuleCat R) TopCat).map f)) }
    change IsIso (ofIso e).hom
    infer_instance

@[simp]

Depends on / 依赖: TopCat, TopCat.homeoOfIso, TopModuleCat, f.hom, homeoOfIso, infer_instance
-/
instance : (forget₂ (TopModuleCat R) TopCat).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    let e : X ≃L[R] Y :=
      { __ := f.hom, __ := TopCat.homeoOfIso (asIso ((forget₂ (TopModuleCat R) TopCat).map f)) }
    change IsIso (ofIso e).hom
    infer_instance

@[simp]
/--
lemma `hom_forget₂_TopCat_map` / 引理 `hom_forget₂_TopCat_map`

English:
lemma hom_forget₂_TopCat_map
  given: {X Y : TopModuleCat R} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 hom_forget₂_TopCat_map
  条件: {X Y : TopModuleCat R} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma hom_forget₂_TopCat_map {X Y : TopModuleCat R} (f : X ⟶ Y) :
    ((forget₂ _ TopCat).map f).hom = f.hom := rfl

@[simp]
/--
lemma `forget₂_TopCat_obj` / 引理 `forget₂_TopCat_obj`

English:
lemma forget₂_TopCat_obj
  given: {X : TopModuleCat R}
  statement: ((forget₂ _ TopCat).obj X : Type _) = X
  proof: rfl

中文:
引理 forget₂_TopCat_obj
  条件: {X : TopModuleCat R}
  结论: ((forget₂ _ TopCat).obj X : Type _) = X
  证明: rfl
-/
lemma forget₂_TopCat_obj {X : TopModuleCat R} : ((forget₂ _ TopCat).obj X : Type _) = X := rfl

open Limits

section Colimit

variable {R}

variable {M : ModuleCat R} {I : Type*} {X : I -> TopModuleCat R} (f : forall i, (X i).toModuleCat ⟶ M)

/--
Definition of `coinduced` / `coinduced` 的定义

English:
definition coinduced
  signature: : TopModuleCat R
  body: letI : TopologicalSpace M := sInf { t | @ContinuousSMul R M _ _ t ∧ @ContinuousAdd M t _ ∧
      forall i, (X i).topologicalSpace.coinduced (f i) <= t }
  have : ContinuousAdd M := continuousAdd_sInf fun _ hs => hs.2.1
  have : ContinuousSMul R M := continuousSMul_sInf fun _ hs => hs.1
  .of R M

中文:
定义 coinduced
  签名: : TopModuleCat R
  定义体: letI : TopologicalSpace M := sInf { t | @ContinuousSMul R M _ _ t ∧ @ContinuousAdd M t _ ∧
      forall i, (X i).topologicalSpace.coinduced (f i) <= t }
  have : ContinuousAdd M := continuousAdd_sInf fun _ hs => hs.2.1
  have : ContinuousSMul R M := continuousSMul_sInf fun _ hs => hs.1
  .of R M

Depends on / 依赖: ContinuousAdd, ContinuousSMul, TopologicalSpace, coinduced, continuousAdd_sInf, continuousSMul_sInf, topologicalSpace, topologicalSpace.coinduced
-/
def coinduced : TopModuleCat R :=
  letI : TopologicalSpace M := sInf { t | @ContinuousSMul R M _ _ t ∧ @ContinuousAdd M t _ ∧
      forall i, (X i).topologicalSpace.coinduced (f i) <= t }
  have : ContinuousAdd M := continuousAdd_sInf fun _ hs => hs.2.1
  have : ContinuousSMul R M := continuousSMul_sInf fun _ hs => hs.1
  .of R M

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toCoinduced` / `toCoinduced` 的定义

English:
definition toCoinduced
  signature: (i)
  body: ofHom (Y := coinduced f)
    ⟨(f i).hom, continuous_iff_coinduced_le.mpr (le_sInf fun _ hτ => hτ.2.2 i)⟩

中文:
定义 toCoinduced
  签名: (i)
  定义体: ofHom (Y := coinduced f)
    ⟨(f i).hom, continuous_iff_coinduced_le.mpr (le_sInf fun _ hτ => hτ.2.2 i)⟩

Depends on / 依赖: coinduced, continuous_iff_coinduced_le, continuous_iff_coinduced_le.mpr, le_sInf
-/
def toCoinduced (i) : X i ⟶ coinduced f :=
  ofHom (Y := coinduced f)
    ⟨(f i).hom, continuous_iff_coinduced_le.mpr (le_sInf fun _ hτ => hτ.2.2 i)⟩

/--
Definition of `ofCocone` / `ofCocone` 的定义

English:
definition ofCocone
  signature: {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
  body: coinduced c.ι.app
  ι :=
  { app := toCoinduced c.ι.app,
    naturality {X Y} f := by ext x; exact congr($(c.ι.naturality f).hom x) }

中文:
定义 ofCocone
  签名: {J : 类型} [Category* J] {F : J ⥤ TopModuleCat R}
  定义体: coinduced c.ι.app
  ι :=
  { app := toCoinduced c.ι.app,
    naturality {X Y} f := by ext x; exact congr($(c.ι.naturality f).hom x) }

Depends on / 依赖: coinduced
-/
def ofCocone {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
    (c : Cocone (F ⋙ forget₂ _ (ModuleCat R))) : Cocone F where
  pt := coinduced c.ι.app
  ι :=
  { app := toCoinduced c.ι.app,
    naturality {X Y} f := by ext x; exact congr($(c.ι.naturality f).hom x) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
  body: ofHom (X := (ofCocone c).pt) ⟨(hc.desc ((forget₂ _ _).mapCocone s)).hom, by
    rw [continuous_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (M₂ := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom,
      continuousAdd_induced (N := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom, fun i =

中文:
定义 isColimit
  签名: {J : 类型} [Category* J] {F : J ⥤ TopModuleCat R}
  定义体: ofHom (X := (ofCocone c).pt) ⟨(hc.desc ((forget₂ _ _).mapCocone s)).hom, by
    rw [continuous_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (M₂ := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom,
      continuousAdd_induced (N := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom, fun i =

Depends on / 依赖: Continuous, F.obj, ModuleCat, coinduced_le_iff_le_induced, continuousAdd_induced, continuousSMul_induced, continuous_iff_le_induced, hc.desc, hc.f, induced_compose, mapCocone, ofCocone, s.pt, sInf_le
-/
def isColimit {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
    {c : Cocone (F ⋙ forget₂ _ (ModuleCat R))} (hc : IsColimit c) :
    IsColimit (ofCocone c) where
  desc s := ofHom (X := (ofCocone c).pt) ⟨(hc.desc ((forget₂ _ _).mapCocone s)).hom, by
    rw [continuous_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (M₂ := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom,
      continuousAdd_induced (N := s.pt) (hc.desc ((forget₂ _ _).mapCocone s)).hom, fun i => ?_⟩
    rw [coinduced_le_iff_le_induced]; rw [induced_compose]; rw [← continuous_iff_le_induced]
    change Continuous (X := F.obj i) (Y := s.pt)
      (c.ι.app i ≫ hc.desc ((forget₂ _ (ModuleCat R)).mapCocone s)).hom
    rw [hc.fac]
    exact (s.ι.app i).hom.2⟩
  fac s i := by ext x; exact congr($(hc.fac ((forget₂ _ _).mapCocone s) i).hom x)
  uniq s m H := by
    ext x
    refine congr($(hc.uniq ((forget₂ _ _).mapCocone s) ((forget₂ _ _).map m) fun j => ?_).hom x)
    ext y
    exact congr($(H j).hom y)

instance {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
    [HasColimit (F ⋙ forget₂ _ (ModuleCat R))] : HasColimit F :=
  ⟨_, isColimit (colimit.isColimit _)⟩

instance {J : Type*} [Category* J] [HasColimitsOfShape J (ModuleCat.{v} R)] :
    HasColimitsOfShape J (TopModuleCat.{v} R) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits (TopModuleCat.{v} R)

中文:
实例 :
  签名: HasColimits (TopModuleCat.{v} R)
-/
instance : HasColimits (TopModuleCat.{v} R) where

end Colimit

section Limit

variable {R}

variable {M : ModuleCat R} {I : Type*} {X : I -> TopModuleCat R} (f : forall i, M ⟶ (X i).toModuleCat)

/--
Definition of `induced` / `induced` 的定义

English:
definition induced
  signature: : TopModuleCat R
  body: letI : TopologicalSpace M := ⨅ i, (X i).topologicalSpace.induced (f i)
  have : ContinuousAdd M := continuousAdd_iInf fun _ => continuousAdd_induced _
  have : ContinuousSMul R M := continuousSMul_iInf fun _ => continuousSMul_induced _
  .of R M

中文:
定义 induced
  签名: : TopModuleCat R
  定义体: letI : TopologicalSpace M := ⨅ i, (X i).topologicalSpace.induced (f i)
  have : ContinuousAdd M := continuousAdd_iInf fun _ => continuousAdd_induced _
  have : ContinuousSMul R M := continuousSMul_iInf fun _ => continuousSMul_induced _
  .of R M

Depends on / 依赖: ContinuousAdd, ContinuousSMul, TopologicalSpace, continuousAdd_iInf, continuousAdd_induced, continuousSMul_iInf, continuousSMul_induced, induced, topologicalSpace, topologicalSpace.induced
-/
def induced : TopModuleCat R :=
  letI : TopologicalSpace M := ⨅ i, (X i).topologicalSpace.induced (f i)
  have : ContinuousAdd M := continuousAdd_iInf fun _ => continuousAdd_induced _
  have : ContinuousSMul R M := continuousSMul_iInf fun _ => continuousSMul_induced _
  .of R M

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromInduced` / `fromInduced` 的定义

English:
definition fromInduced
  signature: (i)
  body: ofHom (X := induced f) ⟨(f i).hom, continuous_iff_le_induced.mpr (iInf_le _ i)⟩

中文:
定义 fromInduced
  签名: (i)
  定义体: ofHom (X := induced f) ⟨(f i).hom, continuous_iff_le_induced.mpr (iInf_le _ i)⟩

Depends on / 依赖: continuous_iff_le_induced, continuous_iff_le_induced.mpr, iInf_le, induced
-/
def fromInduced (i) : induced f ⟶ X i :=
  ofHom (X := induced f) ⟨(f i).hom, continuous_iff_le_induced.mpr (iInf_le _ i)⟩

open Limits

/--
Definition of `ofCone` / `ofCone` 的定义

English:
definition ofCone
  signature: {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
  body: induced c.π.app
  π :=
  { app := fromInduced c.π.app,
    naturality {X Y} f := by ext x; exact congr($(c.π.naturality f).hom x) }

中文:
定义 ofCone
  签名: {J : 类型} [Category* J] {F : J ⥤ TopModuleCat R}
  定义体: induced c.π.app
  π :=
  { app := fromInduced c.π.app,
    naturality {X Y} f := by ext x; exact congr($(c.π.naturality f).hom x) }

Depends on / 依赖: induced
-/
def ofCone {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
    (c : Cone (F ⋙ forget₂ _ (ModuleCat R))) : Cone F where
  pt := induced c.π.app
  π :=
  { app := fromInduced c.π.app,
    naturality {X Y} f := by ext x; exact congr($(c.π.naturality f).hom x) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimit` / `isLimit` 的定义

English:
definition isLimit
  signature: {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
  body: ofHom (Y := (ofCone c).pt) ⟨(hc.lift ((forget₂ _ _).mapCone s)).hom, by
    rw [continuous_iff_coinduced_le]
    refine le_iInf fun i => ?_
    rw [coinduced_le_iff_le_induced]; rw [induced_compose]; rw [← continuous_iff_le_induced]
    change Continuous (X := s.pt) (Y := F.obj i)
      (hc.lift ((f

中文:
定义 isLimit
  签名: {J : 类型} [Category* J] {F : J ⥤ TopModuleCat R}
  定义体: ofHom (Y := (ofCone c).pt) ⟨(hc.lift ((forget₂ _ _).mapCone s)).hom, by
    rw [continuous_iff_coinduced_le]
    refine le_iInf fun i => ?_
    rw [coinduced_le_iff_le_induced]; rw [induced_compose]; rw [← continuous_iff_le_induced]
    change Continuous (X := s.pt) (Y := F.obj i)
      (hc.lift ((f

Depends on / 依赖: Continuous, F.obj, ModuleCat, coinduced_le_iff_le_induced, continuous_iff_coinduced_le, continuous_iff_le_induced, hc.fac, hc.lift, hc.uniq, induced_compose, le_iInf, mapCone, ofCone, s.pt
-/
def isLimit {J : Type*} [Category* J] {F : J ⥤ TopModuleCat R}
    {c : Cone (F ⋙ forget₂ _ (ModuleCat R))} (hc : IsLimit c) :
    IsLimit (ofCone c) where
  lift s := ofHom (Y := (ofCone c).pt) ⟨(hc.lift ((forget₂ _ _).mapCone s)).hom, by
    rw [continuous_iff_coinduced_le]
    refine le_iInf fun i => ?_
    rw [coinduced_le_iff_le_induced]; rw [induced_compose]; rw [← continuous_iff_le_induced]
    change Continuous (X := s.pt) (Y := F.obj i)
      (hc.lift ((forget₂ _ (ModuleCat R)).mapCone s) ≫ c.π.app i).hom
    rw [hc.fac]
    exact (s.π.app i).hom.2⟩
  fac s i := by ext x; exact congr($(hc.fac ((forget₂ _ _).mapCone s) i).hom x)
  uniq s m H := by
    ext x
    refine congr($(hc.uniq ((forget₂ _ _).mapCone s) ((forget₂ _ _).map m) fun j => ?_).hom x)
    ext y
    exact congr($(H j).hom y)

/--
Instance `hasLimit_of_hasLimit_forget₂` / 实例 `hasLimit_of_hasLimit_forget₂`

English:
instance hasLimit_of_hasLimit_forget₂
  signature: {J : Type*} [Category* J] {F : J ⥤ TopModuleCat.{v} R}
  body: ⟨_, isLimit (limit.isLimit _)⟩

中文:
实例 hasLimit_of_hasLimit_forget₂
  签名: {J : 类型} [Category* J] {F : J ⥤ TopModuleCat.{v} R}
  定义体: ⟨_, isLimit (limit.isLimit _)⟩

Depends on / 依赖: isLimit, limit.isLimit
-/
instance hasLimit_of_hasLimit_forget₂ {J : Type*} [Category* J] {F : J ⥤ TopModuleCat.{v} R}
    [HasLimit (F ⋙ forget₂ _ (ModuleCat.{v} R))] : HasLimit F :=
  ⟨_, isLimit (limit.isLimit _)⟩

instance {J : Type*} [Category* J] [HasLimitsOfShape J (ModuleCat.{v} R)] :
    HasLimitsOfShape J (TopModuleCat.{v} R) where
  has_limit _ := hasLimit_of_hasLimit_forget₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits (TopModuleCat.{v} R)
  body: ⟨fun _ => hasLimit_of_hasLimit_forget₂⟩

中文:
实例 :
  签名: HasLimits (TopModuleCat.{v} R)
  定义体: ⟨fun _ => hasLimit_of_hasLimit_forget₂⟩
-/
instance : HasLimits (TopModuleCat.{v} R) where
  has_limits_of_shape _ _ := ⟨fun _ => hasLimit_of_hasLimit_forget₂⟩

instance {J : Type*} [Category* J] {F : J ⥤ TopModuleCat.{v} R}
    [HasLimit (F ⋙ forget₂ _ (ModuleCat.{v} R))]
    [PreservesLimit (F ⋙ forget₂ _ (ModuleCat.{v} R)) (forget _)] :
    PreservesLimit F (forget₂ _ TopCat) :=
  preservesLimit_of_preserves_limit_cone (isLimit (limit.isLimit _))
    (TopCat.isLimitConeOfForget (F := F ⋙ forget₂ _ TopCat)
      ((forget _).mapCone (getLimitCone (F ⋙ forget₂ _ (ModuleCat.{v} R))).1 :)
      (isLimitOfPreserves (forget (ModuleCat R)) (limit.isLimit _)))

instance {J : Type*} [Category* J]
    [HasLimitsOfShape J (ModuleCat.{v} R)]
    [PreservesLimitsOfShape J (forget (ModuleCat.{v} R))] :
    PreservesLimitsOfShape J (forget₂ (TopModuleCat.{v} R) TopCat) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimits (forget₂ (TopModuleCat.{v} R) TopCat.{v})

中文:
实例 :
  签名: PreservesLimits (forget₂ (TopModuleCat.{v} R) TopCat.{v})
-/
instance : PreservesLimits (forget₂ (TopModuleCat.{v} R) TopCat.{v}) where

end Limit

section Adjunction

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `withModuleTopology` / `withModuleTopology` 的定义

English:
definition withModuleTopology
  signature: : ModuleCat R ⥤ TopModuleCat R where
  body: letI := moduleTopology R X
    letI := IsModuleTopology.topologicalAddGroup R X
    .of R X
  map {X Y} f :=
    letI := moduleTopology R X
    letI := moduleTopology R Y
    letI := IsModuleTopology.topologicalAddGroup R Y
    ⟨f.hom, IsModuleTopology.continuous_of_linearMap f.hom⟩

中文:
定义 withModuleTopology
  签名: : ModuleCat R ⥤ TopModuleCat R where
  定义体: letI := moduleTopology R X
    letI := IsModuleTopology.topologicalAddGroup R X
    .of R X
  map {X Y} f :=
    letI := moduleTopology R X
    letI := moduleTopology R Y
    letI := IsModuleTopology.topologicalAddGroup R Y
    ⟨f.hom, IsModuleTopology.continuous_of_linearMap f.hom⟩

Depends on / 依赖: IsModuleTopology, IsModuleTopology.continuous_of_linearMap, IsModuleTopology.topologicalAddGroup, continuous_of_linearMap, f.hom, moduleTopology, topologicalAddGroup
-/
def withModuleTopology : ModuleCat R ⥤ TopModuleCat R where
  obj X :=
    letI := moduleTopology R X
    letI := IsModuleTopology.topologicalAddGroup R X
    .of R X
  map {X Y} f :=
    letI := moduleTopology R X
    letI := moduleTopology R Y
    letI := IsModuleTopology.topologicalAddGroup R Y
    ⟨f.hom, IsModuleTopology.continuous_of_linearMap f.hom⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `withModuleTopologyAdj` / `withModuleTopologyAdj` 的定义

English:
definition withModuleTopologyAdj
  signature: : withModuleTopology R ⊣ forget₂ (TopModuleCat R) (ModuleCat R) where
  body: 𝟙 _
  counit :=
  { app X := ofHom (X := (withModuleTopology R).obj (.of R X))
      ⟨.id, IsModuleTopology.continuous_of_linearMap _⟩ }

中文:
定义 withModuleTopologyAdj
  签名: : withModuleTopology R ⊣ forget₂ (TopModuleCat R) (ModuleCat R) where
  定义体: 𝟙 _
  counit :=
  { app X := ofHom (X := (withModuleTopology R).obj (.of R X))
      ⟨.id, IsModuleTopology.continuous_of_linearMap _⟩ }
-/
def withModuleTopologyAdj : withModuleTopology R ⊣ forget₂ (TopModuleCat R) (ModuleCat R) where
  unit := 𝟙 _
  counit :=
  { app X := ofHom (X := (withModuleTopology R).obj (.of R X))
      ⟨.id, IsModuleTopology.continuous_of_linearMap _⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (TopModuleCat R) (ModuleCat R)).IsRightAdjoint
  body: ⟨_, ⟨withModuleTopologyAdj R⟩⟩

中文:
实例 :
  签名: (forget₂ (TopModuleCat R) (ModuleCat R)).IsRightAdjoint
  定义体: ⟨_, ⟨withModuleTopologyAdj R⟩⟩

Depends on / 依赖: withModuleTopologyAdj
-/
instance : (forget₂ (TopModuleCat R) (ModuleCat R)).IsRightAdjoint := ⟨_, ⟨withModuleTopologyAdj R⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (withModuleTopology R).IsLeftAdjoint
  body: ⟨_, ⟨withModuleTopologyAdj R⟩⟩

中文:
实例 :
  签名: (withModuleTopology R).IsLeftAdjoint
  定义体: ⟨_, ⟨withModuleTopologyAdj R⟩⟩

Depends on / 依赖: withModuleTopologyAdj
-/
instance : (withModuleTopology R).IsLeftAdjoint := ⟨_, ⟨withModuleTopologyAdj R⟩⟩

/--
Definition of `indiscrete` / `indiscrete` 的定义

English:
definition indiscrete
  signature: : ModuleCat.{v} R ⥤ TopModuleCat.{v} R where
  body: letI : TopologicalSpace X := ⊤
    haveI : ContinuousAdd X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    haveI : ContinuousSMul R X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    .of R X
  map {X Y} f :=
    letI : TopologicalSpace X := ⊤
    letI : TopologicalSpace Y := ⊤
 

中文:
定义 indiscrete
  签名: : ModuleCat.{v} R ⥤ TopModuleCat.{v} R where
  定义体: letI : TopologicalSpace X := ⊤
    haveI : ContinuousAdd X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    haveI : ContinuousSMul R X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    .of R X
  map {X Y} f :=
    letI : TopologicalSpace X := ⊤
    letI : TopologicalSpace Y := ⊤
 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, ContinuousAdd, ContinuousSMul, TopModuleCat, TopologicalSpace, continuous_iff_coinduced_le, f.hom, le_top
-/
def indiscrete : ModuleCat.{v} R ⥤ TopModuleCat.{v} R where
  obj X :=
    letI : TopologicalSpace X := ⊤
    haveI : ContinuousAdd X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    haveI : ContinuousSMul R X := ⟨by rw [continuous_iff_coinduced_le]; exact le_top⟩
    .of R X
  map {X Y} f :=
    letI : TopologicalSpace X := ⊤
    letI : TopologicalSpace Y := ⊤
    ConcreteCategory.ofHom (C := TopModuleCat R)
      ⟨f.hom, by rw [continuous_iff_coinduced_le]; exact le_top⟩

/--
Definition of `indiscreteAdj` / `indiscreteAdj` 的定义

English:
definition indiscreteAdj
  signature: : forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R) ⊣ indiscrete.{v} R where
  body: 𝟙 _
  unit := { app X := ConcreteCategory.ofHom (C := TopModuleCat R)
              ⟨.id, by rw [continuous_iff_coinduced_le]; exact le_top⟩ }

中文:
定义 indiscreteAdj
  签名: : forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R) ⊣ indiscrete.{v} R where
  定义体: 𝟙 _
  unit := { app X := ConcreteCategory.ofHom (C := TopModuleCat R)
              ⟨.id, by rw [continuous_iff_coinduced_le]; exact le_top⟩ }
-/
def indiscreteAdj : forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R) ⊣ indiscrete.{v} R where
  counit := 𝟙 _
  unit := { app X := ConcreteCategory.ofHom (C := TopModuleCat R)
              ⟨.id, by rw [continuous_iff_coinduced_le]; exact le_top⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).IsLeftAdjoint
  body: ⟨_, ⟨indiscreteAdj R⟩⟩

中文:
实例 :
  签名: (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).IsLeftAdjoint
  定义体: ⟨_, ⟨indiscreteAdj R⟩⟩

Depends on / 依赖: indiscreteAdj
-/
instance : (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).IsLeftAdjoint := ⟨_, ⟨indiscreteAdj R⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (indiscrete.{v} R).IsRightAdjoint
  body: ⟨_, ⟨indiscreteAdj R⟩⟩

中文:
实例 :
  签名: (indiscrete.{v} R).IsRightAdjoint
  定义体: ⟨_, ⟨indiscreteAdj R⟩⟩

Depends on / 依赖: indiscreteAdj
-/
instance : (indiscrete.{v} R).IsRightAdjoint := ⟨_, ⟨indiscreteAdj R⟩⟩

/-- The free topological module over a topological space. -/
noncomputable
/--
Definition of `freeObj` / `freeObj` 的定义

English:
definition freeObj
  signature: (X : TopCat.{v})
  body: letI : TopologicalSpace (X ->₀ R) := sInf
    { t | @ContinuousSMul R _ _ _ t ∧ @ContinuousAdd _ t _ ∧
      X.str.coinduced (Finsupp.single · 1) <= t }
  letI : ContinuousAdd (X ->₀ R) := continuousAdd_sInf fun _ h => h.2.1
  letI : ContinuousSMul R (X ->₀ R) := continuousSMul_sInf fun _ h => h.1
 

中文:
定义 freeObj
  签名: (X : TopCat.{v})
  定义体: letI : TopologicalSpace (X ->₀ R) := sInf
    { t | @ContinuousSMul R _ _ _ t ∧ @ContinuousAdd _ t _ ∧
      X.str.coinduced (Finsupp.single · 1) <= t }
  letI : ContinuousAdd (X ->₀ R) := continuousAdd_sInf fun _ h => h.2.1
  letI : ContinuousSMul R (X ->₀ R) := continuousSMul_sInf fun _ h => h.1
 

Depends on / 依赖: ContinuousAdd, ContinuousSMul, Finsupp, Finsupp.single, TopologicalSpace, X.str.coinduced, coinduced, continuousAdd_sInf, continuousSMul_sInf, single
-/
def freeObj (X : TopCat.{v}) : TopModuleCat.{max v u} R :=
  letI : TopologicalSpace (X ->₀ R) := sInf
    { t | @ContinuousSMul R _ _ _ t ∧ @ContinuousAdd _ t _ ∧
      X.str.coinduced (Finsupp.single · 1) <= t }
  letI : ContinuousAdd (X ->₀ R) := continuousAdd_sInf fun _ h => h.2.1
  letI : ContinuousSMul R (X ->₀ R) := continuousSMul_sInf fun _ h => h.1
  of R (X ->₀ R)

/--
lemma `coe_freeObj` / 引理 `coe_freeObj`

English:
lemma coe_freeObj
  given: (X : TopCat.{v})
  statement: freeObj R X = (X ->₀ R)
  proof: rfl

中文:
引理 coe_freeObj
  条件: (X : TopCat.{v})
  结论: freeObj R X = (X ->₀ R)
  证明: rfl
-/
lemma coe_freeObj (X : TopCat.{v}) : freeObj R X = (X ->₀ R) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The free topological module over a topological space is functorial. -/
noncomputable
/--
Definition of `freeMap` / `freeMap` 的定义

English:
definition freeMap
  signature: {X Y : TopCat.{v}} (f : X ⟶ Y)
  body: ConcreteCategory.ofHom ⟨Finsupp.lmapDomain _ _ f.hom, by
    rw [continuous_iff_coinduced_le]
    refine le_sInf fun (τ : TopologicalSpace (_ ->₀ R)) ⟨hτ₁, hτ₂, hτ₃⟩ => ?_
    rw [coinduced_le_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (Finsupp.lmapDomain _ _ f.hom),
      continuous

中文:
定义 freeMap
  签名: {X Y : TopCat.{v}} (f : X ⟶ Y)
  定义体: ConcreteCategory.ofHom ⟨Finsupp.lmapDomain _ _ f.hom, by
    rw [continuous_iff_coinduced_le]
    refine le_sInf fun (τ : TopologicalSpace (_ ->₀ R)) ⟨hτ₁, hτ₂, hτ₃⟩ => ?_
    rw [coinduced_le_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (Finsupp.lmapDomain _ _ f.hom),
      continuous

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Finsupp, Finsupp.lmapDomain, TopologicalSpace, coinduced_compose, coinduced_le_iff_le_induced, coinduced_mono, continuousAdd_induced, continuousSMul_induced, continuous_iff_coinduced_le, continuous_iff_coinduced_le.mp, f.hom, le_sInf, lmapDomain, sInf_le
-/
def freeMap {X Y : TopCat.{v}} (f : X ⟶ Y) : freeObj R X ⟶ freeObj R Y :=
  ConcreteCategory.ofHom ⟨Finsupp.lmapDomain _ _ f.hom, by
    rw [continuous_iff_coinduced_le]
    refine le_sInf fun (τ : TopologicalSpace (_ ->₀ R)) ⟨hτ₁, hτ₂, hτ₃⟩ => ?_
    rw [coinduced_le_iff_le_induced]
    refine sInf_le ⟨continuousSMul_induced (Finsupp.lmapDomain _ _ f.hom),
      continuousAdd_induced (Finsupp.lmapDomain _ _ f.hom), ?_⟩
    rw [← coinduced_le_iff_le_induced]
    grw [← hτ₃, ← coinduced_mono (continuous_iff_coinduced_le.mp f.hom.2)]
    rw [coinduced_compose]; rw [coinduced_compose]
    congr! 1
    ext x
    simp [coe_freeObj]⟩

/--
lemma `freeMap_map` / 引理 `freeMap_map`

English:
lemma freeMap_map
  given: {X Y : TopCat.{v}} (f : X ⟶ Y) (v : X ->₀ R)
  proof: rfl

中文:
引理 freeMap_map
  条件: {X Y : TopCat.{v}} (f : X ⟶ Y) (v : X ->₀ R)
  证明: rfl
-/
lemma freeMap_map {X Y : TopCat.{v}} (f : X ⟶ Y) (v : X ->₀ R) :
    (freeMap R f : (X ->₀ R) -> (Y ->₀ R)) v = Finsupp.mapDomain f.hom v := rfl

/-- The free topological module over a topological space as a functor.
This is left adjoint to the forgetful functor. -/
@[simps] noncomputable
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : TopCat.{v} ⥤ TopModuleCat.{max v u} R
  body: { obj := freeObj R
    map f := freeMap R f
    map_id M := by ext x; exact DFunLike.congr_fun (Finsupp.lmapDomain_id _ _) x
    map_comp f g := by ext; exact DFunLike.congr_fun (Finsupp.lmapDomain_comp _ _ f.hom g.hom) _ }

中文:
定义 free
  签名: : TopCat.{v} ⥤ TopModuleCat.{max v u} R
  定义体: { obj := freeObj R
    map f := freeMap R f
    map_id M := by ext x; exact DFunLike.congr_fun (Finsupp.lmapDomain_id _ _) x
    map_comp f g := by ext; exact DFunLike.congr_fun (Finsupp.lmapDomain_comp _ _ f.hom g.hom) _ }

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Finsupp, Finsupp.lmapDomain_comp, Finsupp.lmapDomain_id, congr_fun, f.hom, freeMap, freeObj, g.hom, lmapDomain_comp, lmapDomain_id, map_comp, map_id
-/
def free : TopCat.{v} ⥤ TopModuleCat.{max v u} R :=
  { obj := freeObj R
    map f := freeMap R f
    map_id M := by ext x; exact DFunLike.congr_fun (Finsupp.lmapDomain_id _ _) x
    map_comp f g := by ext; exact DFunLike.congr_fun (Finsupp.lmapDomain_comp _ _ f.hom g.hom) _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free-forgetful adjoint for `TopModuleCat R`. -/
noncomputable
/--
Definition of `freeAdj` / `freeAdj` 的定义

English:
definition freeAdj
  signature: : free.{max v u} R ⊣ forget₂ (TopModuleCat.{max v u} R) TopCat.{max v u} where
  body: { app X := TopCat.ofHom ⟨(Finsupp.single · 1),
      continuous_iff_coinduced_le.mpr (le_sInf fun _ h => h.2.2)⟩,
    naturality {X Y} f := by ext x; simp [freeMap_map] }
  counit :=
  { app X := ConcreteCategory.ofHom (C := TopModuleCat R) ⟨Finsupp.lift _ R X id, by
      rw [continuous_iff_le_indu

中文:
定义 freeAdj
  签名: : free.{max v u} R ⊣ forget₂ (TopModuleCat.{max v u} R) TopCat.{max v u} where
  定义体: { app X := TopCat.ofHom ⟨(Finsupp.single · 1),
      continuous_iff_coinduced_le.mpr (le_sInf fun _ h => h.2.2)⟩,
    naturality {X Y} f := by ext x; simp [freeMap_map] }
  counit :=
  { app X := ConcreteCategory.ofHom (C := TopModuleCat R) ⟨Finsupp.lift _ R X id, by
      rw [continuous_iff_le_indu

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, Finsupp, Finsupp.lift, Finsupp.single, TopCat, TopCat.ofHom, TopModuleCat, coe_fre, coinduced_le_iff_le_induced, continuousAdd_induced, continuousSMul_induced, continuous_iff_coinduced_le, continuous_iff_coinduced_le.mpr, continuous_iff_le_induced, convert, counit, freeMap_map, induced_compose, induced_id
-/
def freeAdj : free.{max v u} R ⊣ forget₂ (TopModuleCat.{max v u} R) TopCat.{max v u} where
  unit :=
  { app X := TopCat.ofHom ⟨(Finsupp.single · 1),
      continuous_iff_coinduced_le.mpr (le_sInf fun _ h => h.2.2)⟩,
    naturality {X Y} f := by ext x; simp [freeMap_map] }
  counit :=
  { app X := ConcreteCategory.ofHom (C := TopModuleCat R) ⟨Finsupp.lift _ R X id, by
      rw [continuous_iff_le_induced]
      refine sInf_le ⟨continuousSMul_induced (Finsupp.lift _ R X id),
        continuousAdd_induced (Finsupp.lift _ R X id), ?_⟩
      rw [coinduced_le_iff_le_induced]; rw [induced_compose]
      convert! induced_id.symm.le
      ext
      simp [coe_freeObj]⟩,
    naturality {X Y} f := by
      ext1
      apply ContinuousLinearMap.coe_injective
      refine Finsupp.lhom_ext' fun a => LinearMap.ext_ring ?_
      dsimp [freeObj, freeMap]
      simp }
  left_triangle_components X := by
    ext1
    apply ContinuousLinearMap.coe_injective
    refine Finsupp.lhom_ext' fun a => LinearMap.ext_ring ?_
    simp [freeMap, freeObj]
  right_triangle_components X := by
    ext
    simp [freeObj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (TopModuleCat.{max v u} R) TopCat).IsRightAdjoint
  body: ⟨_, ⟨freeAdj R⟩⟩

中文:
实例 :
  签名: (forget₂ (TopModuleCat.{max v u} R) TopCat).IsRightAdjoint
  定义体: ⟨_, ⟨freeAdj R⟩⟩

Depends on / 依赖: freeAdj
-/
instance : (forget₂ (TopModuleCat.{max v u} R) TopCat).IsRightAdjoint := ⟨_, ⟨freeAdj R⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (free.{max v u} R).IsLeftAdjoint
  body: ⟨_, ⟨freeAdj R⟩⟩

中文:
实例 :
  签名: (free.{max v u} R).IsLeftAdjoint
  定义体: ⟨_, ⟨freeAdj R⟩⟩

Depends on / 依赖: freeAdj
-/
instance : (free.{max v u} R).IsLeftAdjoint := ⟨_, ⟨freeAdj R⟩⟩

end Adjunction

variable {R} in
/-- The ring isomorphism between the endomorphisms of an object `M` in `TopModuleCat R` and the
continuous `R`-linear endomorphisms of `M`. -/
@[simps]
/--
Definition of `endRingEquiv` / `endRingEquiv` 的定义

English:
definition endRingEquiv
  signature: (M : TopModuleCat R)
  body: TopModuleCat.Hom.hom
  invFun := TopModuleCat.ofHom
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 endRingEquiv
  签名: (M : TopModuleCat R)
  定义体: TopModuleCat.Hom.hom
  invFun := TopModuleCat.ofHom
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: TopModuleCat, TopModuleCat.Hom.hom
-/
def endRingEquiv (M : TopModuleCat R) :
    End M ≃+* (M ->L[R] M) where
  toFun := TopModuleCat.Hom.hom
  invFun := TopModuleCat.ofHom
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end TopModuleCat
