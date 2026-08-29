/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic

/-!
# The presheaf of differentials of a presheaf of modules

In this file, we define the type `M.Derivation φ` of derivations
with values in a presheaf of `R`-modules `M` relative to
a morphism of `φ : S ⟶ F.op ⋙ R` of presheaves of commutative rings
over categories `C` and `D` that are related by a functor `F : C ⥤ D`.
We formalize the notion of universal derivation.

Geometrically, if `f : X ⟶ S` is a morphism of schemes (or more generally
a morphism of commutative ringed spaces), we would like to apply
these definitions in the case where `F` is the pullback functor from
open subsets of `S` to open subsets of `X` and `φ` is the
morphism $O_S ⟶ f_* O_X$.

In order to prove that there exists a universal derivation, the target
of which shall be called the presheaf of relative differentials of `φ`,
we first study the case where `F` is the identity functor.
In this case where we have a morphism of presheaves of commutative
rings `φ' : S' ⟶ R`, we construct a derivation
`DifferentialsConstruction.derivation'` which is universal.
Then, the general case (TODO) shall be obtained by observing that
derivations for `S ⟶ F.op ⋙ R` identify to derivations
for `S' ⟶ R` where `S'` is the pullback by `F` of the presheaf of
commutative rings `S` (the data is the same: it suffices
to show that the two vanishing conditions `d_app` are equivalent).

-/

@[expose] public section

universe v u v₁ v₂ u₁ u₂

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ F.op ⋙ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
@[ext]
/--
Definition of `Derivation` / `Derivation` 的定义

English:
structure Derivation
  parameters: where
  axioms and operations (4):
    - d({X : Dᵒᵖ}) : R.obj X ->+ M.obj X
    - d_mul({X : Dᵒᵖ} (a b : R.obj X)) : d (a * b) = a • d b + b • d a  [default: by cat_disch]
    - d_map({X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X)) : d (R.map f x) = M.map f (d x)  [default: by cat_disch]
    - d_app({X : Cᵒᵖ} (a : S.obj X)) : d (φ.app X a) = 0  [default: by cat_disch]

中文:
结构 导子
  参数: where
  公理与运算 (4 个):
    - d({X : Dᵒᵖ}) : R.obj X ->+ M.obj X
    - d_mul({X : Dᵒᵖ} (a b : R.obj X)) : d (a * b) = a • d b + b • d a  [默认: by cat_disch]
    - d_map({X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X)) : d (R.map f x) = M.map f (d x)  [默认: by cat_disch]
    - d_app({X : Cᵒᵖ} (a : S.obj X)) : d (φ.app X a) = 0  [默认: by cat_disch]

Depends on / 依赖: M.map, R.map, R.obj, S.obj, cat_disch, d_app, d_map
-/
structure Derivation where
  /-- the underlying additive map `R.obj X →+ M.obj X` of a derivation -/
  d {X : Dᵒᵖ} : R.obj X ->+ M.obj X
  d_mul {X : Dᵒᵖ} (a b : R.obj X) : d (a * b) = a • d b + b • d a := by cat_disch
  d_map {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    d (R.map f x) = M.map f (d x) := by cat_disch
  d_app {X : Cᵒᵖ} (a : S.obj X) : d (φ.app X a) = 0 := by cat_disch

namespace Derivation

-- Note: `d_app` cannot be a simp lemma because `dsimp` would
-- simplify the composition of functors `R ⋙ forget₂ _ _`
attribute [simp] d_mul d_map

variable {M N φ}

/--
lemma `congr_d` / 引理 `congr_d`

English:
lemma congr_d
  given: {d d' : M.Derivation φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X)
  proof: by rw [h]

中文:
引理 congr_d
  条件: {d d' : M.导子 φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X)
  证明: by rw [h]
-/
lemma congr_d {d d' : M.Derivation φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X) :
    d.d b = d'.d b := by rw [h]

variable (d : M.Derivation φ)

/--
lemma `d_one` / 引理 `d_one`

English:
lemma d_one
  given: (X : Dᵒᵖ)
  statement: d.d (X := X) 1 = 0
  proof: by
  simpa using d.d_mul (X := X) 1 1

中文:
引理 d_one
  条件: (X : Dᵒᵖ)
  结论: d.d (X := X) 1 = 0
  证明: by
  simpa using d.d_mul (X := X) 1 1
-/
@[simp] lemma d_one (X : Dᵒᵖ) : d.d (X := X) 1 = 0 := by
  simpa using d.d_mul (X := X) 1 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The postcomposition of a derivation by a morphism of presheaves of modules. -/
@[simps! d_apply]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: (f : M ⟶ N)
  body: (f.app _).hom.toAddMonoidHom.comp d.d
  d_map {X Y} g x := by simpa using naturality_apply f g (d.d x)
  d_app {X} a := by
    dsimp
    erw [d_app]
    rw [map_zero]

中文:
定义 postcomp
  签名: (f : M ⟶ N)
  定义体: (f.app _).hom.toAddMonoidHom.comp d.d
  d_map {X Y} g x := by simpa using naturality_apply f g (d.d x)
  d_app {X} a := by
    dsimp
    erw [d_app]
    rw [map_zero]

Depends on / 依赖: f.app, hom.toAddMonoidHom.comp, toAddMonoidHom
-/
def postcomp (f : M ⟶ N) : N.Derivation φ where
  d := (f.app _).hom.toAddMonoidHom.comp d.d
  d_map {X Y} g x := by simpa using naturality_apply f g (d.d x)
  d_app {X} a := by
    dsimp
    erw [d_app]
    rw [map_zero]

/--
Definition of `Universal` / `Universal` 的定义

English:
structure Universal
  parameters: where
  axioms and operations (3):
    - desc({M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)} (d' : M'.Derivation φ)) : M ⟶ M'
    - fac({M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)} (d' : M'.Derivation φ)) : d.postcomp (desc d') = d'  [default: by cat_disch]
    - postcomp_injective({M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)} (φ φ' : M ⟶ M') (h : d.postcomp φ = d.postcomp φ')) : φ = φ'  [default: by cat_disch]

中文:
结构 泛
  参数: where
  公理与运算 (3 个):
    - desc({M' : 预模层 (R ⋙ forget₂ 交换环范畴 环范畴)} (d' : M'.导子 φ)) : M ⟶ M'
    - fac({M' : 预模层 (R ⋙ forget₂ 交换环范畴 环范畴)} (d' : M'.导子 φ)) : d.postcomp (desc d') = d'  [默认: by cat_disch]
    - postcomp_injective({M' : 预模层 (R ⋙ forget₂ 交换环范畴 环范畴)} (φ φ' : M ⟶ M') (h : d.postcomp φ = d.postcomp φ')) : φ = φ'  [默认: by cat_disch]

Depends on / 依赖: CommRingCat, PresheafOfModules, RingCat, cat_disch, d.postcomp, postcomp, postcomp_injective
-/
structure Universal where
  /-- An absolute derivation of `M'` descends as a morphism `M ⟶ M'`. -/
  desc {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : M ⟶ M'
  fac {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : d.postcomp (desc d') = d' := by cat_disch
  postcomp_injective {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (φ φ' : M ⟶ M') (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by cat_disch

attribute [simp] Universal.fac

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton d.Universal
  body: by
    suffices forall {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
      (d' : M'.Derivation φ), h₁.desc d' = h₂.desc d' by
        cases h₁
        cases h₂
        simp only [Universal.mk.injEq]
        ext : 2
        apply this
    intro M' d'
    apply h₁.postcomp_injective
    s

中文:
实例 :
  签名: 子单例 d.泛
  定义体: by
    suffices forall {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
      (d' : M'.Derivation φ), h₁.desc d' = h₂.desc d' by
        cases h₁
        cases h₂
        simp only [Universal.mk.injEq]
        ext : 2
        apply this
    intro M' d'
    apply h₁.postcomp_injective
    s

Depends on / 依赖: CommRingCat, Derivation, PresheafOfModules, RingCat, Universal, Universal.mk.injEq, postcomp_injective
-/
instance : Subsingleton d.Universal where
  allEq h₁ h₂ := by
    suffices forall {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
      (d' : M'.Derivation φ), h₁.desc d' = h₂.desc d' by
        cases h₁
        cases h₂
        simp only [Universal.mk.injEq]
        ext : 2
        apply this
    intro M' d'
    apply h₁.postcomp_injective
    simp

end Derivation

/--
Definition of `HasDifferentials` / `HasDifferentials` 的定义

English:
class HasDifferentials
  parameters: : Prop where
  axioms and operations (1):
    - exists_universal_derivation : exists (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (d : M.Derivation φ), Nonempty d.Universal

中文:
类 有Differentials
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_universal_derivation : 存在 (M : 预模层.{u} (R ⋙ forget₂ _ _)) (d : M.导子 φ), 非空 d.泛
-/
class HasDifferentials : Prop where
  exists_universal_derivation : exists (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
      (d : M.Derivation φ), Nonempty d.Universal

/--
Definition of `Derivation'` / `Derivation'` 的定义

English:
abbreviation Derivation'
  signature: : Type _
  body: M.Derivation (F := 𝟭 D) φ'

中文:
缩写 导子'
  签名: : 类型 _
  定义体: M.Derivation (F := 𝟭 D) φ'

Depends on / 依赖: Derivation, M.Derivation
-/
abbrev Derivation' : Type _ := M.Derivation (F := 𝟭 D) φ'

namespace Derivation'

variable {M φ'}

@[simp]
/--
lemma `d_app` / 引理 `d_app`

English:
lemma d_app
  given: (d : M.Derivation' φ') {X : Dᵒᵖ} (a : S'.obj X)
  proof: Derivation.d_app d _

中文:
引理 d_app
  条件: (d : M.导子' φ') {X : Dᵒᵖ} (a : S'.obj X)
  证明: Derivation.d_app d _

Depends on / 依赖: Derivation, Derivation.d_app, d_app
-/
lemma d_app (d : M.Derivation' φ') {X : Dᵒᵖ} (a : S'.obj X) :
    d.d (φ'.app X a) = 0 :=
  Derivation.d_app d _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `app` / `app` 的定义

English:
definition app
  signature: (d : M.Derivation' φ') (X : Dᵒᵖ)
  body: ModuleCat.Derivation.mk (fun b => d.d b)

@[simp]

中文:
定义 app
  签名: (d : M.导子' φ') (X : Dᵒᵖ)
  定义体: ModuleCat.Derivation.mk (fun b => d.d b)

@[simp]

Depends on / 依赖: Derivation, ModuleCat, ModuleCat.Derivation.mk
-/
noncomputable def app (d : M.Derivation' φ') (X : Dᵒᵖ) : (M.obj X).Derivation (φ'.app X) :=
  ModuleCat.Derivation.mk (fun b => d.d b)

@[simp]
/--
lemma `app_apply` / 引理 `app_apply`

English:
lemma app_apply
  given: (d : M.Derivation' φ') {X : Dᵒᵖ} (b : R.obj X)
  proof: rfl

中文:
引理 app_apply
  条件: (d : M.导子' φ') {X : Dᵒᵖ} (b : R.obj X)
  证明: rfl
-/
lemma app_apply (d : M.Derivation' φ') {X : Dᵒᵖ} (b : R.obj X) :
    (d.app X).d b = d.d b := rfl

section

variable (d : forall (X : Dᵒᵖ), (M.obj X).Derivation (φ'.app X))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (d_map : forall ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
  body: AddMonoidHom.mk' (d X).d (by simp)

中文:
定义 mk
  签名: (d_map : 对任意 ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
  定义体: AddMonoidHom.mk' (d X).d (by simp)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk
-/
def mk (d_map : forall ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
    (d Y).d ((R.map f) x) = (M.map f) ((d X).d x)) : M.Derivation' φ' where
  d {X} := AddMonoidHom.mk' (d X).d (by simp)

variable (d_map : forall ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
      (d Y).d ((R.map f) x) = (M.map f) ((d X).d x))

@[simp]
/--
lemma `mk_app` / 引理 `mk_app`

English:
lemma mk_app
  given: (X : Dᵒᵖ)
  statement: (mk d d_map).app X = d X
  proof: rfl

中文:
引理 mk_app
  条件: (X : Dᵒᵖ)
  结论: (mk d d_map).app X = d X
  证明: rfl
-/
lemma mk_app (X : Dᵒᵖ) : (mk d d_map).app X = d X := rfl

/--
Definition of `Universal.mk` / `Universal.mk` 的定义

English:
definition Universal.mk
  signature: {d : M.Derivation' φ'}
  body: desc
  fac := fac
  postcomp_injective := postcomp_injective

中文:
定义 泛.mk
  签名: {d : M.导子' φ'}
  定义体: desc
  fac := fac
  postcomp_injective := postcomp_injective
-/
def Universal.mk {d : M.Derivation' φ'}
    (desc : forall {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (_ : M'.Derivation' φ'), M ⟶ M')
    (fac : forall {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (d' : M'.Derivation' φ'), d.postcomp (desc d') = d')
    (postcomp_injective : forall {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (α β : M ⟶ M'), d.postcomp α = d.postcomp β -> α = β) : d.Universal where
  desc := desc
  fac := fac
  postcomp_injective := postcomp_injective

end

end Derivation'

namespace DifferentialsConstruction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf of relative differentials of a morphism of presheaves of
commutative rings. -/
@[simps -isSimp]
/--
Definition of `relativeDifferentials'` / `relativeDifferentials'` 的定义

English:
definition relativeDifferentials'
  signature: :
  body: CommRingCat.KaehlerDifferential (φ'.app X)
  -- Have to hint `g' := R.map f` below, or it gets unfolded weirdly.
  map f := CommRingCat.KaehlerDifferential.map (g' := R.map f) (φ'.naturality f)
  -- Without `dsimp`, `ext` doesn't pick up the right lemmas.
  map_id _ := by dsimp; ext; simp
  map_comp

中文:
定义 relativeDifferentials'
  签名: :
  定义体: CommRingCat.KaehlerDifferential (φ'.app X)
  -- Have to hint `g' := R.map f` below, or it gets unfolded weirdly.
  map f := CommRingCat.KaehlerDifferential.map (g' := R.map f) (φ'.naturality f)
  -- Without `dsimp`, `ext` doesn't pick up the right lemmas.
  map_id _ := by dsimp; ext; simp
  map_comp

Depends on / 依赖: CommRingCat, CommRingCat.KaehlerDifferential, KaehlerDifferential
-/
noncomputable def relativeDifferentials' :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj X := CommRingCat.KaehlerDifferential (φ'.app X)
  -- Have to hint `g' := R.map f` below, or it gets unfolded weirdly.
  map f := CommRingCat.KaehlerDifferential.map (g' := R.map f) (φ'.naturality f)
  -- Without `dsimp`, `ext` doesn't pick up the right lemmas.
  map_id _ := by dsimp; ext; simp
  map_comp _ _ := by dsimp; ext; simp

attribute [simp] relativeDifferentials'_obj

@[simp]
/--
lemma `relativeDifferentials'_map_d` / 引理 `relativeDifferentials'_map_d`

English:
lemma relativeDifferentials'_map_d
  given: {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X)
  proof: CommRingCat.KaehlerDifferential.map_d (φ'.naturality f) _

中文:
引理 relativeDifferentials'_map_d
  条件: {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X)
  证明: CommRingCat.KaehlerDifferential.map_d (φ'.naturality f) _
-/
lemma relativeDifferentials'_map_d {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    DFunLike.coe (α := CommRingCat.KaehlerDifferential (φ'.app X))
      (β := fun _ => CommRingCat.KaehlerDifferential (φ'.app Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((relativeDifferentials' φ').map f))
        (CommRingCat.KaehlerDifferential.d x) =
        CommRingCat.KaehlerDifferential.d (R.map f x) :=
  CommRingCat.KaehlerDifferential.map_d (φ'.naturality f) _

/--
Definition of `derivation'` / `derivation'` 的定义

English:
definition derivation'
  signature: : (relativeDifferentials' φ').Derivation' φ'
  body: Derivation'.mk (fun X => CommRingCat.KaehlerDifferential.D (φ'.app X))
    (fun _ _ f x => (relativeDifferentials'_map_d φ' f x).symm)

中文:
定义 derivation'
  签名: : (relativeDifferentials' φ').导子' φ'
  定义体: Derivation'.mk (fun X => CommRingCat.KaehlerDifferential.D (φ'.app X))
    (fun _ _ f x => (relativeDifferentials'_map_d φ' f x).symm)

Depends on / 依赖: CommRingCat, CommRingCat.KaehlerDifferential.D, Derivation, KaehlerDifferential, _map_d, relativeDifferentials
-/
noncomputable def derivation' : (relativeDifferentials' φ').Derivation' φ' :=
  Derivation'.mk (fun X => CommRingCat.KaehlerDifferential.D (φ'.app X))
    (fun _ _ f x => (relativeDifferentials'_map_d φ' f x).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isUniversal'` / `isUniversal'` 的定义

English:
definition isUniversal'
  signature: : (derivation' φ').Universal
  body: Derivation'.Universal.mk
    (fun {M'} d' =>
      { app := fun X => (d'.app X).desc
        naturality := fun {X Y} f => CommRingCat.KaehlerDifferential.ext (fun b => by
          dsimp
          rw [ModuleCat.Derivation.desc_d]; rw [Derivation'.app_apply]
          erw [relativeDifferentials'_map_

中文:
定义 isUniversal'
  签名: : (derivation' φ').泛
  定义体: Derivation'.Universal.mk
    (fun {M'} d' =>
      { app := fun X => (d'.app X).desc
        naturality := fun {X Y} f => CommRingCat.KaehlerDifferential.ext (fun b => by
          dsimp
          rw [ModuleCat.Derivation.desc_d]; rw [Derivation'.app_apply]
          erw [relativeDifferentials'_map_

Depends on / 依赖: CommRingCat, CommRingCat.KaehlerDifferential.ext, Derivation, Derivation.congr_d, KaehlerDifferential, ModuleCat, ModuleCat.Derivation.desc_d, Universal, Universal.mk, _map_d, app_apply, congr_d, desc_d, naturality, relativeDifferentials
-/
noncomputable def isUniversal' : (derivation' φ').Universal :=
  Derivation'.Universal.mk
    (fun {M'} d' =>
      { app := fun X => (d'.app X).desc
        naturality := fun {X Y} f => CommRingCat.KaehlerDifferential.ext (fun b => by
          dsimp
          rw [ModuleCat.Derivation.desc_d]; rw [Derivation'.app_apply]
          erw [relativeDifferentials'_map_d φ' f]
          simp) })
    (fun {M'} d' => by
      ext X b
      apply ModuleCat.Derivation.desc_d)
    (fun {M} α β h => by
      ext1 X
      exact CommRingCat.KaehlerDifferential.ext (Derivation.congr_d h))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDifferentials (F := 𝟭 D) φ'
  body: ⟨_, _, ⟨isUniversal' φ'⟩⟩

中文:
实例 :
  签名: 有Differentials (F := 𝟭 D) φ'
  定义体: ⟨_, _, ⟨isUniversal' φ'⟩⟩

Depends on / 依赖: isUniversal
-/
instance : HasDifferentials (F := 𝟭 D) φ' := ⟨_, _, ⟨isUniversal' φ'⟩⟩

end DifferentialsConstruction

end PresheafOfModules
