/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.PUnit

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`

along with the relevant forgetful functors between them.
-/

@[expose] public section

universe u v

open CategoryTheory

/--
Definition of `SemiRingCat` / `SemiRingCat` 的定义

English:
structure SemiRingCat
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [semiring : Semiring carrier]

中文:
结构 Semi环范畴
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [semiring : 半环 carrier]
-/
structure SemiRingCat where
  /-- The object in the category of semirings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [semiring : Semiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `SemiRingCat.of R` being printed as `{ carrier := R, semiring := ... }` by
`delabStructureInstance`. -/
@[app_delab SemiRingCat.of]
meta def SemiRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] SemiRingCat.semiring

initialize_simps_projections SemiRingCat (-semiring)

namespace SemiRingCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort SemiRingCat (Type u)
  body: ⟨SemiRingCat.carrier⟩

中文:
实例 :
  签名: CoeSort Semi环范畴 (类型u)
  定义体: ⟨SemiRingCat.carrier⟩

Depends on / 依赖: SemiRingCat, SemiRingCat.carrier, carrier
-/
instance : CoeSort SemiRingCat (Type u) :=
  ⟨SemiRingCat.carrier⟩

attribute [coe] SemiRingCat.carrier

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (R : Type u) [Semiring R]
  statement: (of R : Type u) = R
  proof: rfl

中文:
引理 coe_of
  条件: (R : 类型u) [半环 R]
  结论: (of R : 类型u) = R
  证明: rfl
-/
lemma coe_of (R : Type u) [Semiring R] : (of R : Type u) = R :=
  rfl

/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (R : SemiRingCat.{u})
  statement: of R = R
  proof: rfl

中文:
引理 of_carrier
  条件: (R : Semi环范畴.{u})
  结论: of R = R
  证明: rfl
-/
lemma of_carrier (R : SemiRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `SemiRingCat`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R S : SemiRingCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : R ->+* S

中文:
结构 态射
  参数: (R S : Semi环范畴.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : R ->+* S
-/
structure Hom (R S : SemiRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R ->+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category SemiRingCat
  body: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 Semi环范畴
  定义体: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category SemiRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} SemiRingCat (fun R S => R ->+* S)
  body: Hom.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴.{u} Semi环范畴 (fun R S => R ->+* S)
  定义体: Hom.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{u} SemiRingCat (fun R S => R ->+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {R S : SemiRingCat.{u}} (f : Hom R S)
  body: ConcreteCategory.hom (C := SemiRingCat) f

中文:
缩写 态射.hom
  签名: {R S : Semi环范畴.{u}} (f : 态射 R S)
  定义体: ConcreteCategory.hom (C := SemiRingCat) f
-/
abbrev Hom.hom {R S : SemiRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := SemiRingCat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S)
  body: ConcreteCategory.ofHom (C := SemiRingCat) f

中文:
缩写 ofHom
  签名: {R S : 类型u} [半环 R] [半环 S] (f : R ->+* S)
  定义体: ConcreteCategory.ofHom (C := SemiRingCat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, SemiRingCat
-/
abbrev ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := SemiRingCat) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (R S : SemiRingCat) (f : Hom R S)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (R S : Semi环范畴) (f : 态射 R S)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (R S : SemiRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {R : SemiRingCat}
  statement: (𝟙 R : R ⟶ R).hom = RingHom.id R
  proof: rfl

中文:
引理 hom_id
  条件: {R : Semi环范畴}
  结论: (𝟙 R : R ⟶ R).hom = 环态射.id R
  证明: rfl
-/
lemma hom_id {R : SemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (R : SemiRingCat) (r : R)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (R : Semi环范畴) (r : R)
  证明: by simp

@[simp]
-/
lemma id_apply (R : SemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {R S T : Semi环范畴} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl
-/
lemma hom_comp {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {R S T : Semi环范畴} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  证明: by simp

@[ext]
-/
lemma comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R S : SemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {R S : Semi环范畴} {f g : R ⟶ S} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R S : SemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {R S : 类型u} [半环 R] [半环 S] (f : R ->+* S)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {R S : SemiRingCat} (f : R ⟶ S)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {R S : Semi环范畴} (f : R ⟶ S)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {R S : SemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {R : Type u} [Semiring R]
  statement: ofHom (RingHom.id R) = 𝟙 (of R)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {R : 类型u} [半环 R]
  结论: ofHom (环态射.id R) = 𝟙 (of R)
  证明: rfl

@[simp]
-/
lemma ofHom_id {R : Type u} [Semiring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {R S T : Type u} [Semiring R] [Semiring S] [Semiring T]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {R S T : 类型u} [半环 R] [半环 S] [半环 T]
  证明: rfl
-/
lemma ofHom_comp {R S T : Type u} [Semiring R] [Semiring S] [Semiring T]
    (f : R ->+* S) (g : S ->+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {R S : Type u} [Semiring R] [Semiring S]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {R S : 类型u} [半环 R] [半环 S]
  证明: rfl
-/
lemma ofHom_apply {R S : Type u} [Semiring R] [Semiring S]
    (f : R ->+* S) (r : R) : ofHom f r = f r := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {R S : SemiRingCat} (e : R ≅ S) (r : R)
  statement: e.inv (e.hom r) = r
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {R S : Semi环范畴} (e : R ≅ S) (r : R)
  结论: e.inv (e.hom r) = r
  证明: by
  simp
-/
lemma inv_hom_apply {R S : SemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {R S : SemiRingCat} (e : R ≅ S) (s : S)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {R S : Semi环范畴} (e : R ≅ S) (s : S)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {R S : SemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SemiRingCat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 Semi环范畴
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : SemiRingCat) where
  R ≟ R' ⊢
  (forget SemiRingCat).obj R ≟ SemiRingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

instance {R : SemiRingCat} : Semiring ((forget SemiRingCat).obj R) :=
inferInstanceAs Semiring R.carrier

/--
Instance `hasForgetToMonCat` / 实例 `hasForgetToMonCat`

English:
instance hasForgetToMonCat
  signature: : HasForget₂ SemiRingCat MonCat where
  body: { obj := fun R => MonCat.of R
      map := fun f => MonCat.ofHom f.hom.toMonoidHom }

中文:
实例 hasForgetToMonCat
  签名: : 有Forget₂ Semi环范畴 幺半群范畴 where
  定义体: { obj := fun R => MonCat.of R
      map := fun f => MonCat.ofHom f.hom.toMonoidHom }

Depends on / 依赖: MonCat, MonCat.of, MonCat.ofHom, f.hom.toMonoidHom, toMonoidHom
-/
instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat where
  forget₂ :=
    { obj := fun R => MonCat.of R
      map := fun f => MonCat.ofHom f.hom.toMonoidHom }

/--
Instance `hasForgetToAddCommMonCat` / 实例 `hasForgetToAddCommMonCat`

English:
instance hasForgetToAddCommMonCat
  signature: : HasForget₂ SemiRingCat AddCommMonCat where
  body: { obj := fun R => AddCommMonCat.of R
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

中文:
实例 hasForgetToAddCommMonCat
  签名: : 有Forget₂ Semi环范畴 加法交换幺半群范畴 where
  定义体: { obj := fun R => AddCommMonCat.of R
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

Depends on / 依赖: AddCommMonCat, AddCommMonCat.of, AddCommMonCat.ofHom, f.hom.toAddMonoidHom, toAddMonoidHom
-/
instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

/--
lemma `forget₂_monCat_map` / 引理 `forget₂_monCat_map`

English:
lemma forget₂_monCat_map
  given: {R S : SemiRingCat} (f : R ⟶ S) (x)
  proof: rfl

中文:
引理 forget₂_monCat_map
  条件: {R S : Semi环范畴} (f : R ⟶ S) (x)
  证明: rfl
-/
@[simp] lemma forget₂_monCat_map {R S : SemiRingCat} (f : R ⟶ S) (x) :
    (forget₂ SemiRingCat MonCat).map f x = f x := rfl

/--
lemma `forget₂_addCommMonCat_map` / 引理 `forget₂_addCommMonCat_map`

English:
lemma forget₂_addCommMonCat_map
  given: {R S : SemiRingCat} (f : R ⟶ S) (x)
  proof: rfl

中文:
引理 forget₂_addCommMonCat_map
  条件: {R S : Semi环范畴} (f : R ⟶ S) (x)
  证明: rfl
-/
@[simp] lemma forget₂_addCommMonCat_map {R S : SemiRingCat} (f : R ⟶ S) (x) :
    (forget₂ SemiRingCat AddCommMonCat).map f x = f x := rfl

/-- Ring equivalences are isomorphisms in category of semirings -/
@[simps]
/--
Definition of `_root_.RingEquiv.toSemiRingCatIso` / `_root_.RingEquiv.toSemiRingCatIso` 的定义

English:
definition _root_.RingEquiv.toSemiRingCatIso
  signature: {R S : Type u} [Semiring R] [Semiring S] (e : R ≃+* S)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 _root_.环等价.toSemiRingCatIso
  签名: {R S : 类型u} [半环 R] [半环 S] (e : R ≃+* S)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def _root_.RingEquiv.toSemiRingCatIso {R S : Type u} [Semiring R] [Semiring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

/--
Instance `forgetReflectIsos` / 实例 `forgetReflectIsos`

English:
instance forgetReflectIsos
  signature: : (forget SemiRingCat).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

中文:
实例 forgetReflectIsos
  签名: : (forget Semi环范畴).反映同构 where
  定义体: by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

Depends on / 依赖: SemiRingCat, e.toSemiRingCatIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toEquiv, toSemiRingCatIso
-/
instance forgetReflectIsos : (forget SemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

end SemiRingCat

/--
Definition of `RingCat` / `RingCat` 的定义

English:
structure RingCat
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [ring : Ring carrier]

中文:
结构 环范畴
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [ring : 环 carrier]
-/
structure RingCat where
  /-- The object in the category of rings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `RingCat.of R` being printed as `{ carrier := R, ring := ... }` by
`delabStructureInstance`. -/
@[app_delab RingCat.of]
meta def RingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] RingCat.ring

initialize_simps_projections RingCat (-ring)

namespace RingCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort RingCat (Type u)
  body: ⟨RingCat.carrier⟩

中文:
实例 :
  签名: CoeSort 环范畴 (类型u)
  定义体: ⟨RingCat.carrier⟩

Depends on / 依赖: RingCat, RingCat.carrier, carrier
-/
instance : CoeSort RingCat (Type u) :=
  ⟨RingCat.carrier⟩

attribute [coe] RingCat.carrier

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (R : Type u) [Ring R]
  statement: (of R : Type u) = R
  proof: rfl

中文:
引理 coe_of
  条件: (R : 类型u) [环 R]
  结论: (of R : 类型u) = R
  证明: rfl
-/
lemma coe_of (R : Type u) [Ring R] : (of R : Type u) = R :=
  rfl

/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (R : RingCat.{u})
  statement: of R = R
  proof: rfl

中文:
引理 of_carrier
  条件: (R : 环范畴.{u})
  结论: of R = R
  证明: rfl
-/
lemma of_carrier (R : RingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `RingCat`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R S : RingCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : R ->+* S

中文:
结构 态射
  参数: (R S : 环范畴.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : R ->+* S
-/
structure Hom (R S : RingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R ->+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category RingCat
  body: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 环范畴
  定义体: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category RingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} RingCat (fun R S => R ->+* S)
  body: Hom.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴.{u} 环范畴 (fun R S => R ->+* S)
  定义体: Hom.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{u} RingCat (fun R S => R ->+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {R S : RingCat.{u}} (f : Hom R S)
  body: ConcreteCategory.hom (C := RingCat) f

中文:
缩写 态射.hom
  签名: {R S : 环范畴.{u}} (f : 态射 R S)
  定义体: ConcreteCategory.hom (C := RingCat) f
-/
abbrev Hom.hom {R S : RingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := RingCat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {R S : Type u} [Ring R] [Ring S] (f : R ->+* S)
  body: ConcreteCategory.ofHom (C := RingCat) f

中文:
缩写 ofHom
  签名: {R S : 类型u} [环 R] [环 S] (f : R ->+* S)
  定义体: ConcreteCategory.ofHom (C := RingCat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, RingCat
-/
abbrev ofHom {R S : Type u} [Ring R] [Ring S] (f : R ->+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := RingCat) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (R S : RingCat) (f : Hom R S)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (R S : 环范畴) (f : 态射 R S)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (R S : RingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {R : RingCat}
  statement: (𝟙 R : R ⟶ R).hom = RingHom.id R
  proof: rfl

中文:
引理 hom_id
  条件: {R : 环范畴}
  结论: (𝟙 R : R ⟶ R).hom = 环态射.id R
  证明: rfl
-/
lemma hom_id {R : RingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (R : RingCat) (r : R)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (R : 环范畴) (r : R)
  证明: by simp

@[simp]
-/
lemma id_apply (R : RingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {R S T : 环范畴} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl
-/
lemma hom_comp {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {R S T : 环范畴} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  证明: by simp

@[ext]
-/
lemma comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {R S : 环范畴} {f g : R ⟶ S} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {R S : Type u} [Ring R] [Ring S] (f : R ->+* S)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {R S : 类型u} [环 R] [环 S] (f : R ->+* S)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {R S : Type u} [Ring R] [Ring S] (f : R ->+* S) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {R S : RingCat} (f : R ⟶ S)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {R S : 环范畴} (f : R ⟶ S)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {R S : RingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {R : Type u} [Ring R]
  statement: ofHom (RingHom.id R) = 𝟙 (of R)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {R : 类型u} [环 R]
  结论: ofHom (环态射.id R) = 𝟙 (of R)
  证明: rfl

@[simp]
-/
lemma ofHom_id {R : Type u} [Ring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {R S T : Type u} [Ring R] [Ring S] [Ring T]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {R S T : 类型u} [环 R] [环 S] [环 T]
  证明: rfl
-/
lemma ofHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R ->+* S) (g : S ->+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {R S : Type u} [Ring R] [Ring S]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {R S : 类型u} [环 R] [环 S]
  证明: rfl
-/
lemma ofHom_apply {R S : Type u} [Ring R] [Ring S]
    (f : R ->+* S) (r : R) : ofHom f r = f r := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {R S : RingCat} (e : R ≅ S) (r : R)
  statement: e.inv (e.hom r) = r
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {R S : 环范畴} (e : R ≅ S) (r : R)
  结论: e.inv (e.hom r) = r
  证明: by
  simp
-/
lemma inv_hom_apply {R S : RingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {R S : RingCat} (e : R ≅ S) (s : S)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {R S : 环范畴} (e : R ≅ S) (s : S)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {R S : RingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited RingCat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 环范畴
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited RingCat :=
  ⟨of PUnit⟩

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forget_obj_eq_coe (R R' : RingCat) where
  R ≟ R' ⊢
  (forget RingCat).obj R ≟ RingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

instance {R : RingCat} : Ring ((forget RingCat).obj R) :=
inferInstanceAs Ring R.carrier

/--
Instance `hasForgetToSemiRingCat` / 实例 `hasForgetToSemiRingCat`

English:
instance hasForgetToSemiRingCat
  signature: : HasForget₂ RingCat SemiRingCat where
  body: { obj := fun R => SemiRingCat.of R
      map := fun f => SemiRingCat.ofHom f.hom }

中文:
实例 hasForgetToSemiRingCat
  签名: : 有Forget₂ 环范畴 Semi环范畴 where
  定义体: { obj := fun R => SemiRingCat.of R
      map := fun f => SemiRingCat.ofHom f.hom }

Depends on / 依赖: SemiRingCat, SemiRingCat.of, SemiRingCat.ofHom, f.hom
-/
instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat where
  forget₂ :=
    { obj := fun R => SemiRingCat.of R
      map := fun f => SemiRingCat.ofHom f.hom }

/--
lemma `forget₂_map` / 引理 `forget₂_map`

English:
lemma forget₂_map
  given: {R S : RingCat} (f : R ⟶ S) (x)
  proof: rfl

中文:
引理 forget₂_map
  条件: {R S : 环范畴} (f : R ⟶ S) (x)
  证明: rfl
-/
@[simp] lemma forget₂_map {R S : RingCat} (f : R ⟶ S) (x) :
    (forget₂ RingCat SemiRingCat).map f x = f x := rfl

/--
Definition of `fullyFaithfulForget₂ToSemiRingCat` / `fullyFaithfulForget₂ToSemiRingCat` 的定义

English:
definition fullyFaithfulForget₂ToSemiRingCat
  signature: :
  body: ofHom f.hom

中文:
定义 fullyFaithfulForget₂ToSemiRingCat
  签名: :
  定义体: ofHom f.hom

Depends on / 依赖: f.hom
-/
def fullyFaithfulForget₂ToSemiRingCat :
    (forget₂ RingCat SemiRingCat).FullyFaithful where
  preimage f := ofHom f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ RingCat SemiRingCat).Full
  body: fullyFaithfulForget₂ToSemiRingCat.full

中文:
实例 :
  签名: (forget₂ 环范畴 Semi环范畴).满
  定义体: fullyFaithfulForget₂ToSemiRingCat.full

Depends on / 依赖: ToSemiRingCat.full
-/
instance : (forget₂ RingCat SemiRingCat).Full :=
  fullyFaithfulForget₂ToSemiRingCat.full

/--
Instance `hasForgetToAddCommGrp` / 实例 `hasForgetToAddCommGrp`

English:
instance hasForgetToAddCommGrp
  signature: : HasForget₂ RingCat AddCommGrpCat where
  body: { obj := fun R => AddCommGrpCat.of R
      map := fun f => AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

中文:
实例 hasForgetToAddCommGrp
  签名: : 有Forget₂ 环范畴 加法交换群范畴 where
  定义体: { obj := fun R => AddCommGrpCat.of R
      map := fun f => AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, AddCommGrpCat.ofHom, f.hom.toAddMonoidHom, toAddMonoidHom
-/
instance hasForgetToAddCommGrp : HasForget₂ RingCat AddCommGrpCat where
  forget₂ :=
    { obj := fun R => AddCommGrpCat.of R
      map := fun f => AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

/-- Ring equivalences are isomorphisms in category of rings -/
@[simps]
/--
Definition of `_root_.RingEquiv.toRingCatIso` / `_root_.RingEquiv.toRingCatIso` 的定义

English:
definition _root_.RingEquiv.toRingCatIso
  signature: {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 _root_.环等价.toRingCatIso
  签名: {R S : 类型u} [环 R] [环 S] (e : R ≃+* S)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def _root_.RingEquiv.toRingCatIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

/--
Instance `forgetReflectIsos` / 实例 `forgetReflectIsos`

English:
instance forgetReflectIsos
  signature: : (forget RingCat).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget RingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom

中文:
实例 forgetReflectIsos
  签名: : (forget 环范畴).反映同构 where
  定义体: by
    let i := asIso ((forget RingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom

Depends on / 依赖: RingCat, Submodule, Submodule.inclusion_injective, e.toRingCatIso.isIso_hom, f.hom, forget, i.toEquiv, inclusion_injective, isIso_hom, mono_of_injective, toEquiv, toRingCatIso
-/
instance forgetReflectIsos : (forget RingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom

end RingCat

/--
Definition of `CommSemiRingCat` / `CommSemiRingCat` 的定义

English:
structure CommSemiRingCat
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [commSemiring : CommSemiring carrier]

中文:
结构 交换Semi环范畴
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [commSemiring : 交换半环 carrier]
-/
structure CommSemiRingCat where
  /-- The object in the category of commutative semirings associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [commSemiring : CommSemiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `CommSemiRingCat.of R` being printed as `{ carrier := R, commSemiring := ... }` by
`delabStructureInstance`. -/
@[app_delab CommSemiRingCat.of]
meta def CommSemiRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] CommSemiRingCat.commSemiring

initialize_simps_projections CommSemiRingCat (-commSemiring)

namespace CommSemiRingCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CommSemiRingCat) (Type u)
  body: ⟨CommSemiRingCat.carrier⟩

中文:
实例 :
  签名: CoeSort (交换Semi环范畴) (类型u)
  定义体: ⟨CommSemiRingCat.carrier⟩

Depends on / 依赖: CommSemiRingCat, CommSemiRingCat.carrier, carrier
-/
instance : CoeSort (CommSemiRingCat) (Type u) :=
  ⟨CommSemiRingCat.carrier⟩

attribute [coe] CommSemiRingCat.carrier

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (R : Type u) [CommSemiring R]
  statement: (of R : Type u) = R
  proof: rfl

中文:
引理 coe_of
  条件: (R : 类型u) [交换半环 R]
  结论: (of R : 类型u) = R
  证明: rfl
-/
lemma coe_of (R : Type u) [CommSemiring R] : (of R : Type u) = R :=
  rfl

/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (R : CommSemiRingCat.{u})
  statement: of R = R
  proof: rfl

中文:
引理 of_carrier
  条件: (R : 交换Semi环范畴.{u})
  结论: of R = R
  证明: rfl
-/
lemma of_carrier (R : CommSemiRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `CommSemiRingCat`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R S : CommSemiRingCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : R ->+* S

中文:
结构 态射
  参数: (R S : 交换Semi环范畴.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : R ->+* S
-/
structure Hom (R S : CommSemiRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R ->+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category CommSemiRingCat
  body: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 交换Semi环范畴
  定义体: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category CommSemiRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} CommSemiRingCat (fun R S => R ->+* S)
  body: Hom.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴.{u} 交换Semi环范畴 (fun R S => R ->+* S)
  定义体: Hom.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{u} CommSemiRingCat (fun R S => R ->+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {R S : CommSemiRingCat.{u}} (f : Hom R S)
  body: ConcreteCategory.hom (C := CommSemiRingCat) f

中文:
缩写 态射.hom
  签名: {R S : 交换Semi环范畴.{u}} (f : 态射 R S)
  定义体: ConcreteCategory.hom (C := CommSemiRingCat) f
-/
abbrev Hom.hom {R S : CommSemiRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := CommSemiRingCat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S)
  body: ConcreteCategory.ofHom (C := CommSemiRingCat) f

中文:
缩写 ofHom
  签名: {R S : 类型u} [交换半环 R] [交换半环 S] (f : R ->+* S)
  定义体: ConcreteCategory.ofHom (C := CommSemiRingCat) f

Depends on / 依赖: CommSemiRingCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := CommSemiRingCat) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (R S : CommSemiRingCat) (f : Hom R S)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (R S : 交换Semi环范畴) (f : 态射 R S)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (R S : CommSemiRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {R : CommSemiRingCat}
  statement: (𝟙 R : R ⟶ R).hom = RingHom.id R
  proof: rfl

中文:
引理 hom_id
  条件: {R : 交换Semi环范畴}
  结论: (𝟙 R : R ⟶ R).hom = 环态射.id R
  证明: rfl
-/
lemma hom_id {R : CommSemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (R : CommSemiRingCat) (r : R)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (R : 交换Semi环范畴) (r : R)
  证明: by simp

@[simp]
-/
lemma id_apply (R : CommSemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {R S T : 交换Semi环范畴} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl
-/
lemma hom_comp {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {R S T : 交换Semi环范畴} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  证明: by simp

@[ext]
-/
lemma comp_apply {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {R S : 交换Semi环范畴} {f g : R ⟶ S} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S)
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {R S : 类型u} [交换半环 R] [交换半环 S] (f : R ->+* S)
  证明: rfl

@[simp]
-/
lemma hom_ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S) :
    (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {R S : CommSemiRingCat} (f : R ⟶ S)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {R S : 交换Semi环范畴} (f : R ⟶ S)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {R S : CommSemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {R : Type u} [CommSemiring R]
  statement: ofHom (RingHom.id R) = 𝟙 (of R)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {R : 类型u} [交换半环 R]
  结论: ofHom (环态射.id R) = 𝟙 (of R)
  证明: rfl

@[simp]
-/
lemma ofHom_id {R : Type u} [CommSemiring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {R S T : Type u} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {R S T : 类型u} [交换半环 R] [交换半环 S] [交换半环 T]
  证明: rfl
-/
lemma ofHom_comp {R S T : Type u} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R ->+* S) (g : S ->+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {R S : Type u} [CommSemiring R] [CommSemiring S]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {R S : 类型u} [交换半环 R] [交换半环 S]
  证明: rfl
-/
lemma ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S]
    (f : R ->+* S) (r : R) : ofHom f r = f r := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {R S : CommSemiRingCat} (e : R ≅ S) (r : R)
  statement: e.inv (e.hom r) = r
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {R S : 交换Semi环范畴} (e : R ≅ S) (r : R)
  结论: e.inv (e.hom r) = r
  证明: by
  simp
-/
lemma inv_hom_apply {R S : CommSemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {R S : CommSemiRingCat} (e : R ≅ S) (s : S)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {R S : 交换Semi环范畴} (e : R ≅ S) (s : S)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {R S : CommSemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CommSemiRingCat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 交换Semi环范畴
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : CommSemiRingCat) where
  R ≟ R' ⊢
  (forget CommSemiRingCat).obj R ≟ CommSemiRingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

instance {R : CommSemiRingCat} : CommSemiring ((forget CommSemiRingCat).obj R) :=
inferInstanceAs CommSemiring R.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `hasForgetToSemiRingCat` / 实例 `hasForgetToSemiRingCat`

English:
instance hasForgetToSemiRingCat
  signature: : HasForget₂ CommSemiRingCat SemiRingCat where
  body: { obj := fun R => ⟨R⟩
      map := fun f => ⟨f.hom⟩ }

中文:
实例 hasForgetToSemiRingCat
  签名: : 有Forget₂ 交换Semi环范畴 Semi环范畴 where
  定义体: { obj := fun R => ⟨R⟩
      map := fun f => ⟨f.hom⟩ }

Depends on / 依赖: f.hom
-/
instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat where
  forget₂ :=
    { obj := fun R => ⟨R⟩
      map := fun f => ⟨f.hom⟩ }

/--
Definition of `fullyFaithfulForget₂ToSemiRingCat` / `fullyFaithfulForget₂ToSemiRingCat` 的定义

English:
definition fullyFaithfulForget₂ToSemiRingCat
  signature: :
  body: ofHom f.hom

中文:
定义 fullyFaithfulForget₂ToSemiRingCat
  签名: :
  定义体: ofHom f.hom

Depends on / 依赖: f.hom
-/
def fullyFaithfulForget₂ToSemiRingCat :
    (forget₂ CommSemiRingCat SemiRingCat).FullyFaithful where
  preimage f := ofHom f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ CommSemiRingCat SemiRingCat).Full
  body: fullyFaithfulForget₂ToSemiRingCat.full

中文:
实例 :
  签名: (forget₂ 交换Semi环范畴 Semi环范畴).满
  定义体: fullyFaithfulForget₂ToSemiRingCat.full

Depends on / 依赖: ToSemiRingCat.full
-/
instance : (forget₂ CommSemiRingCat SemiRingCat).Full :=
  fullyFaithfulForget₂ToSemiRingCat.full

/--
Instance `hasForgetToCommMonCat` / 实例 `hasForgetToCommMonCat`

English:
instance hasForgetToCommMonCat
  signature: : HasForget₂ CommSemiRingCat CommMonCat where
  body: { obj := fun R => CommMonCat.of R
      map := fun f => CommMonCat.ofHom f.hom.toMonoidHom }

中文:
实例 hasForgetToCommMonCat
  签名: : 有Forget₂ 交换Semi环范畴 交换幺半群范畴 where
  定义体: { obj := fun R => CommMonCat.of R
      map := fun f => CommMonCat.ofHom f.hom.toMonoidHom }

Depends on / 依赖: CommMonCat, CommMonCat.of, CommMonCat.ofHom, f.hom.toMonoidHom, toMonoidHom
-/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat where
  forget₂ :=
    { obj := fun R => CommMonCat.of R
      map := fun f => CommMonCat.ofHom f.hom.toMonoidHom }

/-- Ring equivalences are isomorphisms in category of commutative semirings -/
@[simps]
/--
Definition of `_root_.RingEquiv.toCommSemiRingCatIso` / `_root_.RingEquiv.toCommSemiRingCatIso` 的定义

English:
definition _root_.RingEquiv.toCommSemiRingCatIso
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 _root_.环等价.toCommSemiRingCatIso
  定义体: ofHom e
  inv := ofHom e.symm
-/
def _root_.RingEquiv.toCommSemiRingCatIso
    {R S : Type u} [CommSemiring R] [CommSemiring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

/--
Instance `forgetReflectIsos` / 实例 `forgetReflectIsos`

English:
instance forgetReflectIsos
  signature: : (forget CommSemiRingCat).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommSemiRingCatIso.isIso_hom

中文:
实例 forgetReflectIsos
  签名: : (forget 交换Semi环范畴).反映同构 where
  定义体: by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommSemiRingCatIso.isIso_hom

Depends on / 依赖: CommSemiRingCat, e.toCommSemiRingCatIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toCommSemiRingCatIso, toEquiv
-/
instance forgetReflectIsos : (forget CommSemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommSemiRingCatIso.isIso_hom

end CommSemiRingCat

/--
Definition of `CommRingCat` / `CommRingCat` 的定义

English:
structure CommRingCat
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [commRing : CommRing carrier]

中文:
结构 交换环范畴
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [commRing : 交换环 carrier]
-/
structure CommRingCat where
  /-- The object in the category of commutative rings associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [commRing : CommRing carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `CommRingCat.of R` being printed as `{ carrier := R, commRing := ... }` by
`delabStructureInstance`. -/
@[app_delab CommRingCat.of]
meta def CommRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] CommRingCat.commRing

initialize_simps_projections CommRingCat (-commRing)

namespace CommRingCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CommRingCat (Type u)
  body: ⟨CommRingCat.carrier⟩

中文:
实例 :
  签名: CoeSort 交换环范畴 (类型u)
  定义体: ⟨CommRingCat.carrier⟩

Depends on / 依赖: CommRingCat, CommRingCat.carrier, carrier
-/
instance : CoeSort CommRingCat (Type u) :=
  ⟨CommRingCat.carrier⟩

attribute [coe] CommRingCat.carrier

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (R : Type u) [CommRing R]
  statement: (of R : Type u) = R
  proof: rfl

中文:
引理 coe_of
  条件: (R : 类型u) [交换环 R]
  结论: (of R : 类型u) = R
  证明: rfl
-/
lemma coe_of (R : Type u) [CommRing R] : (of R : Type u) = R :=
  rfl

/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (R : CommRingCat.{u})
  statement: of R = R
  proof: rfl

中文:
引理 of_carrier
  条件: (R : 交换环范畴.{u})
  结论: of R = R
  证明: rfl
-/
lemma of_carrier (R : CommRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `CommRingCat`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R S : CommRingCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : R ->+* S

中文:
结构 态射
  参数: (R S : 交换环范畴.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : R ->+* S
-/
structure Hom (R S : CommRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R ->+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category CommRingCat
  body: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 交换环范畴
  定义体: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category CommRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} CommRingCat (fun R S => R ->+* S)
  body: Hom.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴.{u} 交换环范畴 (fun R S => R ->+* S)
  定义体: Hom.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{u} CommRingCat (fun R S => R ->+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {R S : CommRingCat.{u}} (f : Hom R S)
  body: ConcreteCategory.hom (C := CommRingCat) f

中文:
缩写 态射.hom
  签名: {R S : 交换环范畴.{u}} (f : 态射 R S)
  定义体: ConcreteCategory.hom (C := CommRingCat) f
-/
abbrev Hom.hom {R S : CommRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := CommRingCat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S)
  body: ConcreteCategory.ofHom (C := CommRingCat) f

中文:
缩写 ofHom
  签名: {R S : 类型u} [交换环 R] [交换环 S] (f : R ->+* S)
  定义体: ConcreteCategory.ofHom (C := CommRingCat) f

Depends on / 依赖: CommRingCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := CommRingCat) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (R S : CommRingCat) (f : Hom R S)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (R S : 交换环范畴) (f : 态射 R S)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (R S : CommRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {R : CommRingCat}
  statement: (𝟙 R : R ⟶ R).hom = RingHom.id R
  proof: rfl

中文:
引理 hom_id
  条件: {R : 交换环范畴}
  结论: (𝟙 R : R ⟶ R).hom = 环态射.id R
  证明: rfl
-/
lemma hom_id {R : CommRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (R : CommRingCat) (r : R)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (R : 交换环范畴) (r : R)
  证明: by simp

@[simp]
-/
lemma id_apply (R : CommRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

中文:
引理 hom_comp
  条件: {R S T : 交换环范畴} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl

Depends on / 依赖: Finite
-/
lemma hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {R S T : 交换环范畴} (f : R ⟶ S) (g : S ⟶ T) (r : R)
  证明: by simp

@[ext]
-/
lemma comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {R S : 交换环范畴} {f g : R ⟶ S} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {R S : 类型u} [交换环 R] [交换环 S] (f : R ->+* S)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {R S : CommRingCat} (f : R ⟶ S)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {R S : 交换环范畴} (f : R ⟶ S)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {R S : CommRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {R : Type u} [CommRing R]
  statement: ofHom (RingHom.id R) = 𝟙 (of R)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {R : 类型u} [交换环 R]
  结论: ofHom (环态射.id R) = 𝟙 (of R)
  证明: rfl

@[simp]
-/
lemma ofHom_id {R : Type u} [CommRing R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {R S T : 类型u} [交换环 R] [交换环 S] [交换环 T]
  证明: rfl
-/
lemma ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R ->+* S) (g : S ->+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {R S : Type u} [CommRing R] [CommRing S]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {R S : 类型u} [交换环 R] [交换环 S]
  证明: rfl
-/
lemma ofHom_apply {R S : Type u} [CommRing R] [CommRing S]
    (f : R ->+* S) (r : R) : ofHom f r = f r := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {R S : CommRingCat} (e : R ≅ S) (r : R)
  statement: e.inv (e.hom r) = r
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {R S : 交换环范畴} (e : R ≅ S) (r : R)
  结论: e.inv (e.hom r) = r
  证明: by
  simp
-/
lemma inv_hom_apply {R S : CommRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {R S : CommRingCat} (e : R ≅ S) (s : S)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {R S : 交换环范畴} (e : R ≅ S) (s : S)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {R S : CommRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CommRingCat
  body: ⟨of PUnit⟩

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

中文:
实例 :
  签名: 可居 交换环范畴
  定义体: ⟨of PUnit⟩

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

Depends on / 依赖: solve_by_elim
-/
instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying `TopCat.Presheaf.restrictOpen` to commutative rings.
-/
unif_hint forget_obj_eq_coe (R R' : CommRingCat) where
  R ≟ R' ⊢
  (forget CommRingCat).obj R ≟ CommRingCat.carrier R'

instance {R : CommRingCat} : CommRing ((forget CommRingCat).obj R) :=
inferInstanceAs CommRing R.carrier

/--
Instance `hasForgetToRingCat` / 实例 `hasForgetToRingCat`

English:
instance hasForgetToRingCat
  signature: : HasForget₂ CommRingCat RingCat where
  body: { obj := fun R => RingCat.of R
      map := fun f => RingCat.ofHom f.hom }

中文:
实例 hasForgetToRingCat
  签名: : 有Forget₂ 交换环范畴 环范畴 where
  定义体: { obj := fun R => RingCat.of R
      map := fun f => RingCat.ofHom f.hom }

Depends on / 依赖: RingCat, RingCat.of, RingCat.ofHom, f.hom
-/
instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat where
  forget₂ :=
    { obj := fun R => RingCat.of R
      map := fun f => RingCat.ofHom f.hom }

/--
Definition of `fullyFaithfulForget₂ToRingCat` / `fullyFaithfulForget₂ToRingCat` 的定义

English:
definition fullyFaithfulForget₂ToRingCat
  signature: :
  body: ofHom f.hom

中文:
定义 fullyFaithfulForget₂ToRingCat
  签名: :
  定义体: ofHom f.hom

Depends on / 依赖: f.hom
-/
def fullyFaithfulForget₂ToRingCat :
    (forget₂ CommRingCat RingCat).FullyFaithful where
  preimage f := ofHom f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ CommRingCat RingCat).Full
  body: fullyFaithfulForget₂ToRingCat.full

中文:
实例 :
  签名: (forget₂ 交换环范畴 环范畴).满
  定义体: fullyFaithfulForget₂ToRingCat.full

Depends on / 依赖: ToRingCat.full
-/
instance : (forget₂ CommRingCat RingCat).Full :=
  fullyFaithfulForget₂ToRingCat.full

/--
lemma `forgetToRingCat_map_hom` / 引理 `forgetToRingCat_map_hom`

English:
lemma forgetToRingCat_map_hom
  given: {R S : CommRingCat} (f : R ⟶ S)
  proof: rfl

中文:
引理 forgetToRingCat_map_hom
  条件: {R S : 交换环范畴} (f : R ⟶ S)
  证明: rfl
-/
@[simp] lemma forgetToRingCat_map_hom {R S : CommRingCat} (f : R ⟶ S) :
    ((forget₂ CommRingCat RingCat).map f).hom = f.hom :=
  rfl

/--
lemma `forgetToRingCat_obj` / 引理 `forgetToRingCat_obj`

English:
lemma forgetToRingCat_obj
  given: {R : CommRingCat}
  proof: rfl

中文:
引理 forgetToRingCat_obj
  条件: {R : 交换环范畴}
  证明: rfl
-/
@[simp] lemma forgetToRingCat_obj {R : CommRingCat} :
    (((forget₂ CommRingCat RingCat).obj R) : Type u) = R :=
  rfl

/--
Instance `hasForgetToAddCommMonCat` / 实例 `hasForgetToAddCommMonCat`

English:
instance hasForgetToAddCommMonCat
  signature: : HasForget₂ CommRingCat CommSemiRingCat where
  body: { obj := fun R => CommSemiRingCat.of R
      map := fun f => CommSemiRingCat.ofHom f.hom }

@[simps (nameStem := "commMon")]

中文:
实例 hasForgetToAddCommMonCat
  签名: : 有Forget₂ 交换环范畴 交换Semi环范畴 where
  定义体: { obj := fun R => CommSemiRingCat.of R
      map := fun f => CommSemiRingCat.ofHom f.hom }

@[simps (nameStem := "commMon")]

Depends on / 依赖: CommSemiRingCat, CommSemiRingCat.of, CommSemiRingCat.ofHom, f.hom
-/
instance hasForgetToAddCommMonCat : HasForget₂ CommRingCat CommSemiRingCat where
  forget₂ :=
    { obj := fun R => CommSemiRingCat.of R
      map := fun f => CommSemiRingCat.ofHom f.hom }

@[simps (nameStem := "commMon")]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ CommRingCat CommMonCat
  body: { obj M := .of M, map f := CommMonCat.ofHom f.hom }
  forget_comp := rfl

中文:
实例 :
  签名: 有Forget₂ 交换环范畴 交换幺半群范畴
  定义体: { obj M := .of M, map f := CommMonCat.ofHom f.hom }
  forget_comp := rfl

Depends on / 依赖: CommMonCat, CommMonCat.ofHom, f.hom
-/
instance : HasForget₂ CommRingCat CommMonCat where
  forget₂ := { obj M := .of M, map f := CommMonCat.ofHom f.hom }
  forget_comp := rfl

/-- Ring equivalences are isomorphisms in category of commutative rings -/
@[simps]
/--
Definition of `_root_.RingEquiv.toCommRingCatIso` / `_root_.RingEquiv.toCommRingCatIso` 的定义

English:
definition _root_.RingEquiv.toCommRingCatIso
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 _root_.环等价.toCommRingCatIso
  定义体: ofHom e
  inv := ofHom e.symm
-/
def _root_.RingEquiv.toCommRingCatIso
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm

/--
Instance `forgetReflectIsos` / 实例 `forgetReflectIsos`

English:
instance forgetReflectIsos
  signature: : (forget CommRingCat).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom

中文:
实例 forgetReflectIsos
  签名: : (forget 交换环范畴).反映同构 where
  定义体: by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom

Depends on / 依赖: CommRingCat, e.toCommRingCatIso.isIso_hom, f.hom, forget, i.toEquiv, isIso_hom, toCommRingCatIso, toEquiv
-/
instance forgetReflectIsos : (forget CommRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X ->+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom

end CommRingCat

namespace CategoryTheory.Iso

/--
Definition of `semiRingCatIsoToRingEquiv` / `semiRingCatIsoToRingEquiv` 的定义

English:
definition semiRingCatIsoToRingEquiv
  signature: {R S : SemiRingCat.{u}} (e : R ≅ S)
  body: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 semiRingCatIsoToRingEquiv
  签名: {R S : Semi环范畴.{u}} (e : R ≅ S)
  定义体: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: RingEquiv, RingEquiv.ofRingHom, e.hom.hom, e.inv.hom, ofRingHom
-/
def semiRingCatIsoToRingEquiv {R S : SemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/--
Definition of `ringCatIsoToRingEquiv` / `ringCatIsoToRingEquiv` 的定义

English:
definition ringCatIsoToRingEquiv
  signature: {R S : RingCat.{u}} (e : R ≅ S)
  body: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 ringCatIsoToRingEquiv
  签名: {R S : 环范畴.{u}} (e : R ≅ S)
  定义体: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: RingEquiv, RingEquiv.ofRingHom, e.hom.hom, e.inv.hom, ofRingHom
-/
def ringCatIsoToRingEquiv {R S : RingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/--
Definition of `commSemiRingCatIsoToRingEquiv` / `commSemiRingCatIsoToRingEquiv` 的定义

English:
definition commSemiRingCatIsoToRingEquiv
  signature: {R S : CommSemiRingCat.{u}} (e : R ≅ S)
  body: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 commSemiRingCatIsoToRingEquiv
  签名: {R S : 交换Semi环范畴.{u}} (e : R ≅ S)
  定义体: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: RingEquiv, RingEquiv.ofRingHom, e.hom.hom, e.inv.hom, ofRingHom
-/
def commSemiRingCatIsoToRingEquiv {R S : CommSemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/--
Definition of `commRingCatIsoToRingEquiv` / `commRingCatIsoToRingEquiv` 的定义

English:
definition commRingCatIsoToRingEquiv
  signature: {R S : CommRingCat.{u}} (e : R ≅ S)
  body: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

中文:
定义 commRingCatIsoToRingEquiv
  签名: {R S : 交换环范畴.{u}} (e : R ≅ S)
  定义体: RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

Depends on / 依赖: RingEquiv, RingEquiv.ofRingHom, e.hom.hom, e.inv.hom, ofRingHom
-/
def commRingCatIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/--
lemma `semiRingCatIsoToRingEquiv_toRingHom` / 引理 `semiRingCatIsoToRingEquiv_toRingHom`

English:
lemma semiRingCatIsoToRingEquiv_toRingHom
  given: {R S : SemiRingCat.{u}} (e : R ≅ S)
  proof: rfl

中文:
引理 semiRingCatIsoToRingEquiv_toRingHom
  条件: {R S : Semi环范畴.{u}} (e : R ≅ S)
  证明: rfl

Depends on / 依赖: free.generatingSections_, infer_instance
-/
@[simp] lemma semiRingCatIsoToRingEquiv_toRingHom {R S : SemiRingCat.{u}} (e : R ≅ S) :
    (e.semiRingCatIsoToRingEquiv : R ->+* S) = e.hom.hom := rfl

/--
lemma `ringCatIsoToRingEquiv_toRingHom` / 引理 `ringCatIsoToRingEquiv_toRingHom`

English:
lemma ringCatIsoToRingEquiv_toRingHom
  given: {R S : RingCat.{u}} (e : R ≅ S)
  proof: rfl

中文:
引理 ringCatIsoToRingEquiv_toRingHom
  条件: {R S : 环范畴.{u}} (e : R ≅ S)
  证明: rfl

Depends on / 依赖: IsLocallyFreeData, localGeneratorsData, localGeneratorsData.IsLocallyFreeData
-/
@[simp] lemma ringCatIsoToRingEquiv_toRingHom {R S : RingCat.{u}} (e : R ≅ S) :
    (e.ringCatIsoToRingEquiv : R ->+* S) = e.hom.hom := rfl

/--
lemma `commSemiRingCatIsoToRingEquiv_toRingHom` / 引理 `commSemiRingCatIsoToRingEquiv_toRingHom`

English:
lemma commSemiRingCatIsoToRingEquiv_toRingHom
  given: {R S : CommSemiRingCat.{u}} (e : R ≅ S)
  proof: rfl

中文:
引理 commSemiRingCatIsoToRingEquiv_toRingHom
  条件: {R S : 交换Semi环范畴.{u}} (e : R ≅ S)
  证明: rfl

Depends on / 依赖: IsLocallyFree
-/
@[simp] lemma commSemiRingCatIsoToRingEquiv_toRingHom {R S : CommSemiRingCat.{u}} (e : R ≅ S) :
    (e.commSemiRingCatIsoToRingEquiv : R ->+* S) = e.hom.hom := rfl

/--
lemma `commRingCatIsoToRingEquiv_toRingHom` / 引理 `commRingCatIsoToRingEquiv_toRingHom`

English:
lemma commRingCatIsoToRingEquiv_toRingHom
  given: {R S : CommRingCat.{u}} (e : R ≅ S)
  proof: rfl

中文:
引理 commRingCatIsoToRingEquiv_toRingHom
  条件: {R S : 交换环范畴.{u}} (e : R ≅ S)
  证明: rfl
-/
@[simp] lemma commRingCatIsoToRingEquiv_toRingHom {R S : CommRingCat.{u}} (e : R ≅ S) :
    (e.commRingCatIsoToRingEquiv : R ->+* S) = e.hom.hom := rfl

end CategoryTheory.Iso

/--
lemma `RingCat.forget_map_apply` / 引理 `RingCat.forget_map_apply`

English:
lemma RingCat.forget_map_apply
  statement: {R S : RingCat} (f : R ⟶ S)
  proof: rfl

中文:
引理 环范畴.forget_map_apply
  结论: {R S : 环范畴} (f : R ⟶ S)
  证明: rfl
-/
lemma RingCat.forget_map_apply {R S : RingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget RingCat).obj R) :
    (forget _).map f x = f x :=
  rfl

/--
lemma `CommRingCat.forget_map_apply` / 引理 `CommRingCat.forget_map_apply`

English:
lemma CommRingCat.forget_map_apply
  statement: {R S : CommRingCat} (f : R ⟶ S)
  proof: rfl

中文:
引理 交换环范畴.forget_map_apply
  结论: {R S : 交换环范畴} (f : R ⟶ S)
  证明: rfl

Depends on / 依赖: IsLocallyFree, IsQuasicoherent, M.IsLocallyFree, M.IsQuasicoherent, SheafOfModules
-/
lemma CommRingCat.forget_map_apply {R S : CommRingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget CommRingCat).obj R) :
    (forget _).map f x = f x :=
  rfl
