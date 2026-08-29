/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# The category of commutative Hopf algebras over a commutative ring

This file defines the bundled category `CommHopfAlgCat` of commutative Hopf algebras over a fixed
commutative ring `R` along with the forgetful functor to `CommBialgCat`.
-/

public noncomputable section

open CategoryTheory Coalgebra HopfAlgebra Limits

universe v u
variable {R : Type u} [CommRing R]

/--
Definition of `CommHopfAlgCat` / `CommHopfAlgCat` 的定义

English:
structure CommHopfAlgCat
  parameters: (R : Type u) [CommRing R]
  axioms and operations (4):
    - of((R)) : :
    - X : Type v
    - [commRing : CommRing X]
    - [hopfAlgebra : HopfAlgebra R X]

中文:
结构 交换HopfAlg范畴
  参数: (R : 类型u) [交换环 R]
  公理与运算 (4 个):
    - of((R)) : :
    - X : 类型v
    - [commRing : 交换环 X]
    - [hopfAlgebra : Hopf代数 R X]
-/
structure CommHopfAlgCat (R : Type u) [CommRing R] where
  /-- Turn an unbundled `R`-Hopf algebra into the corresponding object in the category of
  `R`-Hopf algebras. -/
  of (R) ::
  /-- The underlying type. -/
  protected X : Type v
  [commRing : CommRing X]
  [hopfAlgebra : HopfAlgebra R X]

namespace CommHopfAlgCat
variable {A B C : CommHopfAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [HopfAlgebra R X]
  [CommRing Y] [HopfAlgebra R Y] [CommRing Z] [HopfAlgebra R Z]

attribute [instance] commRing hopfAlgebra

initialize_simps_projections CommHopfAlgCat (-commRing, -hopfAlgebra)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (CommHopfAlgCat R) (Type v)
  body: ⟨CommHopfAlgCat.X⟩

中文:
实例 :
  签名: CoeSort (交换HopfAlg范畴 R) (类型v)
  定义体: ⟨CommHopfAlgCat.X⟩

Depends on / 依赖: CommHopfAlgCat, CommHopfAlgCat.X
-/
instance : CoeSort (CommHopfAlgCat R) (Type v) := ⟨CommHopfAlgCat.X⟩

attribute [coe] CommHopfAlgCat.X

variable (R) in
/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (X : Type v) [CommRing X] [HopfAlgebra R X]
  statement: (of R X : Type v) = X
  proof: rfl

中文:
引理 coe_of
  条件: (X : 类型v) [交换环 X] [Hopf代数 R X]
  结论: (of R X : 类型v) = X
  证明: rfl
-/
lemma coe_of (X : Type v) [CommRing X] [HopfAlgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommHopfAlgCat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : CommHopfAlgCat.{v} R)
  axioms and operations (2):
    - mk : :
    - hom' : A ->ₐc[R] B

中文:
结构 态射
  参数: (A B : 交换HopfAlg范畴.{v} R)
  公理与运算 (2 个):
    - mk : :
    - hom' : A ->ₐc[R] B
-/
structure Hom (A B : CommHopfAlgCat.{v} R) where
  mk ::
  /-- The underlying bialgebra map. -/
  hom' : A ->ₐc[R] B

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommHopfAlgCat.{v} R)
  body: Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 (交换HopfAlg范畴.{v} R)
  定义体: Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category (CommHopfAlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (CommHopfAlgCat.{v} R) (· ->ₐc[R] ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 (交换HopfAlg范畴.{v} R) (· ->ₐc[R] ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (CommHopfAlgCat.{v} R) (· ->ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: (f : Hom A B)
  body: ConcreteCategory.hom (C := CommHopfAlgCat R) f

中文:
缩写 态射.hom
  签名: (f : 态射 A B)
  定义体: ConcreteCategory.hom (C := CommHopfAlgCat R) f
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommHopfAlgCat R) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X} {_ : HopfAlgebra R Y}
  body: ConcreteCategory.ofHom (C := CommHopfAlgCat R) f

中文:
缩写 ofHom
  签名: {_ : 交换环 X} {_ : 交换环 Y} {_ : Hopf代数 R X} {_ : Hopf代数 R Y}
  定义体: ConcreteCategory.ofHom (C := CommHopfAlgCat R) f

Depends on / 依赖: CommHopfAlgCat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X} {_ : HopfAlgebra R Y}
    (f : X ->ₐc[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommHopfAlgCat R) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (A B : CommHopfAlgCat.{v} R) (f : Hom A B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (A B : 交换HopfAlg范畴.{v} R) (f : 态射 A B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (A B : CommHopfAlgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' -> hom)


/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  statement: (𝟙 A : A ⟶ A).hom = AlgHom.id R A
  proof: rfl

中文:
引理 hom_id
  结论: (𝟙 A : A ⟶ A).hom = 代数态射.id R A
  证明: rfl
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (A : CommHopfAlgCat.{v} R) (a : A)
  statement: (𝟙 A : A ⟶ A) a = a
  proof: by simp

中文:
引理 id_apply
  条件: (A : 交换HopfAlg范畴.{v} R) (a : A)
  结论: (𝟙 A : A ⟶ A) a = a
  证明: by simp
-/
lemma id_apply (A : CommHopfAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: (f : A ⟶ B) (g : B ⟶ C)
  statement: (f ≫ g).hom = g.hom.comp f.hom
  proof: rfl

中文:
引理 hom_comp
  条件: (f : A ⟶ B) (g : B ⟶ C)
  结论: (f ≫ g).hom = g.hom.comp f.hom
  证明: rfl
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  statement: (f ≫ g) a = g (f a)
  proof: by simp

中文:
引理 comp_apply
  条件: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  结论: (f ≫ g) a = g (f a)
  证明: by simp
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : A ⟶ B} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {f g : A ⟶ B} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: (f : X ->ₐc[R] Y)
  statement: (ofHom f).hom = f
  proof: rfl

中文:
引理 hom_ofHom
  条件: (f : X ->ₐc[R] Y)
  结论: (ofHom f).hom = f
  证明: rfl
-/
@[simp] lemma hom_ofHom (f : X ->ₐc[R] Y) : (ofHom f).hom = f := rfl
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: (f : A ⟶ B)
  statement: ofHom f.hom = f
  proof: rfl

中文:
引理 ofHom_hom
  条件: (f : A ⟶ B)
  结论: ofHom f.hom = f
  证明: rfl
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  statement: ofHom (.id R X) = 𝟙 (of R X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  结论: ofHom (.id R X) = 𝟙 (of R X)
  证明: rfl

@[simp]
-/
@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  given: (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z)
  statement: ofHom (g.comp f) = ofHom f ≫ ofHom g
  proof: rfl

中文:
引理 ofHom_comp
  条件: (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z)
  结论: ofHom (g.comp f) = ofHom f ≫ ofHom g
  证明: rfl
-/
lemma ofHom_comp (f : X ->ₐc[R] Y) (g : Y ->ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: (f : X ->ₐc[R] Y) (x : X)
  statement: ofHom f x = f x
  proof: rfl

中文:
引理 ofHom_apply
  条件: (f : X ->ₐc[R] Y) (x : X)
  结论: ofHom f x = f x
  证明: rfl
-/
lemma ofHom_apply (f : X ->ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: (e : A ≅ B) (x : A)
  statement: e.inv (e.hom x) = x
  proof: by simp

中文:
引理 inv_hom_apply
  条件: (e : A ≅ B) (x : A)
  结论: e.inv (e.hom x) = x
  证明: by simp
-/
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: (e : A ≅ B) (x : B)
  statement: e.hom (e.inv x) = x
  proof: by simp

中文:
引理 hom_inv_apply
  条件: (e : A ≅ B) (x : B)
  结论: e.hom (e.inv x) = x
  证明: by simp
-/
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CommHopfAlgCat R)
  body: ⟨of R R⟩

中文:
实例 :
  签名: 可居 (交换HopfAlg范畴 R)
  定义体: ⟨of R R⟩
-/
instance : Inhabited (CommHopfAlgCat R) := ⟨of R R⟩

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: (A : CommHopfAlgCat.{v} R)
  statement: (forget (CommHopfAlgCat.{v} R)).obj A = A
  proof: rfl

中文:
引理 forget_obj
  条件: (A : 交换HopfAlg范畴.{v} R)
  结论: (forget (交换HopfAlg范畴.{v} R)).obj A = A
  证明: rfl
-/
lemma forget_obj (A : CommHopfAlgCat.{v} R) : (forget (CommHopfAlgCat.{v} R)).obj A = A := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing ((forget (CommHopfAlgCat R)).obj A)
  body: inferInstanceAs CommRing A

中文:
实例 :
  签名: 交换环 ((forget (交换HopfAlg范畴 R)).obj A)
  定义体: inferInstanceAs CommRing A

Depends on / 依赖: CommRing
-/
instance : CommRing ((forget (CommHopfAlgCat R)).obj A) := inferInstanceAs CommRing A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HopfAlgebra R ((forget (CommHopfAlgCat R)).obj A)
  body: inferInstanceAs HopfAlgebra R A

中文:
实例 :
  签名: Hopf代数 R ((forget (交换HopfAlg范畴 R)).obj A)
  定义体: inferInstanceAs HopfAlgebra R A

Depends on / 依赖: HopfAlgebra
-/
instance : HopfAlgebra R ((forget (CommHopfAlgCat R)).obj A) := inferInstanceAs HopfAlgebra R A

/--
Instance `hasForgetToCommBialgCat` / 实例 `hasForgetToCommBialgCat`

English:
instance hasForgetToCommBialgCat
  signature: : HasForget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R) where
  body: .of R A
  forget₂.map f := CommBialgCat.ofHom f.hom

中文:
实例 hasForgetToCommBialgCat
  签名: : 有Forget₂ (交换HopfAlg范畴.{v} R) (交换Bialg范畴.{v} R) where
  定义体: .of R A
  forget₂.map f := CommBialgCat.ofHom f.hom
-/
instance hasForgetToCommBialgCat : HasForget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := CommBialgCat.ofHom f.hom

/--
lemma `forget₂_commBialgCat_obj` / 引理 `forget₂_commBialgCat_obj`

English:
lemma forget₂_commBialgCat_obj
  given: (A : CommHopfAlgCat.{v} R)
  proof: rfl

中文:
引理 forget₂_commBialgCat_obj
  条件: (A : 交换HopfAlg范畴.{v} R)
  证明: rfl
-/
@[simp] lemma forget₂_commBialgCat_obj (A : CommHopfAlgCat.{v} R) :
    (forget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R)).obj A = .of R A := rfl

/--
lemma `forget₂_commBialgCat_map` / 引理 `forget₂_commBialgCat_map`

English:
lemma forget₂_commBialgCat_map
  given: (f : A ⟶ B)
  proof: rfl

中文:
引理 forget₂_commBialgCat_map
  条件: (f : A ⟶ B)
  证明: rfl
-/
@[simp] lemma forget₂_commBialgCat_map (f : A ⟶ B) :
    (forget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R)).map f = CommBialgCat.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original Hopf
algebra. -/
@[expose, simps]
/--
Definition of `ofIsoSelf` / `ofIsoSelf` 的定义

English:
definition ofIsoSelf
  signature: (A : CommHopfAlgCat.{v} R)
  body: 𝟙 A
  inv := 𝟙 A

中文:
定义 ofIsoSelf
  签名: (A : 交换HopfAlg范畴.{v} R)
  定义体: 𝟙 A
  inv := 𝟙 A
-/
def ofIsoSelf (A : CommHopfAlgCat.{v} R) : of R A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

/-- Build an isomorphism in the category `CommHopfAlgCat R` from a `BialgEquiv` between
`HopfAlgebra`s. -/
@[expose, simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X}
  body: ofHom (e : X ->ₐc[R] Y)
  inv := ofHom (e.symm : Y ->ₐc[R] X)

中文:
定义 isoMk
  签名: {X Y : 类型v} {_ : 交换环 X} {_ : 交换环 Y} {_ : Hopf代数 R X}
  定义体: ofHom (e : X ->ₐc[R] Y)
  inv := ofHom (e.symm : Y ->ₐc[R] X)
-/
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X}
    {_ : HopfAlgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X ->ₐc[R] Y)
  inv := ofHom (e.symm : Y ->ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommHopfAlgCat R`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps -isSimp]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (i : A ≅ B)
  body: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

中文:
定义 ofIso
  签名: (i : A ≅ B)
  定义体: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

Depends on / 依赖: i.hom.hom
-/
def ofIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Commutative Hopf algebra equivalences between `HopfAlgebra`s are the same as isomorphisms in
`CommHopfAlgCat R`. -/
@[expose, simps]
/--
Definition of `isoEquivBialgEquiv` / `isoEquivBialgEquiv` 的定义

English:
definition isoEquivBialgEquiv
  signature: : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  body: ofIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 isoEquivBialgEquiv
  签名: : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  定义体: ofIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl
-/
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := ofIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `reflectsIsomorphisms_forget` / 实例 `reflectsIsomorphisms_forget`

English:
instance reflectsIsomorphisms_forget
  signature: : (forget (CommHopfAlgCat.{u} R)).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget (CommHopfAlgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

中文:
实例 reflectsIsomorphisms_forget
  签名: : (forget (交换HopfAlg范畴.{u} R)).反映同构 where
  定义体: by
    let i := asIso ((forget (CommHopfAlgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

Depends on / 依赖: CommHopfAlgCat, f.hom, forget, i.toEquiv, isIso_hom, toEquiv
-/
instance reflectsIsomorphisms_forget : (forget (CommHopfAlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommHopfAlgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommHopfAlgCat

attribute [local ext] Quiver.Hom.unop_inj

/--
Instance `CommAlgCat.grpObjOpOf` / 实例 `CommAlgCat.grpObjOpOf`

English:
instance CommAlgCat.grpObjOpOf
  signature: {A : Type u} [CommRing A] [HopfAlgebra R A]
  body: (CommAlgCat.ofHom <| antipodeAlgHom R A).op
  left_inv := by
    ext x
    -- TODO: Add more simp lemmas to make this `simpa ... using ...` again.
    simp only [unop_comp, unop_tensorObj, hom_comp, coe_tensorObj, lift_unop_hom,
      Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom, unop_id, hom_id,


中文:
实例 交换Alg范畴.grpObjOpOf
  签名: {A : 类型u} [交换环 A] [Hopf代数 R A]
  定义体: (CommAlgCat.ofHom <| antipodeAlgHom R A).op
  left_inv := by
    ext x
    -- TODO: Add more simp lemmas to make this `simpa ... using ...` again.
    simp only [unop_comp, unop_tensorObj, hom_comp, coe_tensorObj, lift_unop_hom,
      Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom, unop_id, hom_id,


Depends on / 依赖: CommAlgCat, CommAlgCat.ofHom, antipodeAlgHom
-/
instance CommAlgCat.grpObjOpOf {A : Type u} [CommRing A] [HopfAlgebra R A] :
    GrpObj (Opposite.op <| CommAlgCat.of R A) where
  inv := (CommAlgCat.ofHom <| antipodeAlgHom R A).op
  left_inv := by
    ext x
    -- TODO: Add more simp lemmas to make this `simpa ... using ...` again.
    simp only [unop_comp, unop_tensorObj, hom_comp, coe_tensorObj, lift_unop_hom,
      Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom, unop_id, hom_id,
      ← Algebra.TensorProduct.lmul'_comp_map, mul_op_of_unop_hom, AlgHom.coe_comp,
      Function.comp_apply, Bialgebra.comulAlgHom_apply, unop_tensorUnit, coe_tensorUnit,
      toUnit_unop_hom, one_op_of_unop_hom, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
    exact mul_antipode_rTensor_comul_apply (R := R) x
  right_inv := by
    ext x
    -- TODO: Add more simp lemmas to make this `simpa ... using ...` again.
    simp only [unop_comp, unop_tensorObj, hom_comp, coe_tensorObj, lift_unop_hom, unop_id, hom_id,
      Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom, ← Algebra.TensorProduct.lmul'_comp_map,
      mul_op_of_unop_hom, AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
      unop_tensorUnit, coe_tensorUnit, toUnit_unop_hom, one_op_of_unop_hom,
      Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
    exact mul_antipode_lTensor_comul_apply (R := R) x

open Opposite MonObj

@[simp]
/--
lemma `CommAlgCat.inv_op_of_unop_hom` / 引理 `CommAlgCat.inv_op_of_unop_hom`

English:
lemma CommAlgCat.inv_op_of_unop_hom
  given: {A : Type u} [CommRing A] [HopfAlgebra R A]
  proof: rfl

中文:
引理 交换Alg范畴.inv_op_of_unop_hom
  条件: {A : 类型u} [交换环 A] [Hopf代数 R A]
  证明: rfl
-/
lemma CommAlgCat.inv_op_of_unop_hom {A : Type u} [CommRing A] [HopfAlgebra R A] :
    ι[op <| CommAlgCat.of R A].unop.hom = antipodeAlgHom R A := rfl

instance (A : (CommAlgCat R)ᵒᵖ) [GrpObj A] : HopfAlgebra R A.unop :=
  .ofAlgHom ι[A].unop.hom
    congr($(GrpObj.left_inv (X := A)).unop.hom)
    congr($(GrpObj.right_inv (X := A)).unop.hom)

variable (R) in
/-- Commutative Hopf algebras over a commutative ring `R` are the same thing as cogroup
`R`-algebras. -/
@[expose, simps! functor_obj_unop_X inverse_obj unitIso_hom_app unitIso_inv_app counitIso_hom_app
  counitIso_inv_app]
/--
Definition of `commHopfAlgCatEquivCogrpCommAlgCat` / `commHopfAlgCatEquivCogrpCommAlgCat` 的定义

English:
definition commHopfAlgCatEquivCogrpCommAlgCat
  signature: : CommHopfAlgCat R ≌ (Grp (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  body: op .mk op .of R A
functor.map {A B} f := op .mk .mk' op CommAlgCat.ofHom f.hom
  inverse.obj A := .of R A.unop.X.unop
inverse.map {A B} f := CommHopfAlgCat.ofHom .ofAlgHom f.unop.hom.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.u

中文:
定义 commHopfAlgCatEquivCogrpCommAlgCat
  签名: : 交换HopfAlg范畴 R ≌ (群 (交换Alg范畴 R)ᵒᵖ)ᵒᵖ where
  定义体: op .mk op .of R A
functor.map {A B} f := op .mk .mk' op CommAlgCat.ofHom f.hom
  inverse.obj A := .of R A.unop.X.unop
inverse.map {A B} f := CommHopfAlgCat.ofHom .ofAlgHom f.unop.hom.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.u
-/
def commHopfAlgCatEquivCogrpCommAlgCat : CommHopfAlgCat R ≌ (Grp (CommAlgCat R)ᵒᵖ)ᵒᵖ where
functor.obj A := op .mk op .of R A
functor.map {A B} f := op .mk .mk' op CommAlgCat.ofHom f.hom
  inverse.obj A := .of R A.unop.X.unop
inverse.map {A B} f := CommHopfAlgCat.ofHom .ofAlgHom f.unop.hom.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

instance {A : CommHopfAlgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj A).unop.X :=
inferInstanceAs IsCommMonObj op CommAlgCat.of R A
