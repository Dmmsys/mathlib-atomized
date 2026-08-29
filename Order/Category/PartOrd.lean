/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Category.Preord
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Category of partial orders

This defines `PartOrd`, the category of partial orders with monotone maps.
-/

@[expose] public section

open CategoryTheory

universe v u

/--
Definition of `PartOrd` / `PartOrd` 的定义

English:
structure PartOrd
  parameters: where
  axioms and operations (3):
    - of : :
    - (carrier : Type*)
    - [str : PartialOrder carrier]

中文:
结构 PartOrd
  参数: where
  公理与运算 (3 个):
    - of : :
    - (carrier : 类型)
    - [str : PartialOrder carrier]
-/
structure PartOrd where
  /-- Construct a bundled `PartOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrd.str

initialize_simps_projections PartOrd (carrier -> coe, -str)

namespace PartOrd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort PartOrd (Type _)
  body: ⟨PartOrd.carrier⟩

中文:
实例 :
  签名: CoeSort PartOrd (Type _)
  定义体: ⟨PartOrd.carrier⟩

Depends on / 依赖: PartOrd, PartOrd.carrier, carrier
-/
instance : CoeSort PartOrd (Type _) :=
  ⟨PartOrd.carrier⟩

attribute [coe] PartOrd.carrier

/-- The type of morphisms in `PartOrd R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : PartOrd.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : X ->o Y

中文:
结构 Hom
  参数: (X Y : PartOrd.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : X ->o Y
-/
structure Hom (X Y : PartOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X ->o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category PartOrd.{u}
  body: Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category PartOrd.{u}
  定义体: Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category PartOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory PartOrd (· ->o ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory PartOrd (· ->o ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory PartOrd (· ->o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : PartOrd.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := PartOrd) f

中文:
缩写 Hom.hom
  签名: {X Y : PartOrd.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := PartOrd) f
-/
abbrev Hom.hom {X Y : PartOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrd) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y)
  body: ConcreteCategory.ofHom (C := PartOrd) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y)
  定义体: ConcreteCategory.ofHom (C := PartOrd) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, PartOrd
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrd) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : PartOrd.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : PartOrd.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : PartOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)


/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : PartOrd}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

中文:
引理 coe_id
  条件: {X : PartOrd}
  结论: (𝟙 X : X -> X) = id
  证明: rfl
-/
lemma coe_id {X : PartOrd} : (𝟙 X : X -> X) = id := rfl

/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : PartOrd} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[ext]

中文:
引理 coe_comp
  条件: {X Y Z : PartOrd} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[ext]
-/
lemma coe_comp {X Y Z : PartOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : PartOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : PartOrd} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : PartOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [PartialOrder X]
  statement: (PartOrd.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [PartialOrder X]
  结论: (PartOrd.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrd.of X : Type u) = X := rfl

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : PartOrd}
  statement: (𝟙 X : X ⟶ X).hom = OrderHom.id
  proof: rfl

中文:
引理 hom_id
  条件: {X : PartOrd}
  结论: (𝟙 X : X ⟶ X).hom = OrderHom.id
  证明: rfl
-/
lemma hom_id {X : PartOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : PartOrd) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : PartOrd) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : PartOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : PartOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : PartOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : PartOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) : (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : PartOrd} (f : X ⟶ Y)
  statement: ofHom (Hom.hom f) = f
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : PartOrd} (f : X ⟶ Y)
  结论: ofHom (Hom.hom f) = f
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : PartOrd} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [PartialOrder X]
  statement: ofHom OrderHom.id = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [PartialOrder X]
  结论: ofHom OrderHom.id = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X ->o Y) (g : Y ->o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : PartOrd} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : PartOrd} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : PartOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : PartOrd} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : PartOrd} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : PartOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `hasForgetToPreord` / 实例 `hasForgetToPreord`

English:
instance hasForgetToPreord
  signature: : HasForget₂ PartOrd Preord where
  body: .of X
  forget₂.map f := Preord.ofHom f.hom

中文:
实例 hasForgetToPreord
  签名: : HasForget₂ PartOrd Preord where
  定义体: .of X
  forget₂.map f := Preord.ofHom f.hom
-/
instance hasForgetToPreord : HasForget₂ PartOrd Preord where
  forget₂.obj X := .of X
  forget₂.map f := Preord.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : PartOrd.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 Iso.mk
  签名: {α β : PartOrd.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : PartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : PartOrd ⥤ PartOrd where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : PartOrd ⥤ PartOrd where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : PartOrd ⥤ PartOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : PartOrd ≌ PartOrd where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : PartOrd ≌ PartOrd where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : PartOrd ≌ PartOrd where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

/-- The ulift functor `PartOrd.{u} ⥤ PartOrd.{max u v}`. -/
@[simps]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : PartOrd.{u} ⥤ PartOrd.{max u v} where
  body: .of (ULift.{v} X)
  map f := PartOrd.ofHom ⟨fun x => ULift.up (f (ULift.down x)),
    fun x y hxy => f.hom.monotone hxy⟩

中文:
定义 uliftFunctor
  签名: : PartOrd.{u} ⥤ PartOrd.{max u v} where
  定义体: .of (ULift.{v} X)
  map f := PartOrd.ofHom ⟨fun x => ULift.up (f (ULift.down x)),
    fun x y hxy => f.hom.monotone hxy⟩
-/
def uliftFunctor : PartOrd.{u} ⥤ PartOrd.{max u v} where
  obj X := .of (ULift.{v} X)
  map f := PartOrd.ofHom ⟨fun x => ULift.up (f (ULift.down x)),
    fun x y hxy => f.hom.monotone hxy⟩

end PartOrd

/--
theorem `partOrd_dual_comp_forget_to_preord` / 定理 `partOrd_dual_comp_forget_to_preord`

English:
theorem partOrd_dual_comp_forget_to_preord
  proof: rfl

中文:
定理 partOrd_dual_comp_forget_to_preord
  证明: rfl
-/
theorem partOrd_dual_comp_forget_to_preord :
    PartOrd.dual ⋙ forget₂ PartOrd Preord =
      forget₂ PartOrd Preord ⋙ Preord.dual :=
  rfl

/--
Definition of `preordToPartOrd` / `preordToPartOrd` 的定义

English:
definition preordToPartOrd
  signature: : Preord.{u} ⥤ PartOrd where
  body: .of (Antisymmetrization X (· <= ·))
  map f := PartOrd.ofHom f.hom.antisymmetrization
  map_id X := by
    ext x
    induction x using Quotient.inductionOn'
    exact Quotient.map'_mk'' _ (fun a b => id) _
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn'
    exact OrderHom.

中文:
定义 preordToPartOrd
  签名: : Preord.{u} ⥤ PartOrd where
  定义体: .of (Antisymmetrization X (· <= ·))
  map f := PartOrd.ofHom f.hom.antisymmetrization
  map_id X := by
    ext x
    induction x using Quotient.inductionOn'
    exact Quotient.map'_mk'' _ (fun a b => id) _
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn'
    exact OrderHom.

Depends on / 依赖: Antisymmetrization
-/
def preordToPartOrd : Preord.{u} ⥤ PartOrd where
  obj X := .of (Antisymmetrization X (· <= ·))
  map f := PartOrd.ofHom f.hom.antisymmetrization
  map_id X := by
    ext x
    induction x using Quotient.inductionOn'
    exact Quotient.map'_mk'' _ (fun a b => id) _
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn'
    exact OrderHom.antisymmetrization_apply_mk ..

/--
Definition of `preordToPartOrdForgetAdjunction` / `preordToPartOrdForgetAdjunction` 的定义

English:
definition preordToPartOrdForgetAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun f := Preord.ofHom
            ⟨f ∘ toAntisymmetrization (· <= ·), f.hom.mono.comp toAntisymmetrization_mono⟩
          invFun f := PartOrd.ofHom
            ⟨fun a => Quotient.liftOn' a f (fun _ _ h => (AntisymmRel.image h f.hom.mono).eq)

中文:
定义 preordToPartOrdForgetAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun f := Preord.ofHom
            ⟨f ∘ toAntisymmetrization (· <= ·), f.hom.mono.comp toAntisymmetrization_mono⟩
          invFun f := PartOrd.ofHom
            ⟨fun a => Quotient.liftOn' a f (fun _ _ h => (AntisymmRel.image h f.hom.mono).eq)

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, AntisymmRel, AntisymmRel.image, PartOrd, PartOrd.ext, PartOrd.ofHom, Preord, Preord.ofHom, Quotient, Quotient.inductionOn, Quotient.liftOn, f.hom.mono, f.hom.mono.comp, homEquiv, homEquiv_naturality_left_symm, inductionOn, invFun, left_inv, liftOn
-/
def preordToPartOrdForgetAdjunction :
    preordToPartOrd.{u} ⊣ forget₂ PartOrd Preord :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun f := Preord.ofHom
            ⟨f ∘ toAntisymmetrization (· <= ·), f.hom.mono.comp toAntisymmetrization_mono⟩
          invFun f := PartOrd.ofHom
            ⟨fun a => Quotient.liftOn' a f (fun _ _ h => (AntisymmRel.image h f.hom.mono).eq),
              fun a b => Quotient.inductionOn₂' a b fun _ _ h => f.hom.mono h⟩
          left_inv _ := PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl }
      homEquiv_naturality_left_symm _ _ :=
        PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl }

-- The `simpNF` linter would complain as `Functor.comp_obj`, `Preord.dual_obj` both apply to LHS
-- of `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_hom_app_coe`
/-- `PreordToPartOrd` and `OrderDual` commute. -/
@[simps! -isSimp hom_app_hom_coe inv_app_hom_coe]
/--
Definition of `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd` / `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd` 的定义

English:
definition preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd
  signature: :
  body: NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl)

中文:
定义 preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd
  签名: :
  定义体: NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl)

Depends on / 依赖: NatIso, NatIso.ofComponents, OrderIso, OrderIso.dualAntisymmetrization, PartOrd, PartOrd.Iso.mk, PartOrd.ext, Quotient, Quotient.inductionOn, dualAntisymmetrization, inductionOn, ofComponents
-/
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd :
    preordToPartOrd.{u} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd :=
  NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl)

-- `simp`-normal form for `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe`
@[simp]
/--
lemma `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe'` / 引理 `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe'`

English:
lemma preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe'
  statement: (X)
  proof: rfl

中文:
引理 preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe'
  结论: (X)
  证明: rfl

Depends on / 依赖: Preord, Preord.dual.obj, preordToPartOrd, preordToPartOrd.obj
-/
lemma preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe' (X)
    (a : preordToPartOrd.obj (Preord.dual.obj X)) :
    (PartOrd.Hom.hom
        (X := preordToPartOrd.obj (Preord.dual.obj X))
        (Y := PartOrd.dual.obj (preordToPartOrd.obj X))
        (preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd.inv.app X)) a =
      (OrderIso.dualAntisymmetrization ↑X).symm a :=
  rfl
