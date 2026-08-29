/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Tactic.Spread

/-!
# Additive and multiplicative equivalences associated to `Multiplicative` and `Additive`.
-/

@[expose] public section

assert_not_exists Finite Fintype

variable {ι G H : Type*}

/-- Reinterpret `G ≃+ H` as `Multiplicative G ≃* Multiplicative H`. -/
@[simps]
/--
Definition of `AddEquiv.toMultiplicative` / `AddEquiv.toMultiplicative` 的定义

English:
definition AddEquiv.toMultiplicative
  signature: [AddZeroClass G] [AddZeroClass H]
  body: { toFun := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    invFun := Ad

中文:
定义 AddEquiv.toMultiplicative
  签名: [AddZeroClass G] [AddZeroClass H]
  定义体: { toFun := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    invFun := Ad

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicative, AddMonoidHom.toMultiplicative.symm, f.left_inv, f.right_inv, f.symm.toAddMonoidHom, f.symm.toMonoidHom, f.toAddMonoidHom, f.toMonoidHom, invFun, left_inv, map_add, map_mul, right_inv, toAddMonoidHom, toMonoidHom, toMultiplicative
-/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/-- Reinterpret `G ≃* H` as `Additive G ≃+ Additive H`. -/
@[simps]
/--
Definition of `MulEquiv.toAdditive` / `MulEquiv.toAdditive` 的定义

English:
definition MulEquiv.toAdditive
  signature: [MulOneClass G] [MulOneClass H]
  body: { toFun := MonoidHom.toAdditive f.toMonoidHom
    invFun := MonoidHom.toAdditive f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  invFun f :=
  { toFun := MonoidHom.toAdditive.symm f.toAddMonoidHom
    invFun := MonoidHom.toAdditive.symm f.symm

中文:
定义 MulEquiv.toAdditive
  签名: [MulOneClass G] [MulOneClass H]
  定义体: { toFun := MonoidHom.toAdditive f.toMonoidHom
    invFun := MonoidHom.toAdditive f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  invFun f :=
  { toFun := MonoidHom.toAdditive.symm f.toAddMonoidHom
    invFun := MonoidHom.toAdditive.symm f.symm

Depends on / 依赖: MonoidHom, MonoidHom.toAdditive, MonoidHom.toAdditive.symm, f.left_inv, f.right_inv, f.symm.toAddMonoidHom, f.symm.toMonoidHom, f.toAddMonoidHom, f.toMonoidHom, invFun, left_inv, map_add, map_mul, right_inv, toAddMonoidHom, toAdditive, toMonoidHom
-/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f :=
  { toFun := MonoidHom.toAdditive f.toMonoidHom
    invFun := MonoidHom.toAdditive f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  invFun f :=
  { toFun := MonoidHom.toAdditive.symm f.toAddMonoidHom
    invFun := MonoidHom.toAdditive.symm f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }

/-- Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`. -/
@[simps]
/--
Definition of `AddEquiv.toMultiplicativeRight` / `AddEquiv.toMultiplicativeRight` 的定义

English:
definition AddEquiv.toMultiplicativeRight
  signature: [MulOneClass G] [AddZeroClass H]
  body: { toFun := f.toAddMonoidHom.toMultiplicativeRight
    invFun := f.symm.toAddMonoidHom.toMultiplicativeLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveLeft
    invFun := f.symm.toMonoidHom.toAdditiveRight
    

中文:
定义 AddEquiv.toMultiplicativeRight
  签名: [MulOneClass G] [AddZeroClass H]
  定义体: { toFun := f.toAddMonoidHom.toMultiplicativeRight
    invFun := f.symm.toAddMonoidHom.toMultiplicativeLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveLeft
    invFun := f.symm.toMonoidHom.toAdditiveRight
    

Depends on / 依赖: f.left_inv, f.right_inv, f.symm.toAddMonoidHom.toMultiplicativeLeft, f.symm.toMonoidHom.toAdditiveRight, f.toAddMonoidHom.toMultiplicativeRight, f.toMonoidHom.toAdditiveLeft, invFun, left_inv, map_add, map_mul, right_inv, toAddMonoidHom, toAdditiveLeft, toAdditiveRight, toMonoidHom, toMultiplicativeLeft, toMultiplicativeRight
-/
def AddEquiv.toMultiplicativeRight [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
  { toFun := f.toAddMonoidHom.toMultiplicativeRight
    invFun := f.symm.toAddMonoidHom.toMultiplicativeLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveLeft
    invFun := f.symm.toMonoidHom.toAdditiveRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/--
Definition of `MulEquiv.toAdditiveLeft` / `MulEquiv.toAdditiveLeft` 的定义

English:
abbreviation MulEquiv.toAdditiveLeft
  signature: [MulOneClass G] [AddZeroClass H]
  body: AddEquiv.toMultiplicativeRight.symm

中文:
缩写 MulEquiv.toAdditiveLeft
  签名: [MulOneClass G] [AddZeroClass H]
  定义体: AddEquiv.toMultiplicativeRight.symm

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicativeRight.symm, toMultiplicativeRight
-/
abbrev MulEquiv.toAdditiveLeft [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicativeRight.symm

/-- Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`. -/
@[simps]
/--
Definition of `AddEquiv.toMultiplicativeLeft` / `AddEquiv.toMultiplicativeLeft` 的定义

English:
definition AddEquiv.toMultiplicativeLeft
  signature: [AddZeroClass G] [MulOneClass H]
  body: { toFun := f.toAddMonoidHom.toMultiplicativeLeft
    invFun := f.symm.toAddMonoidHom.toMultiplicativeRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveRight
    invFun := f.symm.toMonoidHom.toAdditiveLeft
    

中文:
定义 AddEquiv.toMultiplicativeLeft
  签名: [AddZeroClass G] [MulOneClass H]
  定义体: { toFun := f.toAddMonoidHom.toMultiplicativeLeft
    invFun := f.symm.toAddMonoidHom.toMultiplicativeRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveRight
    invFun := f.symm.toMonoidHom.toAdditiveLeft
    

Depends on / 依赖: f.left_inv, f.right_inv, f.symm.toAddMonoidHom.toMultiplicativeRight, f.symm.toMonoidHom.toAdditiveLeft, f.toAddMonoidHom.toMultiplicativeLeft, f.toMonoidHom.toAdditiveRight, invFun, left_inv, map_add, map_mul, right_inv, toAddMonoidHom, toAdditiveLeft, toAdditiveRight, toMonoidHom, toMultiplicativeLeft, toMultiplicativeRight
-/
def AddEquiv.toMultiplicativeLeft [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
  { toFun := f.toAddMonoidHom.toMultiplicativeLeft
    invFun := f.symm.toAddMonoidHom.toMultiplicativeRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveRight
    invFun := f.symm.toMonoidHom.toAdditiveLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/--
Definition of `MulEquiv.toAdditiveRight` / `MulEquiv.toAdditiveRight` 的定义

English:
abbreviation MulEquiv.toAdditiveRight
  signature: [AddZeroClass G] [MulOneClass H]
  body: AddEquiv.toMultiplicativeLeft.symm

中文:
缩写 MulEquiv.toAdditiveRight
  签名: [AddZeroClass G] [MulOneClass H]
  定义体: AddEquiv.toMultiplicativeLeft.symm

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicativeLeft.symm, toMultiplicativeLeft
-/
abbrev MulEquiv.toAdditiveRight [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicativeLeft.symm

/-- The multiplicative version of an additivized monoid is mul-equivalent to itself. -/
@[simps! apply symm_apply]
/--
Definition of `MulEquiv.toMultiplicative_toAdditive` / `MulEquiv.toMultiplicative_toAdditive` 的定义

English:
definition MulEquiv.toMultiplicative_toAdditive
  signature: [MulOneClass G]
  body: AddEquiv.toMultiplicativeLeft MulEquiv.toAdditive (.refl _)

中文:
定义 MulEquiv.toMultiplicative_toAdditive
  签名: [MulOneClass G]
  定义体: AddEquiv.toMultiplicativeLeft MulEquiv.toAdditive (.refl _)

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicativeLeft, MulEquiv, MulEquiv.toAdditive, toAdditive, toMultiplicativeLeft
-/
def MulEquiv.toMultiplicative_toAdditive [MulOneClass G] :
    Multiplicative (Additive G) ≃* G :=
AddEquiv.toMultiplicativeLeft MulEquiv.toAdditive (.refl _)

/-- The additive version of a multiplicativized additive monoid is add-equivalent to itself. -/
@[simps! apply symm_apply]
/--
Definition of `AddEquiv.toAdditive_toMultiplicative` / `AddEquiv.toAdditive_toMultiplicative` 的定义

English:
definition AddEquiv.toAdditive_toMultiplicative
  signature: [AddZeroClass G]
  body: MulEquiv.toAdditiveLeft AddEquiv.toMultiplicative (.refl _)

中文:
定义 AddEquiv.toAdditive_toMultiplicative
  签名: [AddZeroClass G]
  定义体: MulEquiv.toAdditiveLeft AddEquiv.toMultiplicative (.refl _)

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicative, MulEquiv, MulEquiv.toAdditiveLeft, toAdditiveLeft, toMultiplicative
-/
def AddEquiv.toAdditive_toMultiplicative [AddZeroClass G] :
    Additive (Multiplicative G) ≃+ G :=
MulEquiv.toAdditiveLeft AddEquiv.toMultiplicative (.refl _)

/--
Definition of `monoidEndToAdditive` / `monoidEndToAdditive` 的定义

English:
definition monoidEndToAdditive
  signature: (M : Type*) [MulOneClass M]
  body: { MonoidHom.toAdditive with
    map_mul' := fun _ _ => rfl }

中文:
定义 monoidEndToAdditive
  签名: (M : 类型) [MulOneClass M]
  定义体: { MonoidHom.toAdditive with
    map_mul' := fun _ _ => rfl }
-/
@[simps!] def monoidEndToAdditive (M : Type*) [MulOneClass M] :
    Monoid.End M ≃* AddMonoid.End (Additive M) :=
  { MonoidHom.toAdditive with
    map_mul' := fun _ _ => rfl }

/--
Definition of `addMonoidEndToMultiplicative` / `addMonoidEndToMultiplicative` 的定义

English:
definition addMonoidEndToMultiplicative
  signature: (A : Type*) [AddZeroClass A]
  body: { AddMonoidHom.toMultiplicative with
    map_mul' := fun _ _ => rfl }

中文:
定义 addMonoidEndToMultiplicative
  签名: (A : 类型) [AddZeroClass A]
  定义体: { AddMonoidHom.toMultiplicative with
    map_mul' := fun _ _ => rfl }
-/
@[simps!] def addMonoidEndToMultiplicative (A : Type*) [AddZeroClass A] :
    AddMonoid.End A ≃* Monoid.End (Multiplicative A) :=
  { AddMonoidHom.toMultiplicative with
    map_mul' := fun _ _ => rfl }

/-- `Multiplicative (∀ i : ι, K i)` is equivalent to `∀ i : ι, Multiplicative (K i)`. -/
@[simps]
/--
Definition of `MulEquiv.piMultiplicative` / `MulEquiv.piMultiplicative` 的定义

English:
definition MulEquiv.piMultiplicative
  signature: (K : ι -> Type*) [forall i, Add (K i)]
  body: fun i => Multiplicative.ofAdd x.toAdd i
  invFun x := Multiplicative.ofAdd fun i => (x i).toAdd
  map_mul' _ _ := rfl

中文:
定义 MulEquiv.piMultiplicative
  签名: (K : ι -> 类型) [对任意 i, Add (K i)]
  定义体: fun i => Multiplicative.ofAdd x.toAdd i
  invFun x := Multiplicative.ofAdd fun i => (x i).toAdd
  map_mul' _ _ := rfl

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, x.toAdd
-/
def MulEquiv.piMultiplicative (K : ι -> Type*) [forall i, Add (K i)] :
    Multiplicative (forall i : ι, K i) ≃* (forall i : ι, Multiplicative (K i)) where
toFun x := fun i => Multiplicative.ofAdd x.toAdd i
  invFun x := Multiplicative.ofAdd fun i => (x i).toAdd
  map_mul' _ _ := rfl

variable (ι) (G) in
/--
Definition of `MulEquiv.funMultiplicative` / `MulEquiv.funMultiplicative` 的定义

English:
abbreviation MulEquiv.funMultiplicative
  signature: [Add G]
  body: MulEquiv.piMultiplicative fun _ => G

中文:
缩写 MulEquiv.funMultiplicative
  签名: [Add G]
  定义体: MulEquiv.piMultiplicative fun _ => G

Depends on / 依赖: MulEquiv, MulEquiv.piMultiplicative, piMultiplicative
-/
abbrev MulEquiv.funMultiplicative [Add G] :
    Multiplicative (ι -> G) ≃* (ι -> Multiplicative G) :=
  MulEquiv.piMultiplicative fun _ => G

/-- `Additive (∀ i : ι, K i)` is equivalent to `∀ i : ι, Additive (K i)`. -/
@[simps]
/--
Definition of `AddEquiv.piAdditive` / `AddEquiv.piAdditive` 的定义

English:
definition AddEquiv.piAdditive
  signature: (K : ι -> Type*) [forall i, Mul (K i)]
  body: fun i => Additive.ofMul x.toMul i
  invFun x := Additive.ofMul fun i => (x i).toMul
  map_add' _ _ := rfl

中文:
定义 AddEquiv.piAdditive
  签名: (K : ι -> 类型) [对任意 i, Mul (K i)]
  定义体: fun i => Additive.ofMul x.toMul i
  invFun x := Additive.ofMul fun i => (x i).toMul
  map_add' _ _ := rfl

Depends on / 依赖: Additive, Additive.ofMul, x.toMul
-/
def AddEquiv.piAdditive (K : ι -> Type*) [forall i, Mul (K i)] :
    Additive (forall i : ι, K i) ≃+ (forall i : ι, Additive (K i)) where
toFun x := fun i => Additive.ofMul x.toMul i
  invFun x := Additive.ofMul fun i => (x i).toMul
  map_add' _ _ := rfl

variable (ι) (G) in
/--
Definition of `AddEquiv.funAdditive` / `AddEquiv.funAdditive` 的定义

English:
abbreviation AddEquiv.funAdditive
  signature: [Mul G]
  body: AddEquiv.piAdditive fun _ => G

中文:
缩写 AddEquiv.funAdditive
  签名: [Mul G]
  定义体: AddEquiv.piAdditive fun _ => G

Depends on / 依赖: AddEquiv, AddEquiv.piAdditive, piAdditive
-/
abbrev AddEquiv.funAdditive [Mul G] :
    Additive (ι -> G) ≃+ (ι -> Additive G) :=
  AddEquiv.piAdditive fun _ => G

section

variable (G) (H)

/-- `Additive (Multiplicative G)` is just `G`. -/
@[simps!]
/--
Definition of `AddEquiv.additiveMultiplicative` / `AddEquiv.additiveMultiplicative` 的定义

English:
definition AddEquiv.additiveMultiplicative
  signature: [AddZeroClass G]
  body: MulEquiv.toAdditiveLeft (MulEquiv.refl (Multiplicative G))

中文:
定义 AddEquiv.additiveMultiplicative
  签名: [AddZeroClass G]
  定义体: MulEquiv.toAdditiveLeft (MulEquiv.refl (Multiplicative G))

Depends on / 依赖: MulEquiv, MulEquiv.refl, MulEquiv.toAdditiveLeft, Multiplicative, toAdditiveLeft
-/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditiveLeft (MulEquiv.refl (Multiplicative G))

/-- `Multiplicative (Additive H)` is just `H`. -/
@[simps!]
/--
Definition of `MulEquiv.multiplicativeAdditive` / `MulEquiv.multiplicativeAdditive` 的定义

English:
definition MulEquiv.multiplicativeAdditive
  signature: [MulOneClass H]
  body: AddEquiv.toMultiplicativeLeft (AddEquiv.refl (Additive H))

中文:
定义 MulEquiv.multiplicativeAdditive
  签名: [MulOneClass H]
  定义体: AddEquiv.toMultiplicativeLeft (AddEquiv.refl (Additive H))

Depends on / 依赖: AddEquiv, AddEquiv.refl, AddEquiv.toMultiplicativeLeft, Additive, toMultiplicativeLeft
-/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicativeLeft (AddEquiv.refl (Additive H))

/-- `Multiplicative (G × H)` is equivalent to `Multiplicative G × Multiplicative H`. -/
@[simps]
/--
Definition of `MulEquiv.prodMultiplicative` / `MulEquiv.prodMultiplicative` 的定义

English:
definition MulEquiv.prodMultiplicative
  signature: [Add G] [Add H]
  body: (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  invFun := fun (x, y) => Multiplicative.ofAdd (x.toAdd, y.toAdd)
  map_mul' _ _ := rfl

中文:
定义 MulEquiv.prodMultiplicative
  签名: [Add G] [Add H]
  定义体: (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  invFun := fun (x, y) => Multiplicative.ofAdd (x.toAdd, y.toAdd)
  map_mul' _ _ := rfl

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, x.toAdd
-/
def MulEquiv.prodMultiplicative [Add G] [Add H] :
    Multiplicative (G × H) ≃* Multiplicative G × Multiplicative H where
  toFun x := (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  invFun := fun (x, y) => Multiplicative.ofAdd (x.toAdd, y.toAdd)
  map_mul' _ _ := rfl

/-- `Additive (G × H)` is equivalent to `Additive G × Additive H`. -/
@[simps]
/--
Definition of `AddEquiv.prodAdditive` / `AddEquiv.prodAdditive` 的定义

English:
definition AddEquiv.prodAdditive
  signature: [Mul G] [Mul H]
  body: (Additive.ofMul x.toMul.1,
    Additive.ofMul x.toMul.2)
  invFun := fun (x, y) => Additive.ofMul (x.toMul, y.toMul)
  map_add' _ _ := rfl

中文:
定义 AddEquiv.prodAdditive
  签名: [Mul G] [Mul H]
  定义体: (Additive.ofMul x.toMul.1,
    Additive.ofMul x.toMul.2)
  invFun := fun (x, y) => Additive.ofMul (x.toMul, y.toMul)
  map_add' _ _ := rfl

Depends on / 依赖: Additive, Additive.ofMul, x.toMul
-/
def AddEquiv.prodAdditive [Mul G] [Mul H] :
    Additive (G × H) ≃+ Additive G × Additive H where
  toFun x := (Additive.ofMul x.toMul.1,
    Additive.ofMul x.toMul.2)
  invFun := fun (x, y) => Additive.ofMul (x.toMul, y.toMul)
  map_add' _ _ := rfl

end

section End

variable {M : Type*}

/-- `Monoid.End M` is equivalent to `AddMonoid.End (Additive M)`. -/
@[simps! apply]
/--
Definition of `MulEquiv.Monoid.End` / `MulEquiv.Monoid.End` 的定义

English:
definition MulEquiv.Monoid.End
  signature: [Monoid M]
  body: MonoidHom.toAdditive
  map_mul' := fun _ _ => rfl

中文:
定义 MulEquiv.Monoid.End
  签名: [Monoid M]
  定义体: MonoidHom.toAdditive
  map_mul' := fun _ _ => rfl

Depends on / 依赖: MonoidHom, MonoidHom.toAdditive, toAdditive
-/
def MulEquiv.Monoid.End [Monoid M] : Monoid.End M ≃* AddMonoid.End (Additive M) where
  __ := MonoidHom.toAdditive
  map_mul' := fun _ _ => rfl

/-- `AddMonoid.End M` is equivalent to `Monoid.End (Multiplicative M)`. -/
@[simps! apply]
/--
Definition of `MulEquiv.AddMonoid.End` / `MulEquiv.AddMonoid.End` 的定义

English:
definition MulEquiv.AddMonoid.End
  signature: [AddMonoid M]
  body: AddMonoidHom.toMultiplicative
  map_mul' := fun _ _ => rfl

中文:
定义 MulEquiv.AddMonoid.End
  签名: [AddMonoid M]
  定义体: AddMonoidHom.toMultiplicative
  map_mul' := fun _ _ => rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicative, toMultiplicative
-/
def MulEquiv.AddMonoid.End [AddMonoid M] :
    AddMonoid.End M ≃* _root_.Monoid.End (Multiplicative M) where
  __ := AddMonoidHom.toMultiplicative
  map_mul' := fun _ _ => rfl

end End
