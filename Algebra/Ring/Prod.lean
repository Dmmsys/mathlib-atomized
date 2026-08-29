/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Data.Int.Cast.Prod
public import Mathlib.Algebra.GroupWithZero.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Equiv

/-!
# Semiring, ring etc. structures on `R × S`

In this file we define two-binop (`Semiring`, `Ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `RingHom`s and similarly for
`NonUnitalRingHom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* S`: projections `Prod.fst` and `Prod.snd`
  as `RingHom`s;
* `f.prod g : R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : R × S → R' × S'`: `Prod.map f g` as a `RingHom`,
  sends `(x, y)` to `(f x, g y)`.
-/

@[expose] public section


variable {R R' S S' T : Type*}

namespace Prod

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: [Distrib R] [Distrib S]
  body: by ext <;> exact left_distrib ..
  right_distrib _ _ _ := by ext <;> exact right_distrib ..

中文:
实例 instDistrib
  签名: [Distrib R] [Distrib S]
  定义体: by ext <;> exact left_distrib ..
  right_distrib _ _ _ := by ext <;> exact right_distrib ..

Depends on / 依赖: left_distrib, right_distrib
-/
instance instDistrib [Distrib R] [Distrib S] : Distrib (R × S) where
  left_distrib _ _ _ := by ext <;> exact left_distrib ..
  right_distrib _ _ _ := by ext <;> exact right_distrib ..

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  body: { (inferInstance : AddCommMonoid (R × S)),
    (inferInstance : Distrib (R × S)),
    (inferInstance : MulZeroClass (R × S)) with }

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  定义体: { (inferInstance : AddCommMonoid (R × S)),
    (inferInstance : Distrib (R × S)),
    (inferInstance : MulZeroClass (R × S)) with }

Depends on / 依赖: AddCommMonoid, Distrib, MulZeroClass
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    NonUnitalNonAssocSemiring (R × S) :=
  { (inferInstance : AddCommMonoid (R × S)),
    (inferInstance : Distrib (R × S)),
    (inferInstance : MulZeroClass (R × S)) with }

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring R] [NonUnitalSemiring S]
  body: { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : SemigroupWithZero (R × S)) with }

中文:
实例 instNonUnitalSemiring
  签名: [NonUnitalSemiring R] [NonUnitalSemiring S]
  定义体: { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : SemigroupWithZero (R × S)) with }

Depends on / 依赖: NonUnitalNonAssocSemiring, SemigroupWithZero
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] [NonUnitalSemiring S] :
    NonUnitalSemiring (R × S) :=
  { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : SemigroupWithZero (R × S)) with }

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [NonAssocSemiring R] [NonAssocSemiring S]
  body: { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : MulZeroOneClass (R × S)),
    (inferInstance : AddMonoidWithOne (R × S)) with }

中文:
实例 instNonAssocSemiring
  签名: [NonAssocSemiring R] [NonAssocSemiring S]
  定义体: { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : MulZeroOneClass (R × S)),
    (inferInstance : AddMonoidWithOne (R × S)) with }

Depends on / 依赖: AddMonoidWithOne, MulZeroOneClass, NonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring [NonAssocSemiring R] [NonAssocSemiring S] :
    NonAssocSemiring (R × S) :=
  { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : MulZeroOneClass (R × S)),
    (inferInstance : AddMonoidWithOne (R × S)) with }

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring R] [Semiring S]
  body: { (inferInstance : NonUnitalSemiring (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : MonoidWithZero (R × S)) with }

中文:
实例 instSemiring
  签名: [Semiring R] [Semiring S]
  定义体: { (inferInstance : NonUnitalSemiring (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : MonoidWithZero (R × S)) with }

Depends on / 依赖: MonoidWithZero, NonAssocSemiring, NonUnitalSemiring
-/
instance instSemiring [Semiring R] [Semiring S] : Semiring (R × S) :=
  { (inferInstance : NonUnitalSemiring (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : MonoidWithZero (R × S)) with }

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R] [NonUnitalCommSemiring S]
  body: { (inferInstance : NonUnitalSemiring (R × S)), (inferInstance : CommSemigroup (R × S)) with }

中文:
实例 instNonUnitalCommSemiring
  签名: [NonUnitalCommSemiring R] [NonUnitalCommSemiring S]
  定义体: { (inferInstance : NonUnitalSemiring (R × S)), (inferInstance : CommSemigroup (R × S)) with }

Depends on / 依赖: CommSemigroup, NonUnitalSemiring
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [NonUnitalCommSemiring S] :
    NonUnitalCommSemiring (R × S) :=
  { (inferInstance : NonUnitalSemiring (R × S)), (inferInstance : CommSemigroup (R × S)) with }

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring R] [CommSemiring S]
  body: { (inferInstance : Semiring (R × S)), (inferInstance : CommMonoid (R × S)) with }

中文:
实例 instCommSemiring
  签名: [CommSemiring R] [CommSemiring S]
  定义体: { (inferInstance : Semiring (R × S)), (inferInstance : CommMonoid (R × S)) with }

Depends on / 依赖: CommMonoid, Semiring
-/
instance instCommSemiring [CommSemiring R] [CommSemiring S] : CommSemiring (R × S) :=
  { (inferInstance : Semiring (R × S)), (inferInstance : CommMonoid (R × S)) with }

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  body: { (inferInstance : AddCommGroup (R × S)),
    (inferInstance : NonUnitalNonAssocSemiring (R × S)) with }

中文:
实例 instNonUnitalNonAssocRing
  签名: [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  定义体: { (inferInstance : AddCommGroup (R × S)),
    (inferInstance : NonUnitalNonAssocSemiring (R × S)) with }

Depends on / 依赖: AddCommGroup, NonUnitalNonAssocSemiring
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] :
    NonUnitalNonAssocRing (R × S) :=
  { (inferInstance : AddCommGroup (R × S)),
    (inferInstance : NonUnitalNonAssocSemiring (R × S)) with }

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [NonUnitalRing R] [NonUnitalRing S]
  body: { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonUnitalSemiring (R × S)) with }

中文:
实例 instNonUnitalRing
  签名: [NonUnitalRing R] [NonUnitalRing S]
  定义体: { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonUnitalSemiring (R × S)) with }

Depends on / 依赖: NonUnitalNonAssocRing, NonUnitalSemiring
-/
instance instNonUnitalRing [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R × S) :=
  { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonUnitalSemiring (R × S)) with }

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [NonAssocRing R] [NonAssocRing S]
  body: { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

中文:
实例 instNonAssocRing
  签名: [NonAssocRing R] [NonAssocRing S]
  定义体: { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

Depends on / 依赖: AddGroupWithOne, NonAssocSemiring, NonUnitalNonAssocRing
-/
instance instNonAssocRing [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S) :=
  { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Ring R] [Ring S]
  body: { (inferInstance : Semiring (R × S)),
    (inferInstance : AddCommGroup (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

中文:
实例 instRing
  签名: [Ring R] [Ring S]
  定义体: { (inferInstance : Semiring (R × S)),
    (inferInstance : AddCommGroup (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

Depends on / 依赖: AddCommGroup, AddGroupWithOne, Semiring
-/
instance instRing [Ring R] [Ring S] : Ring (R × S) :=
  { (inferInstance : Semiring (R × S)),
    (inferInstance : AddCommGroup (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: [NonUnitalCommRing R] [NonUnitalCommRing S]
  body: { (inferInstance : NonUnitalRing (R × S)), (inferInstance : CommSemigroup (R × S)) with }

中文:
实例 instNonUnitalCommRing
  签名: [NonUnitalCommRing R] [NonUnitalCommRing S]
  定义体: { (inferInstance : NonUnitalRing (R × S)), (inferInstance : CommSemigroup (R × S)) with }

Depends on / 依赖: CommSemigroup, NonUnitalRing
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] [NonUnitalCommRing S] :
    NonUnitalCommRing (R × S) :=
  { (inferInstance : NonUnitalRing (R × S)), (inferInstance : CommSemigroup (R × S)) with }

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [CommRing R] [CommRing S]
  body: { (inferInstance : Ring (R × S)), (inferInstance : CommMonoid (R × S)) with }

中文:
实例 instCommRing
  签名: [CommRing R] [CommRing S]
  定义体: { (inferInstance : Ring (R × S)), (inferInstance : CommMonoid (R × S)) with }

Depends on / 依赖: CommMonoid
-/
instance instCommRing [CommRing R] [CommRing S] : CommRing (R × S) :=
  { (inferInstance : Ring (R × S)), (inferInstance : CommMonoid (R × S)) with }

end Prod

namespace NonUnitalRingHom

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : R × S ->ₙ+* R
  body: { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

中文:
定义 fst
  签名: : R × S ->ₙ+* R
  定义体: { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.fst, MulHom, MulHom.fst, Prod.fst
-/
def fst : R × S ->ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : R × S ->ₙ+* S
  body: { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

中文:
定义 snd
  签名: : R × S ->ₙ+* S
  定义体: { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.snd, MulHom, MulHom.snd, Prod.snd
-/
def snd : R × S ->ₙ+* S :=
  { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

variable {R S}

@[simp]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ⇑(fst R S) = Prod.fst
  proof: rfl

@[simp]

中文:
定理 coe_fst
  结论: ⇑(fst R S) = Prod.fst
  证明: rfl

@[simp]
-/
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl

@[simp]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ⇑(snd R S) = Prod.snd
  proof: rfl

中文:
定理 coe_snd
  结论: ⇑(snd R S) = Prod.snd
  证明: rfl
-/
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl

section Prod

variable [NonUnitalNonAssocSemiring T] (f : R ->ₙ+* S) (g : R ->ₙ+* T)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : R ->ₙ+* S) (g : R ->ₙ+* T)
  body: { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R ->+ S) (g : R ->+ T) with
    toFun := fun x => (f x, g x) }

@[simp]

中文:
定义 prod
  签名: (f : R ->ₙ+* S) (g : R ->ₙ+* T)
  定义体: { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R ->+ S) (g : R ->+ T) with
    toFun := fun x => (f x, g x) }

@[simp]
-/
protected def prod (f : R ->ₙ+* S) (g : R ->ₙ+* T) : R ->ₙ+* S × T :=
  { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R ->+ S) (g : R ->+ T) with
    toFun := fun x => (f x, g x) }

@[simp]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (x)
  statement: f.prod g x = (f x, g x)
  proof: rfl

@[simp]

中文:
定理 prod_apply
  条件: (x)
  结论: f.prod g x = (f x, g x)
  证明: rfl

@[simp]
-/
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl

@[simp]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  statement: (fst S T).comp (f.prod g) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 fst_comp_prod
  结论: (fst S T).comp (f.prod g) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  statement: (snd S T).comp (f.prod g) = g
  proof: ext fun _ => rfl

中文:
定理 snd_comp_prod
  结论: (snd S T).comp (f.prod g) = g
  证明: ext fun _ => rfl
-/
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl

/--
theorem `prod_unique` / 定理 `prod_unique`

English:
theorem prod_unique
  given: (f : R ->ₙ+* S × T)
  statement: ((fst S T).comp f).prod ((snd S T).comp f) = f
  proof: ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

中文:
定理 prod_unique
  条件: (f : R ->ₙ+* S × T)
  结论: ((fst S T).comp f).prod ((snd S T).comp f) = f
  证明: ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

Depends on / 依赖: coe_fst, coe_snd, comp_apply, prod_apply
-/
theorem prod_unique (f : R ->ₙ+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]
variable (f : R ->ₙ+* R') (g : S ->ₙ+* S')

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: : R × S ->ₙ+* R' × S'
  body: (f.comp (fst R S)).prod (g.comp (snd R S))

中文:
定义 prodMap
  签名: : R × S ->ₙ+* R' × S'
  定义体: (f.comp (fst R S)).prod (g.comp (snd R S))

Depends on / 依赖: f.comp, g.comp
-/
def prodMap : R × S ->ₙ+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))

/--
theorem `prodMap_def` / 定理 `prodMap_def`

English:
theorem prodMap_def
  statement: prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S))
  proof: rfl

@[simp]

中文:
定理 prodMap_def
  结论: prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S))
  证明: rfl

@[simp]
-/
theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl

@[simp]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  statement: ⇑(prodMap f g) = Prod.map f g
  proof: rfl

中文:
定理 coe_prodMap
  结论: ⇑(prodMap f g) = Prod.map f g
  证明: rfl
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

/--
theorem `prod_comp_prodMap` / 定理 `prod_comp_prodMap`

English:
theorem prod_comp_prodMap
  given: (f : T ->ₙ+* R) (g : T ->ₙ+* S) (f' : R ->ₙ+* R') (g' : S ->ₙ+* S')
  proof: rfl

中文:
定理 prod_comp_prodMap
  条件: (f : T ->ₙ+* R) (g : T ->ₙ+* S) (f' : R ->ₙ+* R') (g' : S ->ₙ+* S')
  证明: rfl
-/
theorem prod_comp_prodMap (f : T ->ₙ+* R) (g : T ->ₙ+* S) (f' : R ->ₙ+* R') (g' : S ->ₙ+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

end NonUnitalRingHom

namespace RingHom

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : R × S ->+* R
  body: { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

中文:
定义 fst
  签名: : R × S ->+* R
  定义体: { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.fst, MonoidHom, MonoidHom.fst, Prod.fst
-/
def fst : R × S ->+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : R × S ->+* S
  body: { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

中文:
定义 snd
  签名: : R × S ->+* S
  定义体: { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.snd, MonoidHom, MonoidHom.snd, Prod.snd
-/
def snd : R × S ->+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (fst R S) := ⟨(⟨⟨·, 0⟩, rfl⟩)⟩
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (snd R S) := ⟨(⟨⟨0, ·⟩, rfl⟩)⟩

variable {R S}

@[simp]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ⇑(fst R S) = Prod.fst
  proof: rfl

@[simp]

中文:
定理 coe_fst
  结论: ⇑(fst R S) = Prod.fst
  证明: rfl

@[simp]
-/
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl

@[simp]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ⇑(snd R S) = Prod.snd
  proof: rfl

中文:
定理 coe_snd
  结论: ⇑(snd R S) = Prod.snd
  证明: rfl

Depends on / 依赖: IsPreimmersion, IsPreimmersion.comp_iff, Scheme, Scheme.fromSpecResidueField, comp_iff, fromSpecResidueField, infer_instance
-/
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl

section Prod

variable [NonAssocSemiring T] (f : R ->+* S) (g : R ->+* T)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : R ->+* S) (g : R ->+* T)
  body: { MonoidHom.prod (f : R ->* S) (g : R ->* T), AddMonoidHom.prod (f : R ->+ S) (g : R ->+ T) with
    toFun := fun x => (f x, g x) }

@[simp]

中文:
定义 prod
  签名: (f : R ->+* S) (g : R ->+* T)
  定义体: { MonoidHom.prod (f : R ->* S) (g : R ->* T), AddMonoidHom.prod (f : R ->+ S) (g : R ->+ T) with
    toFun := fun x => (f x, g x) }

@[simp]

Depends on / 依赖: X.fromSpecResidueField, fromSpecResidueField
-/
protected def prod (f : R ->+* S) (g : R ->+* T) : R ->+* S × T :=
  { MonoidHom.prod (f : R ->* S) (g : R ->* T), AddMonoidHom.prod (f : R ->+ S) (g : R ->+ T) with
    toFun := fun x => (f x, g x) }

@[simp]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (x)
  statement: f.prod g x = (f x, g x)
  proof: rfl

@[simp]

中文:
定理 prod_apply
  条件: (x)
  结论: f.prod g x = (f x, g x)
  证明: rfl

@[simp]
-/
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl

@[simp]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  statement: (fst S T).comp (f.prod g) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 fst_comp_prod
  结论: (fst S T).comp (f.prod g) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  statement: (snd S T).comp (f.prod g) = g
  proof: ext fun _ => rfl

中文:
定理 snd_comp_prod
  结论: (snd S T).comp (f.prod g) = g
  证明: ext fun _ => rfl
-/
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl

/--
theorem `prod_unique` / 定理 `prod_unique`

English:
theorem prod_unique
  given: (f : R ->+* S × T)
  statement: ((fst S T).comp f).prod ((snd S T).comp f) = f
  proof: ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

中文:
定理 prod_unique
  条件: (f : R ->+* S × T)
  结论: ((fst S T).comp f).prod ((snd S T).comp f) = f
  证明: ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

Depends on / 依赖: coe_fst, coe_snd, comp_apply, prod_apply
-/
theorem prod_unique (f : R ->+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]
variable (f : R ->+* R') (g : S ->+* S')

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: : R × S ->+* R' × S'
  body: (f.comp (fst R S)).prod (g.comp (snd R S))

中文:
定义 prodMap
  签名: : R × S ->+* R' × S'
  定义体: (f.comp (fst R S)).prod (g.comp (snd R S))

Depends on / 依赖: f.comp, g.comp
-/
def prodMap : R × S ->+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))

/--
theorem `prodMap_def` / 定理 `prodMap_def`

English:
theorem prodMap_def
  statement: prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S))
  proof: rfl

@[simp]

中文:
定理 prodMap_def
  结论: prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S))
  证明: rfl

@[simp]
-/
theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl

@[simp]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  statement: ⇑(prodMap f g) = Prod.map f g
  proof: rfl

中文:
定理 coe_prodMap
  结论: ⇑(prodMap f g) = Prod.map f g
  证明: rfl
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

/--
theorem `prod_comp_prodMap` / 定理 `prod_comp_prodMap`

English:
theorem prod_comp_prodMap
  given: (f : T ->+* R) (g : T ->+* S) (f' : R ->+* R') (g' : S ->+* S')
  proof: rfl

中文:
定理 prod_comp_prodMap
  条件: (f : T ->+* R) (g : T ->+* S) (f' : R ->+* R') (g' : S ->+* S')
  证明: rfl
-/
theorem prod_comp_prodMap (f : T ->+* R) (g : T ->+* S) (f' : R ->+* R') (g' : S ->+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

end RingHom

namespace RingEquiv

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : R × S ≃+* S × R
  body: { AddEquiv.prodComm, MulEquiv.prodComm with }

@[simp]

中文:
定义 prodComm
  签名: : R × S ≃+* S × R
  定义体: { AddEquiv.prodComm, MulEquiv.prodComm with }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.prodComm, MulEquiv, MulEquiv.prodComm, prodComm
-/
def prodComm : R × S ≃+* S × R :=
  { AddEquiv.prodComm, MulEquiv.prodComm with }

@[simp]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  statement: ⇑(prodComm : R × S ≃+* S × R) = Prod.swap
  proof: rfl

@[simp]

中文:
定理 coe_prodComm
  结论: ⇑(prodComm : R × S ≃+* S × R) = Prod.swap
  证明: rfl

@[simp]
-/
theorem coe_prodComm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap :=
  rfl

@[simp]
/--
theorem `coe_prodComm_symm` / 定理 `coe_prodComm_symm`

English:
theorem coe_prodComm_symm
  statement: ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap
  proof: rfl

@[simp]

中文:
定理 coe_prodComm_symm
  结论: ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap
  证明: rfl

@[simp]
-/
theorem coe_prodComm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap :=
  rfl

@[simp]
/--
theorem `fst_comp_coe_prodComm` / 定理 `fst_comp_coe_prodComm`

English:
theorem fst_comp_coe_prodComm
  proof: RingHom.ext fun _ => rfl

@[simp]

中文:
定理 fst_comp_coe_prodComm
  证明: RingHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem fst_comp_coe_prodComm :
    (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S :=
  RingHom.ext fun _ => rfl

@[simp]
/--
theorem `snd_comp_coe_prodComm` / 定理 `snd_comp_coe_prodComm`

English:
theorem snd_comp_coe_prodComm
  proof: RingHom.ext fun _ => rfl

中文:
定理 snd_comp_coe_prodComm
  证明: RingHom.ext fun _ => rfl

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem snd_comp_coe_prodComm :
    (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S :=
  RingHom.ext fun _ => rfl

section

variable (R R' S S')

/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
/--
Definition of `prodProdProdComm` / `prodProdProdComm` 的定义

English:
definition prodProdProdComm
  signature: : (R × R') × S × S' ≃+* (R × S) × R' × S'
  body: { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }

@[simp]

中文:
定义 prodProdProdComm
  签名: : (R × R') × S × S' ≃+* (R × S) × R' × S'
  定义体: { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.prodProdProdComm, MulEquiv, MulEquiv.prodProdProdComm, invFun, prodProdProdComm
-/
def prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S' :=
  { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }

@[simp]
/--
theorem `prodProdProdComm_symm` / 定理 `prodProdProdComm_symm`

English:
theorem prodProdProdComm_symm
  statement: (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S'
  proof: rfl

@[simp]

中文:
定理 prodProdProdComm_symm
  结论: (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S'
  证明: rfl

@[simp]
-/
theorem prodProdProdComm_symm : (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S' :=
  rfl

@[simp]
/--
theorem `prodProdProdComm_toAddEquiv` / 定理 `prodProdProdComm_toAddEquiv`

English:
theorem prodProdProdComm_toAddEquiv
  proof: rfl

@[simp]

中文:
定理 prodProdProdComm_toAddEquiv
  证明: rfl

@[simp]
-/
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R R' S S' : _ ≃+ _) = AddEquiv.prodProdProdComm R R' S S' :=
  rfl

@[simp]
/--
theorem `prodProdProdComm_toMulEquiv` / 定理 `prodProdProdComm_toMulEquiv`

English:
theorem prodProdProdComm_toMulEquiv
  proof: rfl

@[simp]

中文:
定理 prodProdProdComm_toMulEquiv
  证明: rfl

@[simp]
-/
theorem prodProdProdComm_toMulEquiv :
    (prodProdProdComm R R' S S' : _ ≃* _) = MulEquiv.prodProdProdComm R R' S S' :=
  rfl

@[simp]
/--
theorem `prodProdProdComm_toEquiv` / 定理 `prodProdProdComm_toEquiv`

English:
theorem prodProdProdComm_toEquiv
  proof: rfl

中文:
定理 prodProdProdComm_toEquiv
  证明: rfl
-/
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm R R' S S' : _ ≃ _) = Equiv.prodProdProdComm R R' S S' :=
  rfl

end

variable (R S) [Subsingleton S]

/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
@[simps]
/--
Definition of `prodZeroRing` / `prodZeroRing` 的定义

English:
definition prodZeroRing
  signature: : R ≃+* R × S where
  body: (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]

中文:
定义 prodZeroRing
  签名: : R ≃+* R × S where
  定义体: (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
-/
def prodZeroRing : R ≃+* R × S where
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]

/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
@[simps]
/--
Definition of `zeroRingProd` / `zeroRingProd` 的定义

English:
definition zeroRingProd
  signature: : R ≃+* S × R where
  body: (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]

中文:
定义 zeroRingProd
  签名: : R ≃+* S × R where
  定义体: (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
-/
def zeroRingProd : R ≃+* S × R where
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]

end RingEquiv

/--
theorem `false_of_nontrivial_of_product_domain` / 定理 `false_of_nontrivial_of_product_domain`

English:
theorem false_of_nontrivial_of_product_domain
  statement: (R S : Type*) [Semiring R] [Semiring S]
  proof: by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero]; rw [Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm

中文:
定理 false_of_nontrivial_of_product_domain
  结论: (R S : 类型) [Semiring R] [Semiring S]
  证明: by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero]; rw [Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero, Prod.mk_eq_zero, eq_zero_or_eq_zero_of_mul_eq_zero, h.symm, mk_eq_zero, zero_ne_one
-/
theorem false_of_nontrivial_of_product_domain (R S : Type*) [Semiring R] [Semiring S]
    [IsDomain (R × S)] [Nontrivial R] [Nontrivial S] : False := by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero]; rw [Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm
