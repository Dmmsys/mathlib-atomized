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

/-- Product of two distributive types is distributive. -/
/-
**Prod.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instDistrib [Distrib R] [Distrib S] : Distrib (R × S) where left_distrib _
 _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two distributive types is distributive.
-/
instance instDistrib [Distrib R] [Distrib S] : Distrib (R × S) where
  left_distrib _ _ _ := by ext <;> exact left_distrib ..
  right_distrib _ _ _ := by ext <;> exact right_distrib ..

/-- Product of two `NonUnitalNonAssocSemiring`s is a `NonUnitalNonAssocSemiring`. -/
/-
**Prod.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] [NonUnitalNonA
ssocSemiring S] : NonUnitalNonAssocSemiring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two `NonUnitalNonAssocSemiring`s is a `NonUnitalNonAssocSemiring`.
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    NonUnitalNonAssocSemiring (R × S) :=
  { (inferInstance : AddCommMonoid (R × S)),
    (inferInstance : Distrib (R × S)),
    (inferInstance : MulZeroClass (R × S)) with }

/-- Product of two `NonUnitalSemiring`s is a `NonUnitalSemiring`. -/
/-
**Prod.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring R] [NonUnitalSemiring S] : NonUni
talSemiring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two `NonUnitalSemiring`s is a `NonUnitalSemiring`.
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] [NonUnitalSemiring S] :
    NonUnitalSemiring (R × S) :=
  { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : SemigroupWithZero (R × S)) with }

/-- Product of two `NonAssocSemiring`s is a `NonAssocSemiring`. -/
/-
**Prod.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonAssocSemiring [NonAssocSemiring R] [NonAssocSemiring S] : NonAssocS
emiring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two `NonAssocSemiring`s is a `NonAssocSemiring`.
-/
instance instNonAssocSemiring [NonAssocSemiring R] [NonAssocSemiring S] :
    NonAssocSemiring (R × S) :=
  { (inferInstance : NonUnitalNonAssocSemiring (R × S)),
    (inferInstance : MulZeroOneClass (R × S)),
    (inferInstance : AddMonoidWithOne (R × S)) with }

/-- Product of two semirings is a semiring. -/
/-
**Prod.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSemiring [Semiring R] [Semiring S] : Semiring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two semirings is a semiring.
-/
instance instSemiring [Semiring R] [Semiring S] : Semiring (R × S) :=
  { (inferInstance : NonUnitalSemiring (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : MonoidWithZero (R × S)) with }

/-- Product of two `NonUnitalCommSemiring`s is a `NonUnitalCommSemiring`. -/
/-
**Prod.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonUnitalCommSemiring [NonUnitalCommSemiring R] [NonUnitalCommSemiring
 S] : NonUnitalCommSemiring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two `NonUnitalCommSemiring`s is a `NonUnitalCommSemiring`.
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [NonUnitalCommSemiring S] :
    NonUnitalCommSemiring (R × S) :=
  { (inferInstance : NonUnitalSemiring (R × S)), (inferInstance : CommSemigroup (R × S)) with }

/-- Product of two commutative semirings is a commutative semiring. -/
/-
**Prod.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCommSemiring [CommSemiring R] [CommSemiring S] : CommSemiring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two commutative semirings is a commutative semiring.
-/
instance instCommSemiring [CommSemiring R] [CommSemiring S] : CommSemiring (R × S) :=
  { (inferInstance : Semiring (R × S)), (inferInstance : CommMonoid (R × S)) with }
/-
**Prod.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing
 S] : NonUnitalNonAssocRing (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] :
    NonUnitalNonAssocRing (R × S) :=
  { (inferInstance : AddCommGroup (R × S)),
    (inferInstance : NonUnitalNonAssocSemiring (R × S)) with }
/-
**Prod.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonUnitalRing [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R ×
 S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R × S) :=
  { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonUnitalSemiring (R × S)) with }
/-
**Prod.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonAssocRing [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S) :=
  { (inferInstance : NonUnitalNonAssocRing (R × S)),
    (inferInstance : NonAssocSemiring (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

/-- Product of two rings is a ring. -/
/-
**Prod.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instRing [Ring R] [Ring S] : Ring (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two rings is a ring.
-/
instance instRing [Ring R] [Ring S] : Ring (R × S) :=
  { (inferInstance : Semiring (R × S)),
    (inferInstance : AddCommGroup (R × S)),
    (inferInstance : AddGroupWithOne (R × S)) with }

/-- Product of two `NonUnitalCommRing`s is a `NonUnitalCommRing`. -/
/-
**Prod.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instNonUnitalCommRing [NonUnitalCommRing R] [NonUnitalCommRing S] : NonUni
talCommRing (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two `NonUnitalCommRing`s is a `NonUnitalCommRing`.
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] [NonUnitalCommRing S] :
    NonUnitalCommRing (R × S) :=
  { (inferInstance : NonUnitalRing (R × S)), (inferInstance : CommSemigroup (R × S)) with }

/-- Product of two commutative rings is a commutative ring. -/
/-
**Prod.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCommRing [CommRing R] [CommRing S] : CommRing (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two commutative rings is a commutative ring.
-/
instance instCommRing [CommRing R] [CommRing S] : CommRing (R × S) :=
  { (inferInstance : Ring (R × S)), (inferInstance : CommMonoid (R × S)) with }

end Prod

namespace NonUnitalRingHom

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`. -/
/-
**NonUnitalRingHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：fst : R × S ->ₙ+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R
 × S` to `R`.
-/
def fst : R × S →ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`. -/
/-
**NonUnitalRingHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：snd : R × S ->ₙ+* S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R
 × S` to `S`.
-/
def snd : R × S →ₙ+* S :=
  { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

variable {R S}

@[simp]
/-
**NonUnitalRingHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_fst : ⇑(fst R S) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_snd : ⇑(snd R S) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl

section Prod

variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

/-- Combine two non-unital ring homomorphisms `f : R →ₙ+* S`, `g : R →ₙ+* T` into
`f.prod g : R →ₙ+* S × T` given by `(f.prod g) x = (f x, g x)` -/
/-
**NonUnitalRingHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：{R : Type u_1} →   {S : Type u_3} →     {T : Type u_5} →       [inst : Non
UnitalNonAssocSemiring R] →         [inst_1 : NonUnitalNonAssocSemiring S] →    
       [inst_2 : NonUnitalNonAssocSemiring T] → (R →ₙ+* S) → (R →ₙ+* T) → R →ₙ+*
 S × T
参数：R →ₙ+* S；R →ₙ+* T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine two non-unital ring homomorphisms `f : R →ₙ+* S`, `g : R →ₙ+* T` into
`f.prod g : R →ₙ+* S × T` given by `(f.prod g) x = (f x, g x)`
-/
protected def prod (f : R →ₙ+* S) (g : R →ₙ+* T) : R →ₙ+* S × T :=
  { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }

@[simp]
/-
**NonUnitalRingHom.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：prod_apply (x) : f.prod g x = (f x, g x)
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl

@[simp]
/-
**NonUnitalRingHom.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：fst_comp_prod : (fst S T).comp (f.prod g) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
-/
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl

@[simp]
/-
**NonUnitalRingHom.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：snd_comp_prod : (snd S T).comp (f.prod g) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
-/
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl
/-
**NonUnitalRingHom.prod_unique** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：prod_unique (f : R ->ₙ+* S × T) : ((fst S T).comp f).prod ((snd S T).comp 
f) = f
参数：f : R ->ₙ+* S × T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_unique (f : R →ₙ+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]
variable (f : R →ₙ+* R') (g : S →ₙ+* S')

/-- `Prod.map` as a `NonUnitalRingHom`. -/
/-
**NonUnitalRingHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：prodMap : R × S ->ₙ+* R' × S'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` as a `NonUnitalRingHom`.
-/
def prodMap : R × S →ₙ+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
/-
**NonUnitalRingHom.prodMap_def** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_prodMap : ⇑(prodMap f g) = Prod.map f g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
/-
**NonUnitalRingHom.prod_comp_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom
`。
形式化陈述：prod_comp_prodMap (f : T ->ₙ+* R) (g : T ->ₙ+* S) (f' : R ->ₙ+* R') (g' : 
S ->ₙ+* S') : (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g)
参数：f : T ->ₙ+* R；g : T ->ₙ+* S；f' : R ->ₙ+* R'；g' : S ->ₙ+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp_prodMap (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

end NonUnitalRingHom

namespace RingHom

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`. -/
/-
**RingHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：fst : R × S ->+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R
`.
-/
def fst : R × S →+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`. -/
/-
**RingHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：snd : R × S ->+* S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S
`.
-/
def snd : R × S →+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
/-
**RingHom.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (fst R S) := ⟨(⟨⟨·, 0⟩, rfl⟩)⟩
/-
**RingHom.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (snd R S) := ⟨(⟨⟨0, ·⟩, rfl⟩)⟩

variable {R S}

@[simp]
/-
**RingHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_fst : ⇑(fst R S) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl

@[simp]
/-
**RingHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_snd : ⇑(snd R S) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl

section Prod

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

/-- Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →+* S × T`
given by `(f.prod g) x = (f x, g x)` -/
/-
**RingHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{R : Type u_1} →   {S : Type u_3} →     {T : Type u_5} →       [inst : Non
AssocSemiring R] →         [inst_1 : NonAssocSemiring S] → [inst_2 : NonAssocSem
iring T] → (R →+* S) → (R →+* T) → R →+* S × T
参数：R →+* S；R →+* T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →
+* S × T`
given by `(f.prod g) x = (f x, g x)`
-/
protected def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
  { MonoidHom.prod (f : R →* S) (g : R →* T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }

@[simp]
/-
**RingHom.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：prod_apply (x) : f.prod g x = (f x, g x)
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl

@[simp]
/-
**RingHom.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：fst_comp_prod : (fst S T).comp (f.prod g) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl

@[simp]
/-
**RingHom.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：snd_comp_prod : (snd S T).comp (f.prod g) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl
/-
**RingHom.prod_unique** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：prod_unique (f : R ->+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f
) = f
参数：f : R ->+* S × T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_unique (f : R →+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]
variable (f : R →+* R') (g : S →+* S')

/-- `Prod.map` as a `RingHom`. -/
/-
**RingHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：prodMap : R × S ->+* R' × S'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` as a `RingHom`.
-/
def prodMap : R × S →+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
/-
**RingHom.prodMap_def** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl

@[simp]
/-
**RingHom.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_prodMap : ⇑(prodMap f g) = Prod.map f g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
/-
**RingHom.prod_comp_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：prod_comp_prodMap (f : T ->+* R) (g : T ->+* S) (f' : R ->+* R') (g' : S -
>+* S') : (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g)
参数：f : T ->+* R；g : T ->+* S；f' : R ->+* R'；g' : S ->+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp_prodMap (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

end RingHom

namespace RingEquiv

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

/-- Swapping components as an equivalence of (semi)rings. -/
/-
**RingEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：prodComm : R × S ≃+* S × R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swapping components as an equivalence of (semi)rings.
-/
def prodComm : R × S ≃+* S × R :=
  { AddEquiv.prodComm, MulEquiv.prodComm with }

@[simp]
/-
**RingEquiv.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_prodComm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap :=
  rfl

@[simp]
/-
**RingEquiv.coe_prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_prodComm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap :=
  rfl

@[simp]
/-
**RingEquiv.fst_comp_coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：fst_comp_coe_prodComm : (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × 
R) = RingHom.snd R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem fst_comp_coe_prodComm :
    (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S :=
  RingHom.ext fun _ => rfl

@[simp]
/-
**RingEquiv.snd_comp_coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：snd_comp_coe_prodComm : (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × 
R) = RingHom.fst R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem snd_comp_coe_prodComm :
    (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S :=
  RingHom.ext fun _ => rfl

section

variable (R R' S S')

/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
/-
**RingEquiv.prodProdProdComm** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`.
-/
def prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S' :=
  { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }

@[simp]
/-
**RingEquiv.prodProdProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：prodProdProdComm_symm : (prodProdProdComm R R' S S').symm = prodProdProdCo
mm R S R' S'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_symm : (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S' :=
  rfl

@[simp]
/-
**RingEquiv.prodProdProdComm_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：prodProdProdComm_toAddEquiv : (prodProdProdComm R R' S S' : _ ≃+ _) = AddE
quiv.prodProdProdComm R R' S S'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R R' S S' : _ ≃+ _) = AddEquiv.prodProdProdComm R R' S S' :=
  rfl

@[simp]
/-
**RingEquiv.prodProdProdComm_toMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：prodProdProdComm_toMulEquiv : (prodProdProdComm R R' S S' : _ ≃* _) = MulE
quiv.prodProdProdComm R R' S S'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem prodProdProdComm_toMulEquiv :
    (prodProdProdComm R R' S S' : _ ≃* _) = MulEquiv.prodProdProdComm R R' S S' :=
  rfl

@[simp]
/-
**RingEquiv.prodProdProdComm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：prodProdProdComm_toEquiv : (prodProdProdComm R R' S S' : _ ≃ _) = Equiv.pr
odProdProdComm R R' S S'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm R R' S S' : _ ≃ _) = Equiv.prodProdProdComm R R' S S' :=
  rfl

end

variable (R S) [Subsingleton S]

/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
@[simps]
/-
**RingEquiv.prodZeroRing** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：prodZeroRing : R ≃+* R × S where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring `R` is isomorphic to `R × S` when `S` is the zero ring
-/
def prodZeroRing : R ≃+* R × S where
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]

/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
@[simps]
/-
**RingEquiv.zeroRingProd** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：zeroRingProd : R ≃+* S × R where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring `R` is isomorphic to `S × R` when `S` is the zero ring
-/
def zeroRingProd : R ≃+* S × R where
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]

end RingEquiv

/-- The product of two nontrivial rings is not a domain -/
/-
**false_of_nontrivial_of_product_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：false_of_nontrivial_of_product_domain (R S : Type*) [Semiring R] [Semiring
 S] [IsDomain (R × S)] [Nontrivial R] [Nontrivial S] : False
参数：R S : Type*；R × S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Prod.mk_eq_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1
 : Zero N] {x : M} {y : N}, (x, y) = 0 ↔ x = 0 ∧ y = 0
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The product of two nontrivial rings is not a domain
-/
theorem false_of_nontrivial_of_product_domain (R S : Type*) [Semiring R] [Semiring S]
    [IsDomain (R × S)] [Nontrivial R] [Nontrivial S] : False := by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm
