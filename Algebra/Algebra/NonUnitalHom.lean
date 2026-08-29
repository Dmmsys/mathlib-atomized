/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Prod

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
* an addition,
* an additive zero,
* a multiplication,
* a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `Mul` instead of `Group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `NonUnitalAlgHom`.

TODO: add `NonUnitalAlgEquiv` when needed.

## Main definitions

  * `NonUnitalAlgHom`
  * `AlgHom.toNonUnitalAlgHom`

## Tags

non-unital, algebra, morphism
-/

@[expose] public section

universe u u₁ v w w₁ w₂ w₃

variable {R : Type u} {S : Type u₁}

/--
Definition of `NonUnitalAlgHom` / `NonUnitalAlgHom` 的定义

English:
structure NonUnitalAlgHom
  parameters: [Monoid R] [Monoid S] (φ : R ->* S) (A : Type v) (B : Type w)
  extends: A ->ₑ+[φ] B, A ->ₙ* B
  (no additional axioms)

中文:
结构 NonUnitalAlgHom
  参数: [Monoid R] [Monoid S] (φ : R ->* S) (A : 类型v) (B : Type w)
  继承: A ->ₑ+[φ] B, A ->ₙ* B
  (无附加公理)

Depends on / 依赖: PreEnvelGroup, PreEnvelGroup.inv, PreEnvelGroup.mul, PreEnvelGroupRel, Quotient, Quotient.inductionOn, Quotient.liftOn, Quotient.sound, congr_inv, congr_mul, inductionOn, liftOn, mul_assoc, mul_one, one_mul
-/
structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R ->* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A ->ₑ+[φ] B, A ->ₙ* B

@[inherit_doc NonUnitalAlgHom]
infixr:25 " ->ₙₐ " => NonUnitalAlgHom _

@[inherit_doc]
notation:25 A " ->ₛₙₐ[" φ "] " B => NonUnitalAlgHom φ A B

@[inherit_doc]
notation:25 A " ->ₙₐ[" R "] " B => NonUnitalAlgHom (MonoidHom.id R) A B

attribute [nolint docBlame] NonUnitalAlgHom.toMulHom

/--
Definition of `NonUnitalAlgSemiHomClass` / `NonUnitalAlgSemiHomClass` 的定义

English:
class NonUnitalAlgSemiHomClass
  parameters: (F : Type*) {R S : outParam Type*} [Monoid R] [Monoid S]
  extends: DistribMulActionSemiHomClass F φ A B, MulHomClass F A B
  (no additional axioms)

中文:
类 NonUnitalAlgSemiHomClass
  参数: (F : 类型) {R S : outParam 类型} [Monoid R] [Monoid S]
  继承: DistribMulActionSemiHomClass F φ A B, MulHomClass F A B
  (无附加公理)

Depends on / 依赖: PreEnvelGroupRel, Quotient, Quotient.inductionOn, Quotient.sound, inductionOn, inv_mul_cancel
-/
class NonUnitalAlgSemiHomClass (F : Type*) {R S : outParam Type*} [Monoid R] [Monoid S]
    (φ : outParam (R ->* S)) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction S B] [FunLike F A B] : Prop
    extends DistribMulActionSemiHomClass F φ A B, MulHomClass F A B

/--
Definition of `NonUnitalAlgHomClass` / `NonUnitalAlgHomClass` 的定义

English:
abbreviation NonUnitalAlgHomClass
  signature: (F : Type*) (R A B : outParam Type*)
  body: NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B

中文:
缩写 NonUnitalAlgHomClass
  签名: (F : 类型) (R A B : outParam 类型)
  定义体: NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B

Depends on / 依赖: MonoidHom, MonoidHom.id, NonUnitalAlgSemiHomClass
-/
abbrev NonUnitalAlgHomClass (F : Type*) (R A B : outParam Type*)
    [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction R B] [FunLike F A B] :=
  NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B

namespace NonUnitalAlgHomClass

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass
    {F R S A B : Type*} {_ : Monoid R} {_ : Monoid S} {φ : outParam (R ->* S)}
    {_ : NonUnitalNonAssocSemiring A} [DistribMulAction R A]
    {_ : NonUnitalNonAssocSemiring B} [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] : NonUnitalRingHomClass F A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with }

variable [Semiring R] [Semiring S] {φ : R ->+* S}
  {A B : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module S B]

-- see Note [lower instance priority]
instance (priority := 100) {F R S A B : Type*}
    {_ : Semiring R} {_ : Semiring S} {φ : R ->+* S}
    {_ : NonUnitalSemiring A} {_ : NonUnitalSemiring B} [Module R A] [Module S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass (R := R) (S := S) F φ A B] :
    SemilinearMapClass F φ A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with map_smulₛₗ := map_smulₛₗ }

instance (priority := 100) {F : Type*} [FunLike F A B] [Module R B] [NonUnitalAlgHomClass F R A B] :
    LinearMapClass F R A B :=
  { ‹NonUnitalAlgHomClass F R A B› with map_smulₛₗ := map_smulₛₗ }

/-- Turn an element of a type `F` satisfying `NonUnitalAlgSemiHomClass F φ A B` into an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[φ] B`. -/
@[coe]
/--
Definition of `toNonUnitalAlgSemiHom` / `toNonUnitalAlgSemiHom` 的定义

English:
definition toNonUnitalAlgSemiHom
  signature: {F R S : Type*} [Monoid R] [Monoid S] {φ : R ->* S} {A B : Type*}
  body: { (f : A ->ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

中文:
定义 toNonUnitalAlgSemiHom
  签名: {F R S : 类型} [Monoid R] [Monoid S] {φ : R ->* S} {A B : 类型}
  定义体: { (f : A ->ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

Depends on / 依赖: map_smul
-/
def toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R ->* S} {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) : A ->ₛₙₐ[φ] B :=
  { (f : A ->ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

instance {F R S A B : Type*} [Monoid R] [Monoid S] {φ : R ->* S}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] :
      CoeTC F (A ->ₛₙₐ[φ] B) :=
  ⟨toNonUnitalAlgSemiHom⟩

/--
Definition of `toNonUnitalAlgHom` / `toNonUnitalAlgHom` 的定义

English:
definition toNonUnitalAlgHom
  signature: {F R : Type*} [Monoid R] {A B : Type*}
  body: { (f : A ->ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

中文:
定义 toNonUnitalAlgHom
  签名: {F R : 类型} [Monoid R] {A B : 类型}
  定义体: { (f : A ->ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

Depends on / 依赖: map_smul
-/
def toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A ->ₙₐ[R] B :=
  { (f : A ->ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }

instance {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A ->ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

end NonUnitalAlgHomClass

namespace NonUnitalAlgHom

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R ->* S)
variable (A : Type v) (B : Type w) (C : Type w₁)
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->ₛₙₐ[φ] B) A B
  body: f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[simp]

中文:
实例 :
  签名: FunLike (A ->ₛₙₐ[φ] B) A B
  定义体: f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[simp]

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ->ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : A ->ₛₙₐ[φ] B)
  statement: f.toFun = ⇑f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: f.toFun = ⇑f
  证明: rfl
-/
theorem toFun_eq_coe (f : A ->ₛₙₐ[φ] B) : f.toFun = ⇑f :=
  rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : A ->ₛₙₐ[φ] B)
  body: f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun -> apply, -toDistribMulActionHom)

中文:
定义 Simps.apply
  签名: (f : A ->ₛₙₐ[φ] B)
  定义体: f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun -> apply, -toDistribMulActionHom)
-/
def Simps.apply (f : A ->ₛₙₐ[φ] B) : A -> B := f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun -> apply, -toDistribMulActionHom)

variable {φ A B C}
@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: {F : Type*} [FunLike F A B]
  proof: rfl

中文:
定理 coe_coe
  结论: {F : 类型} [FunLike F A B]
  证明: rfl
-/
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A ->ₛₙₐ[φ] B) = f :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (A ->ₛₙₐ[φ] B) (A -> B) (↑)
  proof: by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

中文:
定理 coe_injective
  结论: @Function.Injective (A ->ₛₙₐ[φ] B) (A -> B) (↑)
  证明: by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
-/
theorem coe_injective : @Function.Injective (A ->ₛₙₐ[φ] B) (A -> B) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->ₛₙₐ[φ] B) A B
  body: f.toFun
  coe_injective := coe_injective

中文:
实例 :
  签名: FunLike (A ->ₛₙₐ[φ] B) A B
  定义体: f.toFun
  coe_injective := coe_injective

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ->ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective := coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalAlgSemiHomClass (A ->ₛₙₐ[φ] B) φ A B
  body: f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'

@[ext]

中文:
实例 :
  签名: NonUnitalAlgSemiHomClass (A ->ₛₙₐ[φ] B) φ A B
  定义体: f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'

@[ext]

Depends on / 依赖: f.map_add, map_add
-/
instance : NonUnitalAlgSemiHomClass (A ->ₛₙₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x)
  statement: f = g
  proof: coe_injective funext h

中文:
定理 ext
  条件: {f g : A ->ₛₙₐ[φ] B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: coe_injective funext h

Depends on / 依赖: coe_injective
-/
theorem ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) : f = g :=
coe_injective funext h

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : A ->ₛₙₐ[φ] B} (h : f = g) (x : A)
  statement: f x = g x
  proof: h ▸ rfl

@[simp]

中文:
定理 congr_fun
  条件: {f g : A ->ₛₙₐ[φ] B} (h : f = g) (x : A)
  结论: f x = g x
  证明: h ▸ rfl

@[simp]
-/
theorem congr_fun {f g : A ->ₛₙₐ[φ] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A -> B) (h₁ h₂ h₃ h₄)
  statement: ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : A -> B) (h₁ h₂ h₃ h₄)
  结论: ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : A -> B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) = f :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄)
  statement: (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) = f
  proof: by
  rfl

中文:
定理 mk_coe
  条件: (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄)
  结论: (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) = f
  证明: by
  rfl
-/
theorem mk_coe (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) = f := by
  rfl

/--
lemma `addHomMk_coe` / 引理 `addHomMk_coe`

English:
lemma addHomMk_coe
  given: (f : A ->ₛₙₐ[φ] B)
  statement: AddHom.mk f (map_add f) = f
  proof: rfl

@[simp]

中文:
引理 addHomMk_coe
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: AddHom.mk f (map_add f) = f
  证明: rfl

@[simp]
-/
@[simp] lemma addHomMk_coe (f : A ->ₛₙₐ[φ] B) : AddHom.mk f (map_add f) = f := rfl

@[simp]
/--
theorem `toDistribMulActionHom_eq_coe` / 定理 `toDistribMulActionHom_eq_coe`

English:
theorem toDistribMulActionHom_eq_coe
  given: (f : A ->ₛₙₐ[φ] B)
  statement: f.toDistribMulActionHom = ↑f
  proof: rfl

@[simp]

中文:
定理 toDistribMulActionHom_eq_coe
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: f.toDistribMulActionHom = ↑f
  证明: rfl

@[simp]
-/
theorem toDistribMulActionHom_eq_coe (f : A ->ₛₙₐ[φ] B) : f.toDistribMulActionHom = ↑f :=
  rfl

@[simp]
/--
theorem `toMulHom_eq_coe` / 定理 `toMulHom_eq_coe`

English:
theorem toMulHom_eq_coe
  given: (f : A ->ₛₙₐ[φ] B)
  statement: f.toMulHom = ↑f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toMulHom_eq_coe
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: f.toMulHom = ↑f
  证明: rfl

@[simp, norm_cast]
-/
theorem toMulHom_eq_coe (f : A ->ₛₙₐ[φ] B) : f.toMulHom = ↑f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_to_distribMulActionHom` / 定理 `coe_to_distribMulActionHom`

English:
theorem coe_to_distribMulActionHom
  given: (f : A ->ₛₙₐ[φ] B)
  statement: ⇑(f : A ->ₑ+[φ] B) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_to_distribMulActionHom
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: ⇑(f : A ->ₑ+[φ] B) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_to_distribMulActionHom (f : A ->ₛₙₐ[φ] B) : ⇑(f : A ->ₑ+[φ] B) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_to_mulHom` / 定理 `coe_to_mulHom`

English:
theorem coe_to_mulHom
  given: (f : A ->ₛₙₐ[φ] B)
  statement: ⇑(f : A ->ₙ* B) = f
  proof: rfl

中文:
定理 coe_to_mulHom
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: ⇑(f : A ->ₙ* B) = f
  证明: rfl
-/
theorem coe_to_mulHom (f : A ->ₛₙₐ[φ] B) : ⇑(f : A ->ₙ* B) = f :=
  rfl

/--
theorem `to_distribMulActionHom_injective` / 定理 `to_distribMulActionHom_injective`

English:
theorem to_distribMulActionHom_injective
  statement: {f g : A ->ₛₙₐ[φ] B}
  proof: by
  ext a
  exact DistribMulActionHom.congr_fun h a

中文:
定理 to_distribMulActionHom_injective
  结论: {f g : A ->ₛₙₐ[φ] B}
  证明: by
  ext a
  exact DistribMulActionHom.congr_fun h a

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.congr_fun, congr_fun
-/
theorem to_distribMulActionHom_injective {f g : A ->ₛₙₐ[φ] B}
    (h : (f : A ->ₑ+[φ] B) = (g : A ->ₑ+[φ] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a

/--
theorem `to_mulHom_injective` / 定理 `to_mulHom_injective`

English:
theorem to_mulHom_injective
  given: {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₙ* B) = (g : A ->ₙ* B))
  statement: f = g
  proof: by
  ext a
  exact DFunLike.congr_fun h a

@[norm_cast]

中文:
定理 to_mulHom_injective
  条件: {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₙ* B) = (g : A ->ₙ* B))
  结论: f = g
  证明: by
  ext a
  exact DFunLike.congr_fun h a

@[norm_cast]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem to_mulHom_injective {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₙ* B) = (g : A ->ₙ* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a

@[norm_cast]
/--
theorem `coe_distribMulActionHom_mk` / 定理 `coe_distribMulActionHom_mk`

English:
theorem coe_distribMulActionHom_mk
  given: (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄)
  proof: by
  rfl

@[norm_cast]

中文:
定理 coe_distribMulActionHom_mk
  条件: (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄)
  证明: by
  rfl

@[norm_cast]
-/
theorem coe_distribMulActionHom_mk (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) : A ->ₑ+[φ] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩ := by
  rfl

@[norm_cast]
/--
theorem `coe_mulHom_mk` / 定理 `coe_mulHom_mk`

English:
theorem coe_mulHom_mk
  given: (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄)
  proof: by
  rfl

@[simp] -- Marked as `@[simp]` because `MulActionSemiHomClass.map_smulₛₗ` can't be.

中文:
定理 coe_mulHom_mk
  条件: (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄)
  证明: by
  rfl

@[simp] -- Marked as `@[simp]` because `MulActionSemiHomClass.map_smulₛₗ` can't be.
-/
theorem coe_mulHom_mk (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) : A ->ₙ* B) = ⟨f, h₄⟩ := by
  rfl

@[simp] -- Marked as `@[simp]` because `MulActionSemiHomClass.map_smulₛₗ` can't be.
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (f : A ->ₛₙₐ[φ] B) (c : R) (x : A)
  statement: f (c • x) = (φ c) • f x
  proof: map_smulₛₗ _ _ _

中文:
定理 map_smul
  条件: (f : A ->ₛₙₐ[φ] B) (c : R) (x : A)
  结论: f (c • x) = (φ c) • f x
  证明: map_smulₛₗ _ _ _
-/
protected theorem map_smul (f : A ->ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x :=
  map_smulₛₗ _ _ _

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : A ->ₛₙₐ[φ] B) (x y : A)
  statement: f (x + y) = f x + f y
  proof: map_add _ _ _

中文:
定理 map_add
  条件: (f : A ->ₛₙₐ[φ] B) (x y : A)
  结论: f (x + y) = f x + f y
  证明: map_add _ _ _
-/
protected theorem map_add (f : A ->ₛₙₐ[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : A ->ₛₙₐ[φ] B) (x y : A)
  statement: f (x * y) = f x * f y
  proof: map_mul _ _ _

中文:
定理 map_mul
  条件: (f : A ->ₛₙₐ[φ] B) (x y : A)
  结论: f (x * y) = f x * f y
  证明: map_mul _ _ _
-/
protected theorem map_mul (f : A ->ₛₙₐ[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul _ _ _

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : A ->ₛₙₐ[φ] B)
  statement: f 0 = 0
  proof: map_zero _

中文:
定理 map_zero
  条件: (f : A ->ₛₙₐ[φ] B)
  结论: f 0 = 0
  证明: map_zero _
-/
protected theorem map_zero (f : A ->ₛₙₐ[φ] B) : f 0 = 0 :=
  map_zero _

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  body: { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: (R A : 类型) [Monoid R] [NonUnitalNonAssocSemiring A]
  定义体: { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp, norm_cast]
-/
protected def id (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A ->ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(NonUnitalAlgHom.id R A) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(NonUnitalAlgHom.id R A) = id
  证明: rfl
-/
theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (A ->ₛₙₐ[φ] B)
  body: ⟨{ (0 : A ->ₑ+[φ] B) with map_mul' := by simp }⟩

中文:
实例 :
  签名: Zero (A ->ₛₙₐ[φ] B)
  定义体: ⟨{ (0 : A ->ₑ+[φ] B) with map_mul' := by simp }⟩

Depends on / 依赖: map_mul
-/
instance : Zero (A ->ₛₙₐ[φ] B) :=
  ⟨{ (0 : A ->ₑ+[φ] B) with map_mul' := by simp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (A ->ₙₐ[R] A)
  body: ⟨NonUnitalAlgHom.id R A⟩

@[simp]

中文:
实例 :
  签名: One (A ->ₙₐ[R] A)
  定义体: ⟨NonUnitalAlgHom.id R A⟩

@[simp]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.id
-/
instance : One (A ->ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : A ->ₛₙₐ[φ] B) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : A ->ₛₙₐ[φ] B) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : A ->ₛₙₐ[φ] B) = 0 :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : A ->ₙₐ[R] A) : A -> A) = id
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : A ->ₙₐ[R] A) : A -> A) = id
  证明: rfl
-/
theorem coe_one : ((1 : A ->ₙₐ[R] A) : A -> A) = id :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (a : A)
  statement: (0 : A ->ₛₙₐ[φ] B) a = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (a : A)
  结论: (0 : A ->ₛₙₐ[φ] B) a = 0
  证明: rfl
-/
theorem zero_apply (a : A) : (0 : A ->ₛₙₐ[φ] B) a = 0 :=
  rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : A)
  statement: (1 : A ->ₙₐ[R] A) a = a
  proof: rfl

中文:
定理 one_apply
  条件: (a : A)
  结论: (1 : A ->ₙₐ[R] A) a = a
  证明: rfl
-/
theorem one_apply (a : A) : (1 : A ->ₙₐ[R] A) a = a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ->ₛₙₐ[φ] B)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (A ->ₛₙₐ[φ] B)
  定义体: ⟨0⟩
-/
instance : Inhabited (A ->ₛₙₐ[φ] B) :=
  ⟨0⟩

variable {φ' : S ->* R} {ψ : S ->* T} {χ : R ->* T}

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ]
  body: { (f : B ->ₙ* C).comp (g : A ->ₙ* B), (f : B ->ₑ+[ψ] C).comp (g : A ->ₑ+[φ] B) with }

@[simp, norm_cast]

中文:
定义 comp
  签名: (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ]
  定义体: { (f : B ->ₙ* C).comp (g : A ->ₙ* B), (f : B ->ₑ+[ψ] C).comp (g : A ->ₑ+[φ] B) with }

@[simp, norm_cast]
-/
def comp (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A ->ₛₙₐ[χ] C :=
  { (f : B ->ₙ* C).comp (g : A ->ₙ* B), (f : B ->ₑ+[ψ] C).comp (g : A ->ₑ+[φ] B) with }

@[simp, norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ]
  proof: rfl

中文:
定理 coe_comp
  条件: (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ]
  证明: rfl
-/
theorem coe_comp (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A)
  proof: rfl

中文:
定理 comp_apply
  条件: (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A)
  证明: rfl
-/
theorem comp_apply (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := rfl

variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : A ->ₙₐ[R] B₁) (g : B₁ -> A)
  body: { (f : A ->ₙ* B₁).inverse g h₁ h₂, (f : A ->+[R] B₁).inverse g h₁ h₂ with }

@[simp]

中文:
定义 inverse
  签名: (f : A ->ₙₐ[R] B₁) (g : B₁ -> A)
  定义体: { (f : A ->ₙ* B₁).inverse g h₁ h₂, (f : A ->+[R] B₁).inverse g h₁ h₂ with }

@[simp]

Depends on / 依赖: inverse
-/
def inverse (f : A ->ₙₐ[R] B₁) (g : B₁ -> A)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ ->ₙₐ[R] A :=
  { (f : A ->ₙ* B₁).inverse g h₁ h₂, (f : A ->+[R] B₁).inverse g h₁ h₂ with }

@[simp]
/--
theorem `coe_inverse` / 定理 `coe_inverse`

English:
theorem coe_inverse
  statement: (f : A ->ₙₐ[R] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f)
  proof: rfl

中文:
定理 coe_inverse
  结论: (f : A ->ₙₐ[R] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f)
  证明: rfl
-/
theorem coe_inverse (f : A ->ₙₐ[R] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B₁ -> A) = g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inverse'` / `inverse'` 的定义

English:
definition inverse'
  signature: (f : A ->ₛₙₐ[φ] B) (g : B -> A)
  body: { (f : A ->ₙ* B).inverse g h₁ h₂, (f : A ->ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero]; rw [h₁]
    map_add' := fun x y => by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x]; rw

中文:
定义 inverse'
  签名: (f : A ->ₛₙₐ[φ] B) (g : B -> A)
  定义体: { (f : A ->ₙ* B).inverse g h₁ h₂, (f : A ->ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero]; rw [h₁]
    map_add' := fun x y => by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x]; rw

Depends on / 依赖: MulHom, MulHom.inverse_apply, MulHom.toFun_eq_coe, f.map_zero, inverse, inverse_apply, map_add, map_zero, toFun_eq_coe
-/
def inverse' (f : A ->ₛₙₐ[φ] B) (g : B -> A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B ->ₛₙₐ[φ'] A :=
  { (f : A ->ₙ* B).inverse g h₁ h₂, (f : A ->ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero]; rw [h₁]
    map_add' := fun x y => by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x]; rw [← h₂ y]; rw [← map_add]; rw [h₁]; rw [h₂]; rw [h₂] }

@[simp]
/--
theorem `coe_inverse'` / 定理 `coe_inverse'`

English:
theorem coe_inverse'
  statement: (f : A ->ₛₙₐ[φ] B) (g : B -> A)
  proof: rfl

中文:
定理 coe_inverse'
  结论: (f : A ->ₛₙₐ[φ] B) (g : B -> A)
  证明: rfl
-/
theorem coe_inverse' (f : A ->ₛₙₐ[φ] B) (g : B -> A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse' f g k h₁ h₂ : B -> A) = g :=
  rfl

/-! ### Operations on the product type

Note that much of this is copied from [`LinearAlgebra/Prod`](../../LinearAlgebra/Prod). -/


section Prod

variable (R A B)
variable [DistribMulAction R B]

/-- The first projection of a product is a non-unital algebra homomorphism. -/
@[simps toFun]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : A × B ->ₙₐ[R] A where
  body: Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 fst
  签名: : A × B ->ₙₐ[R] A where
  定义体: Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Prod.fst
-/
def fst : A × B ->ₙₐ[R] A where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

/-- The second projection of a product is a non-unital algebra homomorphism. -/
@[simps toFun]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : A × B ->ₙₐ[R] B where
  body: Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 snd
  签名: : A × B ->ₙₐ[R] B where
  定义体: Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Prod.snd
-/
def snd : A × B ->ₙₐ[R] B where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

variable {R A B}
variable [DistribMulAction R C]

set_option backward.isDefEq.respectTransparency false in
/-- The prod of two morphisms is a morphism. -/
@[simps toFun]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  body: Function.prod f g
  map_zero' := by simp only [Function.prod_apply, Prod.mk_zero_zero, map_zero]
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Function.prod_apply, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Function.prod_

中文:
定义 prod
  签名: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  定义体: Function.prod f g
  map_zero' := by simp only [Function.prod_apply, Prod.mk_zero_zero, map_zero]
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Function.prod_apply, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Function.prod_

Depends on / 依赖: Function, Function.prod
-/
def prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : A ->ₙₐ[R] B × C where
  toFun := Function.prod f g
  map_zero' := by simp only [Function.prod_apply, Prod.mk_zero_zero, map_zero]
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Function.prod_apply, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Function.prod_apply, map_smul, MonoidHom.id_apply, Prod.smul_mk]

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  结论: ⇑(f.prod g) = Function.prod f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  given: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  statement: (fst R B C).comp (prod f g) = f
  proof: by
  rfl

@[simp]

中文:
定理 fst_prod
  条件: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  结论: (fst R B C).comp (prod f g) = f
  证明: by
  rfl

@[simp]
-/
theorem fst_prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  rfl

@[simp]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  given: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  statement: (snd R B C).comp (prod f g) = g
  proof: by
  rfl

@[simp]

中文:
定理 snd_prod
  条件: (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C)
  结论: (snd R B C).comp (prod f g) = g
  证明: by
  rfl

@[simp]
-/
theorem snd_prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  rfl

@[simp]
/--
theorem `prod_fst_snd` / 定理 `prod_fst_snd`

English:
theorem prod_fst_snd
  statement: prod (fst R A B) (snd R A B) = 1
  proof: coe_injective Function.prod_fst_snd

中文:
定理 prod_fst_snd
  结论: prod (fst R A B) (snd R A B) = 1
  证明: coe_injective Function.prod_fst_snd

Depends on / 依赖: Function, Function.prod_fst_snd, coe_injective, prod_fst_snd
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  coe_injective Function.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (A ->ₙₐ[R] B) × (A ->ₙₐ[R] C) ≃ (A ->ₙₐ[R] B × C) where
  body: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

中文:
定义 prodEquiv
  签名: : (A ->ₙₐ[R] B) × (A ->ₙₐ[R] C) ≃ (A ->ₙₐ[R] B × C) where
  定义体: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
-/
def prodEquiv : (A ->ₙₐ[R] B) × (A ->ₙₐ[R] C) ≃ (A ->ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

variable (R A B)

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : A ->ₙₐ[R] A × B
  body: prod 1 0

中文:
定义 inl
  签名: : A ->ₙₐ[R] A × B
  定义体: prod 1 0
-/
def inl : A ->ₙₐ[R] A × B :=
  prod 1 0

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : B ->ₙₐ[R] A × B
  body: prod 0 1

中文:
定义 inr
  签名: : B ->ₙₐ[R] A × B
  定义体: prod 0 1
-/
def inr : B ->ₙₐ[R] A × B :=
  prod 0 1

variable {R A B}

@[simp]
/--
theorem `coe_inl` / 定理 `coe_inl`

English:
theorem coe_inl
  statement: (inl R A B : A -> A × B) = fun x => (x, 0)
  proof: rfl

中文:
定理 coe_inl
  结论: (inl R A B : A -> A × B) = fun x => (x, 0)
  证明: rfl
-/
theorem coe_inl : (inl R A B : A -> A × B) = fun x => (x, 0) :=
  rfl

/--
theorem `inl_apply` / 定理 `inl_apply`

English:
theorem inl_apply
  given: (x : A)
  statement: inl R A B x = (x, 0)
  proof: rfl

@[simp]

中文:
定理 inl_apply
  条件: (x : A)
  结论: inl R A B x = (x, 0)
  证明: rfl

@[simp]
-/
theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl

@[simp]
/--
theorem `coe_inr` / 定理 `coe_inr`

English:
theorem coe_inr
  statement: (inr R A B : B -> A × B) = Prod.mk 0
  proof: rfl

中文:
定理 coe_inr
  结论: (inr R A B : B -> A × B) = Prod.mk 0
  证明: rfl
-/
theorem coe_inr : (inr R A B : B -> A × B) = Prod.mk 0 :=
  rfl

/--
theorem `inr_apply` / 定理 `inr_apply`

English:
theorem inr_apply
  given: (x : B)
  statement: inr R A B x = (0, x)
  proof: rfl

中文:
定理 inr_apply
  条件: (x : B)
  结论: inr R A B x = (0, x)
  证明: rfl
-/
theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl

end Prod

end NonUnitalAlgHom

/-! ### Interaction with `AlgHom` -/

namespace AlgHom

variable {F R : Type*} [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) [FunLike F A B] [AlgHomClass F R A B] : NonUnitalAlgHomClass F R A B :=
  { ‹AlgHomClass F R A B› with map_smulₛₗ := map_smul }

/-- A unital morphism of algebras is a `NonUnitalAlgHom`. -/
@[coe]
/--
Definition of `toNonUnitalAlgHom` / `toNonUnitalAlgHom` 的定义

English:
definition toNonUnitalAlgHom
  signature: (f : A ->ₐ[R] B)
  body: { f with map_smul' := map_smul f }

中文:
定义 toNonUnitalAlgHom
  签名: (f : A ->ₐ[R] B)
  定义体: { f with map_smul' := map_smul f }

Depends on / 依赖: map_smul
-/
def toNonUnitalAlgHom (f : A ->ₐ[R] B) : A ->ₙₐ[R] B :=
  { f with map_smul' := map_smul f }

/--
Instance `NonUnitalAlgHom.hasCoe` / 实例 `NonUnitalAlgHom.hasCoe`

English:
instance NonUnitalAlgHom.hasCoe
  signature: : CoeOut (A ->ₐ[R] B) (A ->ₙₐ[R] B)
  body: ⟨toNonUnitalAlgHom⟩

@[simp]

中文:
实例 NonUnitalAlgHom.hasCoe
  签名: : CoeOut (A ->ₐ[R] B) (A ->ₙₐ[R] B)
  定义体: ⟨toNonUnitalAlgHom⟩

@[simp]

Depends on / 依赖: toNonUnitalAlgHom
-/
instance NonUnitalAlgHom.hasCoe : CoeOut (A ->ₐ[R] B) (A ->ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

@[simp]
/--
theorem `toNonUnitalAlgHom_eq_coe` / 定理 `toNonUnitalAlgHom_eq_coe`

English:
theorem toNonUnitalAlgHom_eq_coe
  given: (f : A ->ₐ[R] B)
  statement: f.toNonUnitalAlgHom = f
  proof: rfl

中文:
定理 toNonUnitalAlgHom_eq_coe
  条件: (f : A ->ₐ[R] B)
  结论: f.toNonUnitalAlgHom = f
  证明: rfl
-/
theorem toNonUnitalAlgHom_eq_coe (f : A ->ₐ[R] B) : f.toNonUnitalAlgHom = f :=
  rfl

end AlgHom

section RestrictScalars

namespace NonUnitalAlgHom

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : A ->ₙₐ[S] B)
  body: { (f : A ->ₙ+* B) with
    map_smul' := fun r x => by have := map_smul f (r • 1) x; simpa }

@[simp]

中文:
定义 restrictScalars
  签名: (f : A ->ₙₐ[S] B)
  定义体: { (f : A ->ₙ+* B) with
    map_smul' := fun r x => by have := map_smul f (r • 1) x; simpa }

@[simp]

Depends on / 依赖: map_smul
-/
def restrictScalars (f : A ->ₙₐ[S] B) : A ->ₙₐ[R] B :=
  { (f : A ->ₙ+* B) with
    map_smul' := fun r x => by have := map_smul f (r • 1) x; simpa }

@[simp]
/--
lemma `restrictScalars_apply` / 引理 `restrictScalars_apply`

English:
lemma restrictScalars_apply
  given: (f : A ->ₙₐ[S] B) (x : A)
  statement: f.restrictScalars R x = f x
  proof: rfl

中文:
引理 restrictScalars_apply
  条件: (f : A ->ₙₐ[S] B) (x : A)
  结论: f.restrictScalars R x = f x
  证明: rfl
-/
lemma restrictScalars_apply (f : A ->ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

/--
lemma `coe_restrictScalars` / 引理 `coe_restrictScalars`

English:
lemma coe_restrictScalars
  given: (f : A ->ₙₐ[S] B)
  statement: (f.restrictScalars R : A ->ₙ+* B) = f
  proof: rfl

中文:
引理 coe_restrictScalars
  条件: (f : A ->ₙₐ[S] B)
  结论: (f.restrictScalars R : A ->ₙ+* B) = f
  证明: rfl
-/
lemma coe_restrictScalars (f : A ->ₙₐ[S] B) : (f.restrictScalars R : A ->ₙ+* B) = f := rfl

/--
lemma `coe_restrictScalars'` / 引理 `coe_restrictScalars'`

English:
lemma coe_restrictScalars'
  given: (f : A ->ₙₐ[S] B)
  statement: (f.restrictScalars R : A -> B) = f
  proof: rfl

中文:
引理 coe_restrictScalars'
  条件: (f : A ->ₙₐ[S] B)
  结论: (f.restrictScalars R : A -> B) = f
  证明: rfl
-/
lemma coe_restrictScalars' (f : A ->ₙₐ[S] B) : (f.restrictScalars R : A -> B) = f := rfl

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h => ext (congr_fun h :)

中文:
定理 restrictScalars_injective
  证明: fun _ _ h => ext (congr_fun h :)

Depends on / 依赖: congr_fun
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ->ₙₐ[S] B) -> A ->ₙₐ[R] B) :=
  fun _ _ h => ext (congr_fun h :)

end NonUnitalAlgHom

end RestrictScalars
