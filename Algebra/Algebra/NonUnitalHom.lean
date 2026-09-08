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

/-- A morphism respecting addition, multiplication, and scalar multiplication
(denoted as `A →ₛₙₐ[φ] B`, or `A →ₙₐ[R] B` when `φ` is the identity on `R`).
When these arise from algebra structures, this is the same
as a not-necessarily-unital morphism of algebras. -/
/-
**NonUnitalAlgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u} →   {S : Type u₁} →     [inst : Monoid R] →       [inst_1 : M
onoid S] →         (R →* S) →           (A : Type v) →             (B : Type w) 
→               [inst_2 : NonUnitalNonAssocSemiring A] →                 [Distri
bMulAction R A] → [inst : NonUnitalNonAssocSemiring B] → [DistribMulAction S B] 
→ Type (max v w)
参数：R →* S；A : Type v；B : Type w；max v w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism respecting addition, multiplication, and scalar multiplication
(denoted as `A →ₛₙₐ[φ] B`, or `A →ₙₐ[R] B` when `φ` is the identity on `R`).
When these arise from algebra structures, this is the same
as a not-necessarily-unital morphism of algebras.
-/
structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R →* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A →ₑ+[φ] B, A →ₙ* B

@[inherit_doc NonUnitalAlgHom]
infixr:25 " →ₙₐ " => NonUnitalAlgHom _

@[inherit_doc]
notation:25 A " →ₛₙₐ[" φ "] " B => NonUnitalAlgHom φ A B

@[inherit_doc]
notation:25 A " →ₙₐ[" R "] " B => NonUnitalAlgHom (MonoidHom.id R) A B

attribute [nolint docBlame] NonUnitalAlgHom.toMulHom

/-- `NonUnitalAlgSemiHomClass F φ A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B` which are equivariant with respect to `φ`. -/
/-
**NonUnitalAlgSemiHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   {R : outParam (Type u_2)} →     {S : outParam (Type u_3
)} →       [inst : Monoid R] →         [inst_1 : Monoid S] →           outParam 
(R →* S) →             (A : outParam (Type u_4)) →               (B : outParam (
Type u_5)) →                 [inst_2 : NonUnitalNonAssocSemiring A] →           
        [inst_3 : NonUnitalNonAssocSemiring B] →                     [DistribMul
Action R A] → [DistribMulAction S B] → [FunLike F A B] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalAlgSemiHomClass F φ A B` asserts `F` is a type of bundled algebra homo
morphisms
from `A` to `B` which are equivariant with respect to `φ`.
-/
class NonUnitalAlgSemiHomClass (F : Type*) {R S : outParam Type*} [Monoid R] [Monoid S]
    (φ : outParam (R →* S)) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction S B] [FunLike F A B] : Prop
    extends DistribMulActionSemiHomClass F φ A B, MulHomClass F A B

/-- `NonUnitalAlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B` which are `R`-linear.

  This is an abbreviation to `NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B` -/
/-
**NonUnitalAlgHomClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NonUnitalAlgHomClass (F : Type*) (R A B : outParam Type*) [Monoid R] [NonU
nitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [DistribMulAction R A] [D
istribMulAction R B] [FunLike F A B]
参数：F : Type*；R A B : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalAlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorp
hisms
from `A` to `B` which are `R`-linear.

  This is an abbreviation to `NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B`
-/
abbrev NonUnitalAlgHomClass (F : Type*) (R A B : outParam Type*)
    [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction R B] [FunLike F A B] :=
  NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B

namespace NonUnitalAlgHomClass

-- See note [lower instance priority]
/-
**NonUnitalAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toNonUnitalRingHomClass
    {F R S A B : Type*} {_ : Monoid R} {_ : Monoid S} {φ : outParam (R →* S)}
    {_ : NonUnitalNonAssocSemiring A} [DistribMulAction R A]
    {_ : NonUnitalNonAssocSemiring B} [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] : NonUnitalRingHomClass F A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with }

variable [Semiring R] [Semiring S] {φ : R →+* S}
  {A B : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module S B]

-- see Note [lower instance priority]
/-
**NonUnitalAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {F R S A B : Type*}
    {_ : Semiring R} {_ : Semiring S} {φ : R →+* S}
    {_ : NonUnitalSemiring A} {_ : NonUnitalSemiring B} [Module R A] [Module S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass (R := R) (S := S) F φ A B] :
    SemilinearMapClass F φ A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with map_smulₛₗ := map_smulₛₗ }
/-
**NonUnitalAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {F : Type*} [FunLike F A B] [Module R B] [NonUnitalAlgHomClass F R A B] :
    LinearMapClass F R A B :=
  { ‹NonUnitalAlgHomClass F R A B› with map_smulₛₗ := map_smulₛₗ }

/-- Turn an element of a type `F` satisfying `NonUnitalAlgSemiHomClass F φ A B` into an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[φ] B`. -/
@[coe]
/-
**NonUnitalAlgHomClass.toNonUnitalAlgSemiHom** 是 Mathlib 中的一个定义，位于命名空间 `NonUnita
lAlgHomClass`。
形式化陈述：toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R ->* S} 
{A B : Type*} [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [NonUnitalNon
AssocSemiring B] [DistribMulAction S B] [FunLike F A B] [NonUnitalAlgSemiHomClas
s F φ A B] (f : F) : A ->ₛₙₐ[φ] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalRingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonU
nitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+*
 β), self.toFun …
· 使用定理 `NonUnitalRingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonUn
italNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+* 
β) (x y : α), s…

--- 原说明 ---
Turn an element of a type `F` satisfying `NonUnitalAlgSemiHomClass F φ A B` into
 an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[
φ] B`.
-/
def toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R →* S} {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) : A →ₛₙₐ[φ] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }
/-
**NonUnitalAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F R S A B : Type*} [Monoid R] [Monoid S] {φ : R →* S}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] :
      CoeTC F (A →ₛₙₐ[φ] B) :=
  ⟨toNonUnitalAlgSemiHom⟩

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an actual
@[coe]
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[R] B`. -/
/-
**NonUnitalAlgHomClass.toNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlg
HomClass`。
形式化陈述：toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*} [NonUnitalNonAsso
cSemiring A] [DistribMulAction R A] [NonUnitalNonAssocSemiring B] [DistribMulAct
ion R B] [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A ->ₙₐ[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonU
nitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+*
 β), self.toFun …
· 使用定理 `NonUnitalRingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonUn
italNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+* 
β) (x y : α), s…

--- 原说明 ---
Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an 
actual
@[coe]
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[
R] B`.
-/
def toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }
/-
**NonUnitalAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

end NonUnitalAlgHomClass

namespace NonUnitalAlgHom

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)
variable (A : Type v) (B : Type w) (C : Type w₁)
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

/-
**NonUnitalAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[simp]
/-
**NonUnitalAlgHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：toFun_eq_coe (f : A ->ₛₙₐ[φ] B) : f.toFun = ⇑f
参数：f : A ->ₛₙₐ[φ] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f :=
  rfl

/-- See Note [custom simps projection] -/
/-
**NonUnitalAlgHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom.Simps`。
形式化陈述：{R : Type u} →   {S : Type u₁} →     [inst : Monoid R] →       [inst_1 : M
onoid S] →         (φ : R →* S) →           (A : Type v) →             (B : Type
 w) →               [inst_2 : NonUnitalNonAssocSemiring A] →                 [in
st_3 : DistribMulAction R A] →                   [inst_4 : NonUnitalNonAssocSemi
ring B] → [inst_5 : DistribMulAction S B] → (A →ₛₙₐ[φ] B) → A → B
参数：φ : R →* S；A : Type v；B : Type w；A →ₛₙₐ[φ] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (f : A →ₛₙₐ[φ] B) : A → B := f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun → apply, -toDistribMulActionHom)

variable {φ A B C}
@[simp]
/-
**NonUnitalAlgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：∀ {R : Type u} {S : Type u₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R 
→* S} {A : Type v} {B : Type w}   [inst_2 : NonUnitalNonAssocSemiring A] [inst_3
 : DistribMulAction R A] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : Dist
ribMulAction S B] {F : Type u_2} [inst_6 : FunLike F A B] [inst_7 : NonUnitalAlg
SemiHomClass F φ A B]   (f : F), ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f :=
  rfl
/-
**NonUnitalAlgHom.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_injective : @Function.Injective (A ->ₛₙₐ[φ] B) (A -> B) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
/-
**NonUnitalAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective := coe_injective
/-
**NonUnitalAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalAlgSemiHomClass (A →ₛₙₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'

@[ext]
/-
**NonUnitalAlgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.coe_injective`：coe_injective : @Function.Injective (A ->
ₛₙₐ[φ] B) (A -> B) (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : A →ₛₙₐ[φ] B} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
/-
**NonUnitalAlgHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：congr_fun {f g : A ->ₛₙₐ[φ] B} (h : f = g) (x : A) : f x = g x
参数：h : f = g；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_fun {f g : A →ₛₙₐ[φ] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl

@[simp]
/-
**NonUnitalAlgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_mk (f : A -> B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ]
 B) = f
参数：f : A -> B；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f :=
  rfl

@[simp]
/-
**NonUnitalAlgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：mk_coe (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->ₛ
ₙₐ[φ] B) = f
参数：f : A ->ₛₙₐ[φ] B；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  rfl
/-
**NonUnitalAlgHom.addHomMk_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：∀ {R : Type u} {S : Type u₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R 
→* S} {A : Type v} {B : Type w}   [inst_2 : NonUnitalNonAssocSemiring A] [inst_3
 : DistribMulAction R A] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : Dist
ribMulAction S B] (f : A →ₛₙₐ[φ] B), { toFun := ⇑f, map_add' := ⋯ } = ↑f
参数：f : A →ₛₙₐ[φ] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
@[simp] lemma addHomMk_coe (f : A →ₛₙₐ[φ] B) : AddHom.mk f (map_add f) = f := rfl

@[simp]
/-
**NonUnitalAlgHom.toDistribMulActionHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talAlgHom`。
形式化陈述：toDistribMulActionHom_eq_coe (f : A ->ₛₙₐ[φ] B) : f.toDistribMulActionHom 
= ↑f
参数：f : A ->ₛₙₐ[φ] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDistribMulActionHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toDistribMulActionHom = ↑f :=
  rfl

@[simp]
/-
**NonUnitalAlgHom.toMulHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：toMulHom_eq_coe (f : A ->ₛₙₐ[φ] B) : f.toMulHom = ↑f
参数：f : A ->ₛₙₐ[φ] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toMulHom = ↑f :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalAlgHom.coe_to_distribMulActionHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lAlgHom`。
形式化陈述：coe_to_distribMulActionHom (f : A ->ₛₙₐ[φ] B) : ⇑(f : A ->ₑ+[φ] B) = f
参数：f : A ->ₛₙₐ[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
theorem coe_to_distribMulActionHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₑ+[φ] B) = f :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalAlgHom.coe_to_mulHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_to_mulHom (f : A ->ₛₙₐ[φ] B) : ⇑(f : A ->ₙ* B) = f
参数：f : A ->ₛₙₐ[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
theorem coe_to_mulHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₙ* B) = f :=
  rfl
/-
**NonUnitalAlgHom.to_distribMulActionHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `No
nUnitalAlgHom`。
形式化陈述：to_distribMulActionHom_injective {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₑ+[φ] 
B) = (g : A ->ₑ+[φ] B)) : f = g
参数：h : (f : A ->ₑ+[φ] B) = (g : A ->ₑ+[φ] B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalAlgHom.ext`：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `DistribMulActionHom.congr_fun`：∀ {M : Type u_1} [inst : Monoid M] {N : T
ype u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 : AddMonoid A] 
  [inst_3 : Distrib…
-/
theorem to_distribMulActionHom_injective {f g : A →ₛₙₐ[φ] B}
    (h : (f : A →ₑ+[φ] B) = (g : A →ₑ+[φ] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a
/-
**NonUnitalAlgHom.to_mulHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom
`。
形式化陈述：to_mulHom_injective {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₙ* B) = (g : A ->ₙ*
 B)) : f = g
参数：h : (f : A ->ₙ* B) = (g : A ->ₙ* B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalAlgHom.ext`：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem to_mulHom_injective {f g : A →ₛₙₐ[φ] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a

@[norm_cast]
/-
**NonUnitalAlgHom.coe_distribMulActionHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lAlgHom`。
形式化陈述：coe_distribMulActionHom_mk (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : ((⟨⟨⟨f, h₁⟩,
 h₂, h₃⟩, h₄⟩ : A ->ₛₙₐ[φ] B) : A ->ₑ+[φ] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩
参数：f : A ->ₛₙₐ[φ] B；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
theorem coe_distribMulActionHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₑ+[φ] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩ := by
  rfl

@[norm_cast]
/-
**NonUnitalAlgHom.coe_mulHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_mulHom_mk (f : A ->ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩
 : A ->ₛₙₐ[φ] B) : A ->ₙ* B) = ⟨f, h₄⟩
参数：f : A ->ₛₙₐ[φ] B；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
theorem coe_mulHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  rfl

@[simp] -- Marked as `@[simp]` because `MulActionSemiHomClass.map_smulₛₗ` can't be.
/-
**NonUnitalAlgHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：∀ {R : Type u} {S : Type u₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R 
→* S} {A : Type v} {B : Type w}   [inst_2 : NonUnitalNonAssocSemiring A] [inst_3
 : DistribMulAction R A] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : Dist
ribMulAction S B] (f : A →ₛₙₐ[φ] B) (c : R) (x : A), f (c • x) = φ c • f x
参数：f : A →ₛₙₐ[φ] B；c : R；x : A；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `DistribMulActionSemiHomClass.toMulActionSemiHomClass`：∀ {F : Type u_10} 
{M : outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {
A : outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
protected theorem map_smul (f : A →ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x :=
  map_smulₛₗ _ _ _
/-
**NonUnitalAlgHom.map_add** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：∀ {R : Type u} {S : Type u₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R 
→* S} {A : Type v} {B : Type w}   [inst_2 : NonUnitalNonAssocSemiring A] [inst_3
 : DistribMulAction R A] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : Dist
ribMulAction S B] (f : A →ₛₙₐ[φ] B) (x y : A), f (x + y) = f x + f y
参数：f : A →ₛₙₐ[φ] B；x y : A；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
protected theorem map_add (f : A →ₛₙₐ[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _
/-
**NonUnitalAlgHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：∀ {R : Type u} {S : Type u₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R 
→* S} {A : Type v} {B : Type w}   [inst_2 : NonUnitalNonAssocSemiring A] [inst_3
 : DistribMulAction R A] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : Dist
ribMulAction S B] (f : A →ₛₙₐ[φ] B) (x y : A), f (x * y) = f x * f y
参数：f : A →ₛₙₐ[φ] B；x y : A；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
protected theorem map_mul (f : A →ₛₙₐ[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul _ _ _
/-
**NonUnitalAlgHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：∀ {R : Type u} {S : Type u₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R 
→* S} {A : Type v} {B : Type w}   [inst_2 : NonUnitalNonAssocSemiring A] [inst_3
 : DistribMulAction R A] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : Dist
ribMulAction S B] (f : A →ₛₙₐ[φ] B), f 0 = 0
参数：f : A →ₛₙₐ[φ] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
protected theorem map_zero (f : A →ₛₙₐ[φ] B) : f 0 = 0 :=
  map_zero _

/-- The identity map as a `NonUnitalAlgHom`. -/
/-
**NonUnitalAlgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：(R : Type u_2) →   (A : Type u_3) →     [inst : Monoid R] → [inst_1 : NonU
nitalNonAssocSemiring A] → [inst_2 : DistribMulAction R A] → A →ₙₐ[R] A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonU
nitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+*
 β), self.toFun …
· 使用定理 `NonUnitalRingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonUn
italNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+* 
β) (x y : α), s…

--- 原说明 ---
The identity map as a `NonUnitalAlgHom`.
-/
protected def id (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A →ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp, norm_cast]
/-
**NonUnitalAlgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_id : ⇑(NonUnitalAlgHom.id R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id :=
  rfl
/-
**NonUnitalAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (A →ₛₙₐ[φ] B) :=
  ⟨{ (0 : A →ₑ+[φ] B) with map_mul' := by simp }⟩
/-
**NonUnitalAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (A →ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩

@[simp]
/-
**NonUnitalAlgHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_zero : ⇑(0 : A ->ₛₙₐ[φ] B) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : A →ₛₙₐ[φ] B) = 0 :=
  rfl

@[simp]
/-
**NonUnitalAlgHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_one : ((1 : A ->ₙₐ[R] A) : A -> A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : A →ₙₐ[R] A) : A → A) = id :=
  rfl
/-
**NonUnitalAlgHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：zero_apply (a : A) : (0 : A ->ₛₙₐ[φ] B) a = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 :=
  rfl
/-
**NonUnitalAlgHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：one_apply (a : A) : (1 : A ->ₙₐ[R] A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a :=
  rfl
/-
**NonUnitalAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A →ₛₙₐ[φ] B) :=
  ⟨0⟩

variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}

/-- The composition of morphisms is a morphism. -/
/-
**NonUnitalAlgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：comp (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ
] : A ->ₛₙₐ[χ] C
参数：f : B ->ₛₙₐ[ψ] C；g : A ->ₛₙₐ[φ] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms is a morphism.
-/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C :=
  { (f : B →ₙ* C).comp (g : A →ₙ* B), (f : B →ₑ+[ψ] C).comp (g : A →ₑ+[φ] B) with }

@[simp, norm_cast]
/-
**NonUnitalAlgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_comp (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ
] : ⇑(f.comp g) = (⇑f) ∘ (⇑g)
参数：f : B ->ₛₙₐ[ψ] C；g : A ->ₛₙₐ[φ] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := rfl
/-
**NonUnitalAlgHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：comp_apply (f : B ->ₛₙₐ[ψ] C) (g : A ->ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ
 χ] (x : A) : f.comp g x = f (g x)
参数：f : B ->ₛₙₐ[ψ] C；g : A ->ₛₙₐ[φ] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := rfl

variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

/-- The inverse of a bijective morphism is a morphism. -/
/-
**NonUnitalAlgHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：inverse (f : A ->ₙₐ[R] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f) (
h₂ : Function.RightInverse g f) : B₁ ->ₙₐ[R] A
参数：f : A ->ₙₐ[R] B₁；g : B₁ -> A；h₁ : Function.LeftInverse g f；h₂ : Function.Righ
tInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective morphism is a morphism.
-/
def inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →ₙₐ[R] A :=
  { (f : A →ₙ* B₁).inverse g h₁ h₂, (f : A →+[R] B₁).inverse g h₁ h₂ with }

@[simp]
/-
**NonUnitalAlgHom.coe_inverse** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_inverse (f : A ->ₙₐ[R] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g 
f) (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B₁ -> A) = g
参数：f : A ->ₙₐ[R] B₁；g : B₁ -> A；h₁ : Function.LeftInverse g f；h₂ : Function.Righ
tInverse g f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B₁ → A) = g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of a bijective morphism is a morphism. -/
/-
**NonUnitalAlgHom.inverse'** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：inverse' (f : A ->ₛₙₐ[φ] B) (g : B -> A) (k : Function.RightInverse φ' φ) 
(h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B ->ₛₙₐ[φ'] A
参数：f : A ->ₛₙₐ[φ] B；g : B -> A；k : Function.RightInverse φ' φ；h₁ : Function.Left
Inverse g f；h₂ : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective morphism is a morphism.
-/
def inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B →ₛₙₐ[φ'] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero, h₁]
    map_add' := fun x y ↦ by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x, ← h₂ y, ← map_add, h₁, h₂, h₂] }

@[simp]
/-
**NonUnitalAlgHom.coe_inverse'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_inverse' (f : A ->ₛₙₐ[φ] B) (g : B -> A) (k : Function.RightInverse φ'
 φ) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : (inverse'
 f g k h₁ h₂ : B -> A) = g
参数：f : A ->ₛₙₐ[φ] B；g : B -> A；k : Function.RightInverse φ' φ；h₁ : Function.Left
Inverse g f；h₂ : Function.RightInverse g f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse' f g k h₁ h₂ : B → A) = g :=
  rfl

/-! ### Operations on the product type

Note that much of this is copied from [`LinearAlgebra/Prod`](../../LinearAlgebra/Prod). -/


section Prod

variable (R A B)
variable [DistribMulAction R B]

/-- The first projection of a product is a non-unital algebra homomorphism. -/
@[simps toFun]
/-
**NonUnitalAlgHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：fst : A × B ->ₙₐ[R] A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a product is a non-unital algebra homomorphism.
-/
def fst : A × B →ₙₐ[R] A where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

/-- The second projection of a product is a non-unital algebra homomorphism. -/
@[simps toFun]
/-
**NonUnitalAlgHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：snd : A × B ->ₙₐ[R] B where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a product is a non-unital algebra homomorphism.
-/
def snd : A × B →ₙₐ[R] B where
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
/-
**NonUnitalAlgHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : A ->ₙₐ[R] B × C where toFun
参数：f : A ->ₙₐ[R] B；g : A ->ₙₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prod of two morphisms is a morphism.
-/
def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : A →ₙₐ[R] B × C where
  toFun := Function.prod f g
  map_zero' := by simp only [Function.prod_apply, Prod.mk_zero_zero, map_zero]
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Function.prod_apply, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Function.prod_apply, map_smul, MonoidHom.id_apply, Prod.smul_mk]
/-
**NonUnitalAlgHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : ⇑(f.prod g) = Function.prod
 f g
参数：f : A ->ₙₐ[R] B；g : A ->ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/-
**NonUnitalAlgHom.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：fst_prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : (fst R B C).comp (prod f g)
 = f
参数：f : A ->ₙₐ[R] B；g : A ->ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  rfl

@[simp]
/-
**NonUnitalAlgHom.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：snd_prod (f : A ->ₙₐ[R] B) (g : A ->ₙₐ[R] C) : (snd R B C).comp (prod f g)
 = g
参数：f : A ->ₙₐ[R] B；g : A ->ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  rfl

@[simp]
/-
**NonUnitalAlgHom.prod_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：prod_fst_snd : prod (fst R A B) (snd R A B) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.coe_injective`：coe_injective : @Function.Injective (A ->
ₛₙₐ[φ] B) (A -> B) (↑)
· 使用定理 `Function.prod_fst_snd`：∀ {α : Type u_1} {β : Type u_2}, Function.prod Pr
od.fst Prod.snd = id
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  coe_injective Function.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/-
**NonUnitalAlgHom.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：prodEquiv : (A ->ₙₐ[R] B) × (A ->ₙₐ[R] C) ≃ (A ->ₙₐ[R] B × C) where toFun 
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same domain is equivalent to taking the 
product of
their codomains.
-/
def prodEquiv : (A →ₙₐ[R] B) × (A →ₙₐ[R] C) ≃ (A →ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

variable (R A B)

/-- The left injection into a product is a non-unital algebra homomorphism. -/
/-
**NonUnitalAlgHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：inl : A ->ₙₐ[R] A × B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left injection into a product is a non-unital algebra homomorphism.
-/
def inl : A →ₙₐ[R] A × B :=
  prod 1 0

/-- The right injection into a product is a non-unital algebra homomorphism. -/
/-
**NonUnitalAlgHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：inr : B ->ₙₐ[R] A × B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right injection into a product is a non-unital algebra homomorphism.
-/
def inr : B →ₙₐ[R] A × B :=
  prod 0 1

variable {R A B}

@[simp]
/-
**NonUnitalAlgHom.coe_inl** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_inl : (inl R A B : A -> A × B) = fun x => (x, 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl
/-
**NonUnitalAlgHom.inl_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：inl_apply (x : A) : inl R A B x = (x, 0)
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl

@[simp]
/-
**NonUnitalAlgHom.coe_inr** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：coe_inr : (inr R A B : B -> A × B) = Prod.mk 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl
/-
**NonUnitalAlgHom.inr_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：inr_apply (x : B) : inr R A B x = (0, x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [FunLike F A B] [AlgHomClass F R A B] : NonUnitalAlgHomClass F R A B :=
  { ‹AlgHomClass F R A B› with map_smulₛₗ := map_smul }

/-- A unital morphism of algebras is a `NonUnitalAlgHom`. -/
@[coe]
/-
**AlgHom.toNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toNonUnitalAlgHom (f : A ->ₐ[R] B) : A ->ₙₐ[R] B
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unital morphism of algebras is a `NonUnitalAlgHom`.
-/
def toNonUnitalAlgHom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
  { f with map_smul' := map_smul f }
/-
**AlgHom.NonUnitalAlgHom.hasCoe** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom.NonUnitalAlgHo
m`。
形式化陈述：{R : Type u_2} →   [inst : CommSemiring R] →     {A : Type u_3} →       {B
 : Type u_4} →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →
 [inst_3 : Algebra R A] → [inst_4 : Algebra R B] → CoeOut (A →ₐ[R] B) (A →ₙₐ[R] 
B)
参数：A →ₐ[R] B；A →ₙₐ[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NonUnitalAlgHom.hasCoe : CoeOut (A →ₐ[R] B) (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

@[simp]
/-
**AlgHom.toNonUnitalAlgHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toNonUnitalAlgHom_eq_coe (f : A ->ₐ[R] B) : f.toNonUnitalAlgHom = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalAlgHom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f :=
  rfl

end AlgHom

section RestrictScalars

namespace NonUnitalAlgHom

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital algebra homomorphism
over `S` can be viewed as a non-unital algebra homomorphism over `R`. -/
/-
**NonUnitalAlgHom.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgHom`。
形式化陈述：restrictScalars (f : A ->ₙₐ[S] B) : A ->ₙₐ[R] B
参数：f : A ->ₙₐ[S] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonU
nitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+*
 β), self.toFun …
· 使用定理 `NonUnitalRingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonUn
italNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+* 
β) (x y : α), s…

--- 原说明 ---
If a monoid `R` acts on another monoid `S`, then a non-unital algebra homomorphi
sm
over `S` can be viewed as a non-unital algebra homomorphism over `R`.
-/
def restrictScalars (f : A →ₙₐ[S] B) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    map_smul' := fun r x ↦ by have := map_smul f (r • 1) x; simpa }

@[simp]
/-
**NonUnitalAlgHom.restrictScalars_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgH
om`。
形式化陈述：restrictScalars_apply (f : A ->ₙₐ[S] B) (x : A) : f.restrictScalars R x = 
f x
参数：f : A ->ₙₐ[S] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_apply (f : A →ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
/-
**NonUnitalAlgHom.coe_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgHom
`。
形式化陈述：coe_restrictScalars (f : A ->ₙₐ[S] B) : (f.restrictScalars R : A ->ₙ+* B) 
= f
参数：f : A ->ₙₐ[S] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
lemma coe_restrictScalars (f : A →ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl
/-
**NonUnitalAlgHom.coe_restrictScalars'** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalAlgHo
m`。
形式化陈述：coe_restrictScalars' (f : A ->ₙₐ[S] B) : (f.restrictScalars R : A -> B) = 
f
参数：f : A ->ₙₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_restrictScalars' (f : A →ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl
/-
**NonUnitalAlgHom.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
AlgHom`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : (A ->ₙ
ₐ[S] B) -> A ->ₙₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.ext`：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `NonUnitalAlgHom.congr_fun`：congr_fun {f g : A ->ₛₙₐ[φ] B} (h : f = g) (x
 : A) : f x = g x
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₙₐ[S] B) → A →ₙₐ[R] B) :=
  fun _ _ h ↦ ext (congr_fun h :)

end NonUnitalAlgHom

end RestrictScalars

