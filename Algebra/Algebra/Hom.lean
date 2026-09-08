/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `AlgHom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notation

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

@[expose] public section

universe u v w u₁ v₁

/-- Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`. -/
/-
**AlgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) →     (B : Type w) →       [inst : CommSemir
ing R] →         [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] →
 [Algebra R B] → Type (max v w)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`.
-/
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

/-- Reinterpret an `AlgHom` as a `RingHom` -/
add_decl_doc AlgHom.toRingHom

@[inherit_doc AlgHom]
infixr:25 " →ₐ " => AlgHom _

@[inherit_doc]
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

/-- `AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`. -/
/-
**AlgHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [inst : CommSemiring R] →        
   [inst_1 : Semiring A] → [inst_2 : Semiring B] → [Algebra R A] → [Algebra R B]
 → [FunLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.
-/
class AlgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] : Prop
    extends RingHomClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

-- For now, don't replace `AlgHom.commutes` and `AlgHomClass.commutes` with the more generic lemma.
-- The file `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean` slows down by
-- 15% if we would do so (see benchmark on PR https://github.com/leanprover-community/mathlib4/pull/18040).
-- attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- see Note [lower instance priority]
/-
**AlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }

/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
/-
**AlgHomClass.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgHomClass`。
形式化陈述：toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A ->ₐ
[R] B where __
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …

--- 原说明 ---
Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`.
-/
def toAlgHom {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) : A →ₐ[R] B where
  __ := (f : A →+* B)
  toFun := f
  commutes' := AlgHomClass.commutes f

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-
**AlgHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：funLike : FunLike (A ->ₐ[R] B) A B where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr
/-
**AlgHom.algHomClass** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：algHomClass : AlgHomClass (A ->ₐ[R] B) R A B where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `RingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemir
ing α] [inst_1 : NonAssocSemiring β] (self : α →+* β),   (↑↑self).toFun 0 = 0
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
instance algHomClass : AlgHomClass (A →ₐ[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'
/-
**AlgHom._root_.AlgHomClass.toLinearMap_toAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgH
om`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.AlgHomClass.toLinearMap_toAlgHom {R A B F : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) : (AlgHomClass.toAlgHom f : A →ₗ[R] B) = f := rfl

/-- See Note [custom simps projection] -/
/-
**AlgHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom.Simps`。
形式化陈述：{R : Type u} →   {α : Type v} →     {β : Type w} →       [inst : CommSemir
ing R] →         [inst_1 : Semiring α] →           [inst_2 : Semiring β] → [inst
_3 : Algebra R α] → [inst_4 : Algebra R β] → (α →ₐ[R] β) → α → β
参数：α →ₐ[R] β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) : α → β := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
/-
**AlgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] {F : Type u_1} [inst_5 : FunLike F A B] [inst_6 : AlgHomClass F R A B]   (f :
 F), ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(AlgHomClass.toAlgHom f : A →ₐ[R] B) = f :=
  rfl

@[simp]
/-
**AlgHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toFun_eq_coe (f : A ->ₐ[R] B) : f.toFun = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : A →ₐ[R] B) : f.toFun = f :=
  rfl

/-- Turn an algebra homomorphism into the corresponding multiplicative monoid homomorphism. -/
@[coe]
/-
**AlgHom.toMonoidHom'** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toMonoidHom' (f : A ->ₐ[R] B) : A ->* B
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an algebra homomorphism into the corresponding multiplicative monoid homomo
rphism.
-/
def toMonoidHom' (f : A →ₐ[R] B) : A →* B := (f : A →+* B)
/-
**AlgHom.coeOutMonoidHom** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：coeOutMonoidHom : CoeOut (A ->ₐ[R] B) (A ->* B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeOutMonoidHom : CoeOut (A →ₐ[R] B) (A →* B) :=
  ⟨AlgHom.toMonoidHom'⟩

/-- Turn an algebra homomorphism into the corresponding additive monoid homomorphism. -/
@[coe]
/-
**AlgHom.toAddMonoidHom'** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toAddMonoidHom' (f : A ->ₐ[R] B) : A ->+ B
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an algebra homomorphism into the corresponding additive monoid homomorphism
.
-/
def toAddMonoidHom' (f : A →ₐ[R] B) : A →+ B := (f : A →+* B)
/-
**AlgHom.coeOutAddMonoidHom** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：coeOutAddMonoidHom : CoeOut (A ->ₐ[R] B) (A ->+ B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeOutAddMonoidHom : CoeOut (A →ₐ[R] B) (A →+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩

@[simp]
/-
**AlgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_mk {f : A ->+* B} (h) : ((⟨f, h⟩ : A ->ₐ[R] B) : A -> B) = f
参数：h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A → B) = f :=
  rfl

@[norm_cast]
/-
**AlgHom.coe_mks** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_mks {f : A -> B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : 
A ->ₐ[R] B) = f
参数：h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f :=
  rfl

@[simp, norm_cast]
/-
**AlgHom.coe_ringHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_ringHom_mk {f : A ->+* B} (h) : ((⟨f, h⟩ : A ->ₐ[R] B) : A ->+* B) = f
参数：h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_ringHom_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A →+* B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
/-
**AlgHom.toRingHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f :=
  rfl

@[simp, norm_cast]
/-
**AlgHom.coe_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_toRingHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f :=
  rfl

@[simp, norm_cast]
/-
**AlgHom.coe_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_toMonoidHom (f : A ->ₐ[R] B) : ⇑(f : A ->* B) = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_toMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl

@[simp, norm_cast]
/-
**AlgHom.coe_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_toAddMonoidHom (f : A ->ₐ[R] B) : ⇑(f : A ->+ B) = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
-/
theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f :=
  rfl

@[simp]
/-
**AlgHom.toRingHom_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_toMonoidHom (f : A ->ₐ[R] B) : ((f : A ->+* B) : A ->* B) = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem toRingHom_toMonoidHom (f : A →ₐ[R] B) : ((f : A →+* B) : A →* B) = f :=
  rfl

@[simp]
/-
**AlgHom.toRingHom_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_toAddMonoidHom (f : A ->ₐ[R] B) : ((f : A ->+* B) : A ->+ B) = f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem toRingHom_toAddMonoidHom (f : A →ₐ[R] B) : ((f : A →+* B) : A →+ B) = f :=
  rfl

variable (φ : A →ₐ[R] B)
/-
**AlgHom.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_fn_injective : @Function.Injective (A ->ₐ[R] B) (A -> B) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) (↑) :=
  DFunLike.coe_injective
/-
**AlgHom.coe_fn_inj** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_fn_inj {φ₁ φ₂ : A ->ₐ[R] B} : (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq
/-
**AlgHom.coe_ringHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_ringHom_injective : Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->+* B
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_fn_injective`：coe_fn_injective : @Function.Injective (A ->ₐ[R
] B) (A -> B) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H
/-
**AlgHom.coe_monoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_monoidHom_injective : Function.Injective ((↑) : (A ->ₐ[R] B) -> A ->* 
B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.coe_monoidHom_injective`：coe_monoidHom_injective : Injective (fu
n f : α ->+* β => (f : α ->* β))
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
-/
theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoidHom_injective.comp coe_ringHom_injective
/-
**AlgHom.coe_addMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_addMonoidHom_injective : Function.Injective ((↑) : (A ->ₐ[R] B) -> A -
>+ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.coe_addMonoidHom_injective`：coe_addMonoidHom_injective : Injecti
ve (fun f : α ->+* β => (f : α ->+ β))
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
-/
theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_addMonoidHom_injective.comp coe_ringHom_injective
/-
**AlgHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] {φ₁ φ₂ : A →ₐ[R] B}, φ₁ = φ₂ → ∀ (x : A), φ₁ x = φ₂ x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x
/-
**AlgHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] (φ : A →ₐ[R] B) {x y : A}, x = y → φ x = φ y
参数：φ : A →ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
/-
**AlgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = φ₂
参数：H : forall x, φ₁ x = φ₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

@[simp]
/-
**AlgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mk_coe {f : A ->ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ 
: A ->ₐ[R] B) = f
参数：h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f :=
  rfl
/-
**AlgHom.addHomMk_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] (f : A →ₐ[R] B), { toFun := ⇑f, map_add' := ⋯ } = ↑f
参数：f : A →ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
-/
@[simp] lemma addHomMk_coe (f : A →ₐ[R] B) : AddHom.mk f (map_add f) = f := rfl

@[simp]
/-
**AlgHom.commutes** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r
/-
**AlgHom.comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：comp_algebraMap : (φ : A ->+* B).comp (algebraMap R A) = algebraMap R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem comp_algebraMap : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext <| φ.commutes

/-- If a `RingHom` is `R`-linear, then it is an `AlgHom`. -/
/-
**AlgHom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：mk' (f : A ->+* B) (h : forall (c : R) (x), f (c • x) = c • f x) : A ->ₐ[R
] B
参数：f : A ->+* B；h : forall (c : R) (x), f (c • x) = c • f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `RingHom` is `R`-linear, then it is an `AlgHom`.
-/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Algebra.algebraMap_eq_smul_one, h, f.map_one] }

@[simp]
/-
**AlgHom.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_mk' (f : A ->+* B) (h : forall (c : R) (x), f (c • x) = c • f x) : ⇑(m
k' f h) = f
参数：f : A ->+* B；h : forall (c : R) (x), f (c • x) = c • f x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl

section

variable (R A)

/-- Identity map as an `AlgHom`. -/
/-
**AlgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：(R : Type u) → (A : Type v) → [inst : CommSemiring R] → [inst_1 : Semiring
 A] → [inst_2 : Algebra R A] → A →ₐ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as an `AlgHom`.
-/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }

@[simp, norm_cast]
/-
**AlgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_id : ⇑(AlgHom.id R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl

@[simp]
/-
**AlgHom.id_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：id_toRingHom : (AlgHom.id R A : A ->+* A) = RingHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl

end

/-
**AlgHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：id_apply (p : A) : AlgHom.id R A p = p
参数：p : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl

/-- If `φ₁` and `φ₂` are `R`-algebra homomorphisms with the
domain of `φ₁` equal to the codomain of `φ₂`, then
`φ₁.comp φ₂` is the algebra homomorphism `x ↦ φ₁ (φ₂ x)`.
-/
/-
**AlgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : A ->ₐ[R] C
参数：φ₁ : B ->ₐ[R] C；φ₂ : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ₁` and `φ₂` are `R`-algebra homomorphisms with the
domain of `φ₁` equal to the codomain of `φ₂`, then
`φ₁.comp φ₂` is the algebra homomorphism `x ↦ φ₁ (φ₂ x)`.
-/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by rw [← φ₁.commutes, ← φ₂.commutes]; rfl }

@[simp]
/-
**AlgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
参数：φ₁ : B ->ₐ[R] C；φ₂ : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl
/-
**AlgHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁
 (φ₂ p)
参数：φ₁ : B ->ₐ[R] C；φ₂ : A ->ₐ[R] B；p : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl
/-
**AlgHom.comp_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：comp_toRingHom (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : (φ₁.comp φ₂ : A ->+* 
C) = (φ₁ : B ->+* C).comp ↑φ₂
参数：φ₁ : B ->ₐ[R] C；φ₂ : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem comp_toRingHom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
    (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ :=
  rfl

@[simp]
/-
**AlgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：comp_id : φ.comp (AlgHom.id R A) = φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  rfl

@[simp]
/-
**AlgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：id_comp : (AlgHom.id R B).comp φ = φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  rfl
/-
**AlgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : A ->ₐ[R] B) : (φ₁.com
p φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
参数：φ₁ : C ->ₐ[R] D；φ₂ : B ->ₐ[R] C；φ₃ : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  rfl
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {φ₁ : B →ₐ[R] C} {φ₂ : A →ₐ[R] B} :
    RingHomCompTriple φ₂.toRingHom φ₁.toRingHom (φ₁.comp φ₂).toRingHom := ⟨rfl⟩

/-- R-Alg ⥤ R-Mod -/
/-
**AlgHom.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap : A ->ₗ[R] B where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
R-Alg ⥤ R-Mod
-/
def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
/-
**AlgHom.toLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_apply (p : A) : φ.toLinearMap p = φ p
参数：p : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl

@[simp]
/-
**AlgHom.coe_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：coe_toLinearMap : ⇑φ.toLinearMap = φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toLinearMap : ⇑φ.toLinearMap = φ := rfl
/-
**AlgHom.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_injective : Function.Injective (toLinearMap : _ -> A ->ₗ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
/-
**AlgHom.comp_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：comp_toLinearMap (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.comp f).toLinearMa
p = g.toLinearMap.comp f.toLinearMap
参数：f : A ->ₐ[R] B；g : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toLinearMap (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
/-
**AlgHom.toLinearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  rfl
/-
**AlgHom.linearMapMk_toAddHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSemiring R] [inst_1 :
 Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R 
B] (f : A →ₐ[R] B), { toAddHom := ↑f, map_smul' := ⋯ } = f.toLinearMap
参数：f : A →ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
@[simp] lemma linearMapMk_toAddHom (f : A →ₐ[R] B) : LinearMap.mk f (map_smul f) = f.toLinearMap :=
  rfl

/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
/-
**AlgHom.ofLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：ofLinearMap (f : A ->ₗ[R] B) (map_one : f 1 = 1) (map_mul : forall x y, f 
(x * y) = f x * f y) : A ->ₐ[R] B
参数：f : A ->ₗ[R] B；map_one : f 1 = 1；map_mul : forall x y, f (x * y) = f x * f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `
1` and `*`.
-/
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' c := by simp only [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one] }

@[simp]
/-
**AlgHom.ofLinearMap_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ofLinearMap_toLinearMap (map_one) (map_mul) : ofLinearMap φ.toLinearMap ma
p_one map_mul = φ
参数：map_one；map_mul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ :=
  rfl

@[simp]
/-
**AlgHom.toLinearMap_ofLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_ofLinearMap (f : A ->ₗ[R] B) (map_one) (map_mul) : toLinearMap
 (ofLinearMap f map_one map_mul) = f
参数：f : A ->ₗ[R] B；map_one；map_mul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f :=
  rfl

@[simp]
/-
**AlgHom.ofLinearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ofLinearMap_id (map_one) (map_mul) : ofLinearMap LinearMap.id map_one map_
mul = AlgHom.id R A
参数：map_one；map_mul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  rfl
/-
**AlgHom.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A
 B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
参数：r : R'；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
/-
**AlgHom.End** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：End : Monoid (A ->ₐ[R] A) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance End : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := AlgHom.id R A
  one_mul _ := rfl
  mul_one _ := rfl

@[simp]
/-
**AlgHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：one_apply (x : A) : (1 : A ->ₐ[R] A) x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
  rfl

@[simp]
/-
**AlgHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mul_apply (φ ψ : A ->ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x)
参数：φ ψ : A ->ₐ[R] A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl
/-
**AlgHom.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (φ : A →ₐ[R] A)   (n : ℕ), ⇑(φ ^ n) = (⇑φ)^[n]
参数：φ : A →ₐ[R] A；n : ℕ；φ ^ n；⇑φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
@[simp] theorem coe_pow (φ : A →ₐ[R] A) (n : ℕ) : ⇑(φ ^ n) = φ^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]
/-
**AlgHom.algebraMap_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：algebraMap_eq_apply (f : A ->ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y
 = x) : algebraMap R B y = f x
参数：f : A ->ₐ[R] B；h : algebraMap R A y = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem algebraMap_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm
/-
**AlgHom.cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：cancel_right {g₁ g₂ : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hf : Function.Surjecti
ve f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHom.ext_iff`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [i
nst_…
-/
lemma cancel_right {g₁ g₂ : B →ₐ[R] C} {f : A →ₐ[R] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩
/-
**AlgHom.cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：cancel_left {g₁ g₂ : A ->ₐ[R] B} {f : B ->ₐ[R] C} (hf : Function.Injective
 f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AlgHom.ext_iff`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [i
nst_…
-/
lemma cancel_left {g₁ g₂ : A →ₐ[R] B} {f : B →ₐ[R] C} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| fun _ ↦ hf.eq_iff.mp <| AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

/-- `AlgHom.toLinearMap` as a `MonoidHom`. -/
/-
**AlgHom.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] → [inst_1 : Se
miring A] → [inst_2 : Algebra R A] → (A →ₐ[R] A) →* Module.End R A
参数：A →ₐ[R] A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom.toLinearMap` as a `MonoidHom`.
-/
@[simps] def toEnd : (A →ₐ[R] A) →* Module.End R A where
  toFun := toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

end Semiring
end AlgHom

namespace IsScalarTower

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
/-
**IsScalarTower.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `IsScalarTower`。
形式化陈述：toAlgHom : S ->ₐ[R] A where toRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element.
-/
def toAlgHom : S →ₐ[R] A where
  toRingHom := algebraMap S A
  commutes' r := by simpa [Algebra.smul_def] using smul_assoc r (1 : S) (1 : A)
/-
**IsScalarTower.toAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y
参数：y : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y := rfl

@[simp]
/-
**IsScalarTower.coe_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A :=
  RingHom.ext fun _ => rfl

@[simp]
/-
**IsScalarTower.coe_toAlgHom'** 是 Mathlib 中的一个定理，位于命名空间 `IsScalarTower`。
形式化陈述：coe_toAlgHom' : (toAlgHom R S A : S -> A) = algebraMap S A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgHom' : (toAlgHom R S A : S → A) = algebraMap S A := rfl

end IsScalarTower

/-- The algebra morphism underlying `algebraMap`. -/
alias Algebra.algHom := IsScalarTower.toAlgHom

alias Algebra.algHom_apply := IsScalarTower.toAlgHom_apply

namespace AlgHomClass

@[simp]
/-
**AlgHomClass.toRingHom_toAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgHomClass`。
形式化陈述：toRingHom_toAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring
 B] [Algebra R A] [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B
] (f : F) : RingHomClass.toRingHom (AlgHomClass.toAlgHom f) = RingHomClass.toRin
gHom f
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma toRingHom_toAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    RingHomClass.toRingHom (AlgHomClass.toAlgHom f) = RingHomClass.toRingHom f := rfl

end AlgHomClass

namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
/-
**RingHom.toNatAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：toNatAlgHom [Semiring R] [Semiring S] (f : R ->+* S) : R ->ₐ[Nat] S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism.
-/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }

@[simp]
/-
**RingHom.toNatAlgHom_coe** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：toNatAlgHom_coe [Semiring R] [Semiring S] (f : R ->+* S) : ⇑f.toNatAlgHom 
= ⇑f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNatAlgHom_coe [Semiring R] [Semiring S] (f : R →+* S) :
    ⇑f.toNatAlgHom = ⇑f := rfl
/-
**RingHom.toNatAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：toNatAlgHom_apply [Semiring R] [Semiring S] (f : R ->+* S) (x : R) : f.toN
atAlgHom x = f x
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNatAlgHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    f.toNatAlgHom x = f x := rfl

variable (R) (S) in
/-- Ring homomorphisms are the same as `ℕ`-algebra homomorphisms. -/
@[simps]
/-
**RingHom.equivNatAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：equivNatAlgHom [Semiring R] [Semiring S] : (R ->+* S) ≃ (R ->ₐ[Nat] S) whe
re toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphisms are the same as `ℕ`-algebra homomorphisms.
-/
def equivNatAlgHom [Semiring R] [Semiring S] : (R →+* S) ≃ (R →ₐ[ℕ] S) where
  toFun := RingHom.toNatAlgHom
  invFun := AlgHom.toRingHom

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
/-
**RingHom.toIntAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：toIntAlgHom [Ring R] [Ring S] (f : R ->+* S) : R ->ₐ[Int] S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism.
-/
def toIntAlgHom [Ring R] [Ring S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }

@[simp]
/-
**RingHom.toIntAlgHom_coe** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：toIntAlgHom_coe [Ring R] [Ring S] (f : R ->+* S) : ⇑f.toIntAlgHom = ⇑f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toIntAlgHom_coe [Ring R] [Ring S] (f : R →+* S) :
    ⇑f.toIntAlgHom = ⇑f := rfl
/-
**RingHom.toIntAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：toIntAlgHom_apply [Ring R] [Ring S] (f : R ->+* S) (x : R) : f.toIntAlgHom
 x = f x
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toIntAlgHom_apply [Ring R] [Ring S] (f : R →+* S) (x : R) :
    f.toIntAlgHom x = f x := rfl
/-
**RingHom.toIntAlgHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：toIntAlgHom_injective [Ring R] [Ring S] : Function.Injective (RingHom.toIn
tAlgHom : (R ->+* S) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

variable (R) (S) in
/-- Ring homomorphisms are the same as `ℤ`-algebra homomorphisms. -/
@[simps]
/-
**RingHom.equivIntAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：equivIntAlgHom [Ring R] [Ring S] : (R ->+* S) ≃ (R ->ₐ[Int] S) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphisms are the same as `ℤ`-algebra homomorphisms.
-/
def equivIntAlgHom [Ring R] [Ring S] : (R →+* S) ≃ (R →ₐ[ℤ] S) where
  toFun := RingHom.toIntAlgHom
  invFun := AlgHom.toRingHom

end RingHom

namespace Algebra

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- `AlgebraMap` as an `AlgHom`. -/
/-
**Algebra.ofId** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：ofId : R ->ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgebraMap` as an `AlgHom`.
-/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }

variable {R}
/-
**Algebra.ofId_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R], Algebra.ofId R R = AlgHom.id R R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofId_self : ofId R R = .id R R := rfl
/-
**Algebra.toRingHom_ofId** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u} (A : Type v) [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A],   ↑(Algebra.ofId R A) = algebraMap R A
参数：A : Type v；Algebra.ofId R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
@[simp] lemma toRingHom_ofId : ofId R A = algebraMap R A := rfl

@[simp]
/-
**Algebra.ofId_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：ofId_apply (r) : ofId R A r = algebraMap R A r
参数：r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl

/-- This is a special case of a more general instance that we define in a later file. -/
/-
**Algebra.subsingleton_id** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
形式化陈述：subsingleton_id : Subsingleton (R ->ₐ[R] A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
This is a special case of a more general instance that we define in a later file
.
-/
instance subsingleton_id : Subsingleton (R →ₐ[R] A) :=
  ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals created when chaining heterobasic ext lemmas. -/
@[ext high]
/-
**Algebra.ext_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：ext_id (f g : R ->ₐ[R] A) : f = g
参数：f g : R ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
This ext lemma closes trivial subgoals created when chaining heterobasic ext lem
mas.
-/
theorem ext_id (f g : R →ₐ[R] A) : f = g := Subsingleton.elim _ _

@[simp]
/-
**Algebra.comp_ofId** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：comp_ofId (φ : A ->ₐ[R] B) : φ.comp (Algebra.ofId R A) = Algebra.ofId R B
参数：φ : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
-/
theorem comp_ofId (φ : A →ₐ[R] B) : φ.comp (Algebra.ofId R A) = Algebra.ofId R B := by ext

section MulDistribMulAction

/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulDistribMulAction (A →ₐ[R] A) Aˣ where
  smul f := Units.map f
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
  smul_mul _ _ _ := by ext; exact map_mul _ _ _
  smul_one _ := by ext; exact map_one _

@[simp]
/-
**Algebra.smul_units_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：smul_units_def (f : A ->ₐ[R] A) (x : Aˣ) : f • x = Units.map (f : A ->* A)
 x
参数：f : A ->ₐ[R] A；x : Aˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_units_def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := rfl

end MulDistribMulAction

variable (M : Submonoid R) {B : Type w} [Semiring B] [Algebra R B] {A}

/-
**Algebra.algebraMapSubmonoid_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：algebraMapSubmonoid_map_eq (f : A ->ₐ[R] B) : (algebraMapSubmonoid A M).ma
p f = algebraMapSubmonoid B M
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma algebraMapSubmonoid_map_eq (f : A →ₐ[R] B) :
    (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M := by
  ext x
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    simp only [AlgHom.commutes]
    use r
  · rintro ⟨r, hr, rfl⟩
    simp only [Submonoid.mem_map]
    use (algebraMap R A r)
    simp only [AlgHom.commutes, and_true]
    use r
/-
**Algebra.algebraMapSubmonoid_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：algebraMapSubmonoid_le_comap (f : A ->ₐ[R] B) : algebraMapSubmonoid A M <=
 (algebraMapSubmonoid B M).comap f.toRingHom
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.algebraMapSubmonoid_map_eq`：algebraMapSubmonoid_map_eq (f : A ->
ₐ[R] B) : (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
-/
lemma algebraMapSubmonoid_le_comap (f : A →ₐ[R] B) :
    algebraMapSubmonoid A M ≤ (algebraMapSubmonoid B M).comap f.toRingHom := by
  rw [← algebraMapSubmonoid_map_eq M f]
  exact Submonoid.le_comap_map (Algebra.algebraMapSubmonoid A M)

end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribSMul.toLinearMap`. -/
@[simps]
/-
**MulSemiringAction.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringAction`。
形式化陈述：toAlgHom (m : M) : A ->ₐ[R] A
参数：m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribSMul.toLinearMap`.
-/
def toAlgHom (m : M) : A →ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }
/-
**MulSemiringAction.toAlgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringAct
ion`。
形式化陈述：toAlgHom_injective [FaithfulSMul M A] : Function.Injective (MulSemiringAct
ion.toAlgHom R A : M -> A ->ₐ[R] A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgHom.ext_iff`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [i
nst_…
-/
theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

end MulSemiringAction

section

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
  [Subsingleton T]

/-
**uniqueOfRight** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：uniqueOfRight : Unique (S ->ₐ[R] T) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueOfRight : Unique (S →ₐ[R] T) where
  default := AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ ↦ (Subsingleton.elim _ _))
  uniq _ := AlgHom.ext fun _ ↦ Subsingleton.elim _ _

@[simp]
/-
**AlgHom.default_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.default_apply (x : S) : (default : S ->ₐ[R] T) x = 0
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AlgHom.default_apply (x : S) : (default : S →ₐ[R] T) x = 0 :=
  rfl

end

