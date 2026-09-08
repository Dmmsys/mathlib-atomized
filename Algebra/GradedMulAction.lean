/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.Algebra.GradedMonoid

/-!
# Additively-graded multiplicative action structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(•) : A i → M j → M (i +ᵥ j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `GradedMonoid.GSMul A M`
* `GradedMonoid.GMulAction A M`

With the `SigmaGraded` scope open, these respectively imbue:

* `SMul (GradedMonoid A) (GradedMonoid M)`
* `MulAction (GradedMonoid A) (GradedMonoid M)`

For now, these typeclasses are primarily used in the construction of `DirectSum.GModule.Module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedSMul A M` (which provides the obvious `GradedMonoid.GSMul A` instance)

which provides the API lemma

* `SetLike.graded_smul_mem_graded`

Note that there is no need for `SetLike.graded_mul_action` or similar, as all the information it
would contain is already supplied by `GradedSMul` when the objects within `A` and `M` have
a `MulAction` instance.

## Tags

graded action
-/

public section


variable {ιA ιB ιM : Type*}

namespace GradedMonoid

/-! ### Typeclasses -/


section Defs

variable (A : ιA → Type*) (M : ιM → Type*)

/-- A graded version of `SMul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`. -/
/-
**GradedMonoid.GSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `GradedMonoid`。
形式化陈述：{ιA : Type u_1} →   {ιM : Type u_3} → (ιA → Type u_4) → (ιM → Type u_5) → 
[VAdd ιA ιM] → Type (max (max (max u_1 u_3) u_4) u_5)
参数：ιA → Type u_4；ιM → Type u_5；max (max (max u_1 u_3) u_4) u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `SMul`. Scalar multiplication combines grades additively, i.
e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`.
-/
class GSMul [VAdd ιA ιM] where
  /-- The homogeneous multiplication map `smul` -/
  smul {i j} : A i → M j → M (i +ᵥ j)

/-- A graded version of `Mul.toSMul` -/
/-
**GradedMonoid.GMul.toGSMul** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GMul`。
形式化陈述：{ιA : Type u_1} → (A : ιA → Type u_4) → [inst : Add ιA] → [GradedMonoid.GM
ul A] → GradedMonoid.GSMul A A
参数：A : ιA → Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Mul.toSMul`
-/
instance GMul.toGSMul [Add ιA] [GMul A] : GSMul A A where smul := GMul.mul
/-
**GradedMonoid.GSMul.toSMul** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GSMul`。
形式化陈述：{ιA : Type u_1} →   {ιM : Type u_3} →     (A : ιA → Type u_4) →       (M :
 ιM → Type u_5) → [inst : VAdd ιA ιM] → [GradedMonoid.GSMul A M] → SMul (GradedM
onoid A) (GradedMonoid M)
参数：A : ιA → Type u_4；M : ιM → Type u_5；GradedMonoid A；GradedMonoid M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance GSMul.toSMul [VAdd ιA ιM] [GSMul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun x y ↦ ⟨_, GSMul.smul x.snd y.snd⟩⟩
/-
**GradedMonoid.mk_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `GradedMonoid`。
形式化陈述：mk_smul_mk [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j) : mk i a • m
k j b = mk (i +ᵥ j) (GSMul.smul a b)
参数：a : A i；b : M j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul_mk [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i +ᵥ j) (GSMul.smul a b) :=
  rfl

/-- A graded version of `MulAction`. -/
/-
**GradedMonoid.GMulAction** 是 Mathlib 中的一个归纳类型，位于命名空间 `GradedMonoid`。
形式化陈述：{ιA : Type u_1} →   {ιM : Type u_3} →     (A : ιA → Type u_4) →       (ιM 
→ Type u_5) →         [inst : AddMonoid ιA] → [VAdd ιA ιM] → [GradedMonoid.GMono
id A] → Type (max (max (max u_1 u_3) u_4) u_5)
参数：A : ιA → Type u_4；ιM → Type u_5；max (max (max u_1 u_3) u_4) u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `MulAction`.
-/
class GMulAction [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A] extends GSMul A M where
  /-- One is the neutral element for `•` -/
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b

/-- The graded version of `Monoid.toMulAction`. -/
/-
**GradedMonoid.GMonoid.toGMulAction** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GMon
oid`。
形式化陈述：{ιA : Type u_1} →   (A : ιA → Type u_4) → [inst : AddMonoid ιA] → [inst_1 
: GradedMonoid.GMonoid A] → GradedMonoid.GMulAction A A
参数：A : ιA → Type u_4。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedMonoid.GMonoid.one_mul`：∀ {ι : Type u_1} {A : ι → Type u_2} {inst 
: AddMonoid ι} [self : GradedMonoid.GMonoid A] (a : GradedMonoid A), 1 * a = a
· 使用定理 `GradedMonoid.GMonoid.mul_assoc`：∀ {ι : Type u_1} {A : ι → Type u_2} {ins
t : AddMonoid ι} [self : GradedMonoid.GMonoid A] (a b c : GradedMonoid A),   a *
 b * c = a * (b * c)

--- 原说明 ---
The graded version of `Monoid.toMulAction`.
-/
instance GMonoid.toGMulAction [AddMonoid ιA] [GMonoid A] : GMulAction A A :=
  { GMul.toGSMul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }
/-
**GradedMonoid.GMulAction.toMulAction** 是 Mathlib 中的一个定义，位于命名空间 `GradedMonoid.GM
ulAction`。
形式化陈述：{ιA : Type u_1} →   {ιM : Type u_3} →     (A : ιA → Type u_4) →       (M :
 ιM → Type u_5) →         [inst : AddMonoid ιA] →           [inst_1 : GradedMono
id.GMonoid A] →             [inst_2 : VAdd ιA ιM] → [GradedMonoid.GMulAction A M
] → MulAction (GradedMonoid A) (GradedMonoid M)
参数：A : ιA → Type u_4；M : ιM → Type u_5；GradedMonoid A；GradedMonoid M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedMonoid.GMulAction.mul_smul`：∀ {ιA : Type u_1} {ιM : Type u_3} {A :
 ιA → Type u_4} {M : ιM → Type u_5} {inst : AddMonoid ιA} {inst_1 : VAdd ιA ιM} 
  {inst_2 : GradedMono…
· 使用定理 `GradedMonoid.GMulAction.one_smul`：∀ {ιA : Type u_1} {ιM : Type u_3} {A :
 ιA → Type u_4} {M : ιM → Type u_5} {inst : AddMonoid ιA} {inst_1 : VAdd ιA ιM} 
  {inst_2 : GradedMono…
-/
instance GMulAction.toMulAction [AddMonoid ιA] [GMonoid A] [VAdd ιA ιM] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M) where
  one_smul := GMulAction.one_smul
  mul_smul := GMulAction.mul_smul

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type*}

/-- A version of `GradedMonoid.GSMul` for internally graded objects. -/
/-
**SetLike.GradedSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `SetLike`。
形式化陈述：{ιA : Type u_1} →   {ιB : Type u_2} →     {S : Type u_5} →       {R : Type
 u_6} →         {N : Type u_7} →           {M : Type u_8} → [SetLike S R] → [Set
Like N M] → [SMul R M] → [VAdd ιA ιB] → (ιA → S) → (ιB → N) → Prop
参数：ιA → S；ιB → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `GradedMonoid.GSMul` for internally graded objects.
-/
class SetLike.GradedSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  (A : ιA → S) (B : ιB → N) : Prop where
  /-- Multiplication is homogeneous -/
  smul_mem : ∀ ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i +ᵥ j)
/-
**SetLike.toGSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetLike.toGSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [
VAdd ιA ιB] (A : ιA -> S) (B : ιB -> N) [SetLike.GradedSMul A B] : GradedMonoid.
GSMul (fun i => A i) fun i => B i where smul a b
参数：A : ιA -> S；B : ιB -> N。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SetLike.toGSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] :
    GradedMonoid.GSMul (fun i ↦ A i) fun i ↦ B i where
  smul a b := ⟨a.1 • b.1, SetLike.GradedSMul.smul_mem a.2 b.2⟩

@[simp]
/-
**SetLike.coe_GSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.coe_GSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M]
 [VAdd ιA ιB] (A : ιA -> S) (B : ιB -> N) [SetLike.GradedSMul A B] {i : ιA} {j :
 ιB} (x : A i) (y : B j) : (@GradedMonoid.GSMul.smul ιA ιB (fun i => A i) (fun i
 => B i) _ _ i j x y : M) = x.1 • y.1
参数：A : ιA -> S；B : ιB -> N；x : A i；y : B j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SetLike.coe_GSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] {i : ιA} {j : ιB} (x : A i) (y : B j) :
    (@GradedMonoid.GSMul.smul ιA ιB (fun i ↦ A i) (fun i ↦ B i) _ _ i j x y : M) = x.1 • y.1 :=
  rfl

/-- Internally graded version of `Mul.toSMul`. -/
/-
**SetLike.GradedMul.toGradedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetLike.GradedMul.toGradedSMul [AddMonoid ιA] [Monoid R] {S : Type*} [SetL
ike S R] (A : ιA -> S) [SetLike.GradedMonoid A] : SetLike.GradedSMul A A where s
mul_mem _ _ _ _ hi hj
参数：A : ιA -> S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMul.mul_mem`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3
} {inst : SetLike S R} {inst_1 : Mul R} {inst_2 : Add ι} {A : ι → S}   [self : S
etLike.GradedMu…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…

--- 原说明 ---
Internally graded version of `Mul.toSMul`.
-/
instance SetLike.GradedMul.toGradedSMul [AddMonoid ιA] [Monoid R] {S : Type*} [SetLike S R]
    (A : ιA → S) [SetLike.GradedMonoid A] : SetLike.GradedSMul A A where
  smul_mem _ _ _ _ hi hj := SetLike.GradedMonoid.toGradedMul.mul_mem hi hj

end Subobjects

section HomogeneousElements

variable {S R N M : Type*} [SetLike S R] [SetLike N M]

/-
**SetLike.IsHomogeneousElem.graded_smul** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.IsHom
ogeneousElem`。
形式化陈述：∀ {ιA : Type u_1} {ιB : Type u_2} {S : Type u_4} {R : Type u_5} {N : Type 
u_6} {M : Type u_7} [inst : SetLike S R]   [inst_1 : SetLike N M] [inst_2 : VAdd
 ιA ιB] [inst_3 : SMul R M] {A : ιA → S} {B : ιB → N} [SetLike.GradedSMul A B]  
 {a : R} {b : M}, SetLike.IsHomogeneousElem A a → SetLike.IsHomogeneousElem B b 
→ SetLike.IsHomogeneousElem B (a • b)
参数：a • b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedSMul.smul_mem`：∀ {ιA : Type u_1} {ιB : Type u_2} {S : Type
 u_5} {R : Type u_6} {N : Type u_7} {M : Type u_8} {inst : SetLike S R}   {inst_
1 : SetLike N M} …
-/
theorem SetLike.IsHomogeneousElem.graded_smul [VAdd ιA ιB] [SMul R M] {A : ιA → S} {B : ιB → N}
    [SetLike.GradedSMul A B] {a : R} {b : M} :
    SetLike.IsHomogeneousElem A a → SetLike.IsHomogeneousElem B b →
    SetLike.IsHomogeneousElem B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i +ᵥ j, SetLike.GradedSMul.smul_mem hi hj⟩

end HomogeneousElements

