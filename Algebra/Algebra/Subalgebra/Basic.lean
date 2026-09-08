/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

The `Algebra.adjoin` operation and complete lattice structure can be found in
`Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean`.
-/

@[expose] public section

open Module

universe u u' v w w'

/-- A subalgebra is a sub(semi)ring that includes the range of `algebraMap`. -/
/-
**Subalgebra** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebr
a R A] : Type v extends Subsemiring A where /-- The image of `algebraMap` is con
tained in the underlying set of the subalgebra -/ algebraMap_mem' : forall r, al
gebraMap R A r in carrier zero_mem'
参数：R : Type u；A : Type v。
继承自：Subsemiring A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra is a sub(semi)ring that includes the range of `algebraMap`.
-/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v
    extends Subsemiring A where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1

/-- Reinterpret a `Subalgebra` as a `Subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subalgebra R A) A where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subalgebra R A) := .ofSetLike (Subalgebra R A) A

initialize_simps_projections Subalgebra (carrier → coe, as_prefix coe)

@[simp]
/-
**Subalgebra.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_mk (s : Subsemiring A) (h) : (Subalgebra.mk (R
参数：s : Subsemiring A；h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Subsemiring A) (h) : (Subalgebra.mk (R := R) s h : Set A) = s :=
  rfl

@[simp]
/-
**Subalgebra.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_mk (s : Subsemiring A) (h) (x) : x in Subalgebra.mk (R
参数：s : Subsemiring A；h；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk (s : Subsemiring A) (h) (x) : x ∈ Subalgebra.mk (R := R) s h ↔ x ∈ s :=
  .rfl

/-- The actual `Subalgebra` obtained from an element of a type satisfying `SubsemiringClass` and
`SMulMemClass`. -/
@[simps]
/-
**Subalgebra.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLi
ke S A] [SubsemiringClass S A] [SMulMemClass S R A] (s : S) : Subalgebra R A whe
re carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `Subalgebra` obtained from an element of a type satisfying `Subsemiri
ngClass` and
`SMulMemClass`.
-/
def ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [SubsemiringClass S A] [SMulMemClass S R A] (s : S) :
    Subalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' r :=
    Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set A) (Subalgebra R A) (↑)
    (fun s ↦ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ (r : R), algebraMap R A r ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := by simpa using h.2.2 0
        add_mem' := h.1
        one_mem' := by simpa using h.2.2 1
        mul_mem' := h.2.1
        algebraMap_mem' := h.2.2 },
      rfl ⟩
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubsemiringClass (Subalgebra R A) A where
  add_mem {s} := add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

@[simp]
/-
**Subalgebra.mem_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_toSubsemiring {S : Subalgebra R A} {x} : x in S.toSubsemiring ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubsemiring {S : Subalgebra R A} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl
/-
**Subalgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_carrier {s : Subalgebra R A} {x : A} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
/-
**Subalgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x in T) : S = T
参数：h : forall x : A, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {S T : Subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
/-
**Subalgebra.coe_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_toSubsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S :=
  rfl
/-
**Subalgebra.toSubsemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubsemiring_injective : Function.Injective (toSubsemiring : Subalgebra R
 A -> Subsemiring A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.mem_toSubsemiring`：mem_toSubsemiring {S : Subalgebra R A} {x}
 : x in S.toSubsemiring ↔ x in S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : Subalgebra R A → Subsemiring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]
/-
**Subalgebra.toSubsemiring_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiri
ng ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subalgebra.toSubsemiring_injective`：toSubsemiring_injective : Function.I
njective (toSubsemiring : Subalgebra R A -> Subsemiring A)
-/
theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
/-
**Subalgebra.copy** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : Semiring A] → [inst_2 : Algebra R A] → (S : Subalgebra R A) → (s : Set A) → 
s = ↑S → Subalgebra R A
参数：S : Subalgebra R A；s : Set A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix de
finitional
equalities.
-/
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }
/-
**Subalgebra.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S
参数：S : Subalgebra R A；s : Set A；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : Subalgebra R A)
/-
**Subalgebra.instSMulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：instSMulMemClass : SMulMemClass (Subalgebra R A) R A where smul_mem {S} r 
x hx
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subalgebra.algebraMap_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (self : Subalgebra R A)   (
r : R), (algebra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
instance instSMulMemClass : SMulMemClass (Subalgebra R A) R A where
  smul_mem {S} r x hx := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**Subalgebra._root_.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.algebraMap_mem {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [OneMemClass S A] [SMulMemClass S R A] (s : S) (r : R) :
    algebraMap R A r ∈ s :=
  Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)
/-
**Subalgebra.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   (r : R), (algebraMap R A) r ∈ S
参数：S : Subalgebra R A；r : R；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem algebraMap_mem (r : R) : algebraMap R A r ∈ S :=
  algebraMap_mem S r
/-
**Subalgebra.rangeS_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：rangeS_le : (algebraMap R A).rangeS <= S.toSubsemiring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
-/
theorem rangeS_le : (algebraMap R A).rangeS ≤ S.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
/-
**Subalgebra.range_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：range_subset : Set.range (algebraMap R A) subseteq S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
-/
theorem range_subset : Set.range (algebraMap R A) ⊆ S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r
/-
**Subalgebra.range_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：range_le : Set.range (algebraMap R A) <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.range_subset`：range_subset : Set.range (algebraMap R A) subse
teq S
-/
theorem range_le : Set.range (algebraMap R A) ≤ S :=
  S.range_subset
/-
**Subalgebra.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
参数：hx : x in S；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  SMulMemClass.smul_mem r hx
/-
**Subalgebra.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem one_mem : (1 : A) ∈ S :=
  one_mem S
/-
**Subalgebra.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x ∈ S → y ∈ S → x * y ∈
 S
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
  mul_mem hx hy
/-
**Subalgebra.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈ S → ∀ (n : ℕ), x ^ n 
∈ S
参数：S : Subalgebra R A；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  pow_mem hx n
/-
**Subalgebra.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A),   0 ∈ S
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem zero_mem : (0 : A) ∈ S :=
  zero_mem S
/-
**Subalgebra.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x ∈ S → y ∈ S → x + y ∈
 S
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  add_mem hx hy
/-
**Subalgebra.nsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈ S → ∀ (n : ℕ), n • x 
∈ S
参数：S : Subalgebra R A；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
  nsmul_mem hx n
/-
**Subalgebra.natCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   (n : ℕ), ↑n ∈ S
参数：S : Subalgebra R A；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `natCast_mem`：natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n :
 R) in s
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem natCast_mem (n : ℕ) : (n : A) ∈ S :=
  natCast_mem S n
/-
**Subalgebra.list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {L : List A}, (∀ x ∈ L, x ∈ S) → L
.prod ∈ S
参数：S : Subalgebra R A；∀ x ∈ L, x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem list_prod_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
  list_prod_mem h
/-
**Subalgebra.list_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {L : List A}, (∀ x ∈ L, x ∈ S) → L
.sum ∈ S
参数：S : Subalgebra R A；∀ x ∈ L, x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem list_sum_mem {L : List A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
  list_sum_mem h
/-
**Subalgebra.multiset_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {m : Multiset A}, (∀ x ∈ m, x ∈ S)
 → m.sum ∈ S
参数：S : Subalgebra R A；∀ x ∈ m, x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   (m : Multiset M), (∀
 a ∈ m…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem multiset_sum_mem {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
  multiset_sum_mem m h
/-
**Subalgebra.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w} {t : Finset ι} {f : ι
 → A}, (∀ x ∈ t, f x ∈ S) → ∑ x ∈ t, f x ∈ S
参数：S : Subalgebra R A；∀ x ∈ t, f x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∑ x ∈ t, f x) ∈ S :=
  sum_mem h
/-
**Subalgebra.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : CommSemiring
 A] [inst_2 : Algebra R A]   (S : Subalgebra R A) {m : Multiset A}, (∀ x ∈ m, x 
∈ S) → m.prod ∈ S
参数：S : Subalgebra R A；∀ x ∈ m, x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem multiset_prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (S : Subalgebra R A) {m : Multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
  multiset_prod_mem m h
/-
**Subalgebra.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : CommSemiring
 A] [inst_2 : Algebra R A]   (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f
 : ι → A}, (∀ x ∈ t, f x ∈ S) → ∏ x ∈ t, f x ∈ S
参数：S : Subalgebra R A；∀ x ∈ t, f x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x ∈ t, f x ∈ S) :
    (∏ x ∈ t, f x) ∈ S :=
  prod_mem h

/-- Turn a `Subalgebra` into a `NonUnitalSubalgebra` by forgetting that it contains `1`. -/
@[reducible]
/-
**Subalgebra.toNonUnitalSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A where
 __
参数：S : Subalgebra R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S

--- 原说明 ---
Turn a `Subalgebra` into a `NonUnitalSubalgebra` by forgetting that it contains 
`1`.
-/
def toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r
/-
**Subalgebra.one_mem_toNonUnitalSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra
`。
形式化陈述：one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) : (1 : A) in S.toNonUni
talSubalgebra
参数：S : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
-/
lemma one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) : (1 : A) ∈ S.toNonUnitalSubalgebra :=
  S.one_mem

@[simp]
/-
**Subalgebra.mem_toNonUnitalSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：mem_toNonUnitalSubalgebra {S : Subalgebra R A} {x : A} : x in S.toNonUnita
lSubalgebra ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toNonUnitalSubalgebra {S : Subalgebra R A} {x : A} :
    x ∈ S.toNonUnitalSubalgebra ↔ x ∈ S :=
  Iff.rfl
/-
**Subalgebra.toNonUnitalSubalgebra_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subalgeb
ra`。
形式化陈述：toNonUnitalSubalgebra_injective : Function.Injective (toNonUnitalSubalgebr
a : Subalgebra R A -> NonUnitalSubalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma toNonUnitalSubalgebra_injective : Function.Injective
    (toNonUnitalSubalgebra : Subalgebra R A → NonUnitalSubalgebra R A) :=
  fun _ _ ↦ by simp [SetLike.ext_iff]
/-
**Subalgebra.toNonUnitalSubalgebra_inj** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：toNonUnitalSubalgebra_inj {S U : Subalgebra R A} : S.toNonUnitalSubalgebra
 = U.toNonUnitalSubalgebra ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Subalgebra.toNonUnitalSubalgebra_injective`：toNonUnitalSubalgebra_inject
ive : Function.Injective (toNonUnitalSubalgebra : Subalgebra R A -> NonUnitalSub
algebra R A)
-/
lemma toNonUnitalSubalgebra_inj {S U : Subalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U :=
  toNonUnitalSubalgebra_injective.eq_iff
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.instSubsemiringClass with
    neg_mem := fun {S x} hx => neg_one_smul R x ▸ S.smul_mem hx _ }
/-
**Subalgebra.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x ∈ S
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem neg_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
  neg_mem hx
/-
**Subalgebra.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y ∈ S → x - y ∈ S
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem sub_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  sub_mem hx hy
/-
**Subalgebra.zsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → ∀ (n : ℤ), n • x ∈ S
参数：S : Subalgebra R A；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  zsmul_mem hx n
/-
**Subalgebra.intCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] (S : Subalgebra R A) (n : ℤ),   ↑n ∈ S
参数：S : Subalgebra R A；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intCast_mem`：intCast_mem (n : Int) : (n : R) in s
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem intCast_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
  intCast_mem S n

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
@[reducible]
/-
**Subalgebra.toAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Al
gebra R A] (S : Subalgebra R A) : AddSubmonoid A
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from a subalgebra of `A` to an additive submonoid of `A`.
-/
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid

/-- A subalgebra over a ring is also a `Subring`. -/
@[reducible]
/-
**Subalgebra.toSubring** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S
 : Subalgebra R A) : Subring A
参数：S : Subalgebra R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.neg_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x 
∈ S

--- 原说明 ---
A subalgebra over a ring is also a `Subring`.
-/
def toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    Subring A :=
  { S.toSubsemiring with neg_mem' := S.neg_mem }
/-
**Subalgebra.mem_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A
] {S : Subalgebra R A} {x} : x in S.toSubring ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} {x} : x ∈ S.toSubring ↔ x ∈ S :=
  Iff.rfl
/-
**Subalgebra.coe_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A
] (S : Subalgebra R A) : (↑S.toSubring : Set A) = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) : (↑S.toSubring : Set A) = S :=
  rfl
/-
**Subalgebra.toSubring_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algeb
ra R A] : Function.Injective (toSubring : Subalgebra R A -> Subring A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.mem_toSubring`：mem_toSubring {R : Type u} {A : Type v} [CommR
ing R] [Ring A] [Algebra R A] {S : Subalgebra R A} {x} : x in S.toSubring ↔ x in
 S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (toSubring : Subalgebra R A → Subring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]
/-
**Subalgebra.toSubring_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A
] {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subalgebra.toSubring_injective`：toSubring_injective {R : Type u} {A : Ty
pe v} [CommRing R] [Ring A] [Algebra R A] : Function.Injective (toSubring : Suba
lgebra R A -> Subrin…
-/
theorem toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U :=
  toSubring_injective.eq_iff
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited S :=
  ⟨(0 : S.toSubsemiring)⟩

section

/-! `Subalgebra`s inherit structure from their `Subsemiring` / `Semiring` coercions. -/


/-
**Subalgebra.toSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgeb
ra R A) : Semiring S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subalgebra`s inherit structure from their `Subsemiring` / `Semiring` coercions.
-/
instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring
/-
**Subalgebra.toCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : 
Subalgebra R A) : CommSemiring S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiring S :=
  S.toSubsemiring.toCommSemiring
/-
**Subalgebra.toRing** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ri
ng S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ring S :=
  S.toSubring.toRing
/-
**Subalgebra.toCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R
 A) : CommRing S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    CommRing S :=
  S.toSubring.toCommRing

end

/-- The forgetful map from `Subalgebra` to `Submodule` as an `OrderEmbedding` -/
@[instance_reducible] -- Not `@[reducible]` because it is an order embedding rather than a function.
/-
**Subalgebra.toSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：toSubmodule : Subalgebra R A ↪o Submodule R A where toEmbedding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map from `Subalgebra` to `Submodule` as an `OrderEmbedding`
-/
def toSubmodule : Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx ↦
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h ↦ ext fun x ↦ SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-! TODO: bundle other forgetful maps between algebraic substructures, e.g.
  `toSubsemiring` and `toSubring` in this file. -/

@[simp]
/-
**Subalgebra.mem_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_toSubmodule {x} : x in (toSubmodule S) ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
TODO: bundle other forgetful maps between algebraic substructures, e.g.
  `toSubsemiring` and `toSubring` in this file.
-/
theorem mem_toSubmodule {x} : x ∈ (toSubmodule S) ↔ x ∈ S := Iff.rfl

@[simp]
/-
**Subalgebra.coe_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_toSubmodule (S : Subalgebra R A) : (toSubmodule S : Set A) = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmodule (S : Subalgebra R A) : (toSubmodule S : Set A) = S := rfl
/-
**Subalgebra.toSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubmodule_injective : Function.Injective (toSubmodule : Subalgebra R A -
> Submodule R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toSubmodule_injective : Function.Injective (toSubmodule : Subalgebra R A → Submodule R A) :=
  fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

section

/-! `Subalgebra`s inherit structure from their `Submodule` coercions. -/


/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subalgebra`s inherit structure from their `Submodule` coercions.
-/
instance (priority := low) module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    Module R' S :=
  inferInstance
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R S :=
  inferInstance
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  inferInstance

/-- More general form of `Subalgebra.algebra`.

This instance should have low priority since it is slow to fail:
before failing, it will cause a search through all `SMul R' R` instances,
which can quickly get expensive.
-/
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More general form of `Subalgebra.algebra`.

This instance should have low priority since it is slow to fail:
before failing, it will cause a search through all `SMul R' R` instances,
which can quickly get expensive.
-/
instance (priority := 500) algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A]
    [IsScalarTower R' R A] :
    Algebra R' S where
  algebraMap := (algebraMap R' A).codRestrict S fun x => by
    rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←
      Algebra.algebraMap_eq_smul_one]
    exact algebraMap_mem S _
  commutes' := fun _ _ => Subtype.ext <| Algebra.commutes _ _
  smul_def' := fun _ _ => Subtype.ext <| Algebra.smul_def _ _
/-
**Subalgebra.algebra** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：algebra : Algebra R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra R S := S.algebra'

@[simp]
/-
**Subalgebra.mk_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mk_algebraMap {S : Subalgebra R A} (r : R) (hr : algebraMap R A r in S) : 
⟨algebraMap R A r, hr⟩ = algebraMap R S r
参数：r : R；hr : algebraMap R A r in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_algebraMap {S : Subalgebra R A} (r : R) (hr : algebraMap R A r ∈ S) :
    ⟨algebraMap R A r, hr⟩ = algebraMap R S r := rfl

end

/-
**Subalgebra.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：instIsTorsionFree [IsTorsionFree R A] : IsTorsionFree R S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTorsionFree [IsTorsionFree R A] : IsTorsionFree R S :=
  S.toSubmodule.instIsTorsionFree
/-
**Subalgebra.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   (x y : ↥S), ↑(x + y) = ↑x + ↑y
参数：S : Subalgebra R A；x y : ↥S；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl
/-
**Subalgebra.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   (x y : ↥S), ↑(x * y) = ↑x * ↑y
参数：S : Subalgebra R A；x y : ↥S；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl
/-
**Subalgebra.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A),   ↑0 = 0
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem coe_zero : ((0 : S) : A) = 0 := rfl
/-
**Subalgebra.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A),   ↑1 = 1
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem coe_one : ((1 : S) : A) = 1 := rfl
/-
**Subalgebra.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] {S : Subalgebra R A} (x : ↥S),   ↑(-x) = -↑x
参数：x : ↥S；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl
/-
**Subalgebra.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] {S : Subalgebra R A}   (x y : ↥S), ↑(x - y) = ↑x - ↑y
参数：x y : ↥S；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
-/
protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl

@[simp, norm_cast]
/-
**Subalgebra.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
 (↑(r • x) : A) = r • (x : A)
参数：r : R'；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • (x : A) := rfl

@[simp, norm_cast]
/-
**Subalgebra.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_algebraMap [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower
 R' R A] (r : R') : ↑(algebraMap R' S r) = algebraMap R' A r
参数：r : R'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
    (r : R') : ↑(algebraMap R' S r) = algebraMap R' A r := rfl
/-
**Subalgebra.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   (x : ↥S) (n : ℕ), ↑(x ^ n) = ↑x ^ 
n
参数：S : Subalgebra R A；x : ↥S；n : ℕ；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_pow`：coe_pow {M} [Monoid M] {A : Type*} [SetLike A M]
 [SubmonoidClass A M] {S : A} (x : S) (n : Nat) : ↑(x ^ n) = (x : M) ^ n
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem coe_pow (x : S) (n : ℕ) : (↑(x ^ n) : A) = (x : A) ^ n :=
  SubmonoidClass.coe_pow x n
/-
**Subalgebra.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {x : ↥S}, ↑x = 0 ↔ x = 0
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero
/-
**Subalgebra.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (S : Subalgebra R A)   {x : ↥S}, ↑x = 1 ↔ x = 1
参数：S : Subalgebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.coe_eq_one`：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
protected theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  OneMemClass.coe_eq_one

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype
/-- Embedding of a subalgebra into the algebra. -/
/-
**Subalgebra.val** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：val : S ->ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of a subalgebra into the algebra.
-/
def val : S →ₐ[R] A :=
  { toFun := ((↑) : S → A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

@[simp]
/-
**Subalgebra.coe_val** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_val : (S.val : S -> A) = ((↑) : S -> A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_val : (S.val : S → A) = ((↑) : S → A) := rfl
/-
**Subalgebra.val_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：val_apply (x : S) : S.val x = (x : A)
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_apply (x : S) : S.val x = (x : A) := rfl

@[simp]
/-
**Subalgebra.toSubsemiring_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubsemiring_subtype : S.toSubsemiring.subtype = (S.val : S ->+* A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubsemiring_subtype : S.toSubsemiring.subtype = (S.val : S →+* A) := rfl

@[simp]
/-
**Subalgebra.toSubring_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : S
ubalgebra R A) : S.toSubring.subtype = (S.val : S ->+* A)
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.subtype = (S.val : S →+* A) := rfl

/-- Linear equivalence between `S : Submodule R A` and `S`. Though these types are equal,
we define it as a `LinearEquiv` to avoid type equalities. -/
/-
**Subalgebra.toSubmoduleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between `S : Submodule R A` and `S`. Though these types are e
qual,
we define it as a `LinearEquiv` to avoid type equalities.
-/
def toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
@[simps! coe toSubsemiring]
/-
**Subalgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：map (f : A ->ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B
参数：f : A ->ₐ[R] B；S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a subalgebra via an algebra homomorphism.
-/
def map (f : A →ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A →+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }

@[gcongr]
/-
**Subalgebra.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_mono {S₁ S₂ : Subalgebra R A} {f : A ->ₐ[R] B} : S₁ <= S₂ -> S₁.map f 
<= S₂.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A →ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_mono
/-
**Subalgebra.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_injective {f : A ->ₐ[R] B} (hf : Function.Injective f) : Function.Inje
ctive (map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem map_injective {f : A →ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
  ext <| Set.ext_iff.1 <| Set.image_injective.2 hf <| Set.ext <| SetLike.ext_iff.mp ih

@[simp]
/-
**Subalgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
  SetLike.coe_injective <| Set.image_id _
/-
**Subalgebra.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_map (S : Subalgebra R A) (g : B ->ₐ[R] C) (f : A ->ₐ[R] B) : (S.map f)
.map g = S.map (g.comp f)
参数：S : Subalgebra R A；g : B ->ₐ[R] C；f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

@[simp]
/-
**Subalgebra.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_map {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B} : y in map f S ↔ exi
sts x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsemiring.mem_map`：mem_map {f : R ->+* S} {s : Subsemiring R} {y : S} 
: y in s.map f ↔ exists x in s, f x = y
-/
theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ map f S ↔ ∃ x ∈ S, f x = y :=
  Subsemiring.mem_map
/-
**Subalgebra.map_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_toSubmodule {S : Subalgebra R A} {f : A ->ₐ[R] B} : (toSubmodule <| S.
map f) = S.toSubmodule.map f.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem map_toSubmodule {S : Subalgebra R A} {f : A →ₐ[R] B} :
    (toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap :=
  SetLike.coe_injective rfl

/-- Preimage of a subalgebra under an algebra homomorphism. -/
@[simps! coe toSubsemiring]
/-
**Subalgebra.comap** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：comap (f : A ->ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A
参数：f : A ->ₐ[R] B；S : Subalgebra R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of a subalgebra under an algebra homomorphism.
-/
def comap (f : A →ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A →+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebraMap_mem r }

attribute [norm_cast] coe_comap
/-
**Subalgebra.map_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_le {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Subalgebra R B} : map f 
S <= U ↔ S <= comap f U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} :
    map f S ≤ U ↔ S ≤ comap f U :=
  Set.image_subset_iff
/-
**Subalgebra.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：gc_map_comap (f : A ->ₐ[R] B) : GaloisConnection (map f) (comap f)
参数：f : A ->ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.map_le`：map_le {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Sub
algebra R B} : map f S <= U ↔ S <= comap f U
-/
theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U => map_le

@[simp]
/-
**Subalgebra.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_comap (S : Subalgebra R B) (f : A ->ₐ[R] B) (x : A) : x in S.comap f ↔
 f x in S
参数：S : Subalgebra R B；f : A ->ₐ[R] B；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
/-
**Subalgebra.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：noZeroDivisors {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors
 A] [Algebra R A] (S : Subalgebra R A) : NoZeroDivisors S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance noZeroDivisors {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
    [Algebra R A] (S : Subalgebra R A) : NoZeroDivisors S :=
  inferInstanceAs (NoZeroDivisors S.toSubsemiring)
/-
**Subalgebra.isDomain** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：isDomain {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A] (S
 : Subalgebra R A) : IsDomain S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isDomain {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    (S : Subalgebra R A) : IsDomain S :=
  inferInstanceAs (IsDomain S.toSubring)

end Subalgebra

namespace SubalgebraClass

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

/-
**SubalgebraClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubalgebraClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) toAlgebra : Algebra R s where
  algebraMap := {
    toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩
    map_one' := Subtype.ext <| by simp
    map_mul' _ _ := Subtype.ext <| by simp
    map_zero' := Subtype.ext <| by simp
    map_add' _ _ := Subtype.ext <| by simp }
  commutes' r x := Subtype.ext <| Algebra.commutes r (x : A)
  smul_def' r x := Subtype.ext <| (algebraMap_smul A r (x : A)).symm

@[simp, norm_cast]
/-
**SubalgebraClass.coe_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `SubalgebraClass`。
形式化陈述：coe_algebraMap (r : R) : (algebraMap R s r : A) = algebraMap R A r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_algebraMap (r : R) : (algebraMap R s r : A) = algebraMap R A r := rfl

/-- Embedding of a subalgebra into the algebra, as an algebra homomorphism. -/
/-
**SubalgebraClass.val** 是 Mathlib 中的一个定义，位于命名空间 `SubalgebraClass`。
形式化陈述：val (s : S) : s ->ₐ[R] A
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of a subalgebra into the algebra, as an algebra homomorphism.
-/
def val (s : S) : s →ₐ[R] A :=
  { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ ↦ rfl }

@[simp]
/-
**SubalgebraClass.coe_val** 是 Mathlib 中的一个定理，位于命名空间 `SubalgebraClass`。
形式化陈述：coe_val : (val s : s -> A) = ((↑) : s -> A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_val : (val s : s → A) = ((↑) : s → A) :=
  rfl

end SubalgebraClass

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (p : Submodule R A)

/-- A submodule containing `1` and closed under multiplication is a subalgebra. -/
@[simps coe toSubsemiring]
/-
**Submodule.toSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toSubalgebra (p : Submodule R A) (h_one : (1 : A) in p) (h_mul : forall x 
y, x in p -> y in p -> x * y in p) : Subalgebra R A
参数：p : Submodule R A；h_one : (1 : A) in p；h_mul : forall x y, x in p -> y in p -
> x * y in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule containing `1` and closed under multiplication is a subalgebra.
-/
def toSubalgebra (p : Submodule R A) (h_one : (1 : A) ∈ p)
    (h_mul : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p) : Subalgebra R A :=
  { p with
    mul_mem' := fun hx hy ↦ h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }

@[simp]
/-
**Submodule.mem_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} : x in p.toSubalgeb
ra h_one h_mul ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} :
    x ∈ p.toSubalgebra h_one h_mul ↔ x ∈ p := Iff.rfl
/-
**Submodule.toSubalgebra_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubalgebra_mk (s : Submodule R A) (h1 hmul) : s.toSubalgebra h1 hmul = S
ubalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩ (by intro r; rw [Algebra.
algebraMap_eq_smul_one]; apply s.smul_mem _ h1)
参数：s : Submodule R A；h1 hmul。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubalgebra_mk (s : Submodule R A) (h1 hmul) :
    s.toSubalgebra h1 hmul =
      Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩
        (by intro r; rw [Algebra.algebraMap_eq_smul_one]; apply s.smul_mem _ h1) :=
  rfl

@[simp]
/-
**Submodule.toSubalgebra_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) : Subalgebra.to
Submodule (p.toSubalgebra h_one h_mul) = p
参数：p : Submodule R A；h_one h_mul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) :
    Subalgebra.toSubmodule (p.toSubalgebra h_one h_mul) = p :=
  SetLike.coe_injective rfl

@[simp]
/-
**Submodule._root_.Subalgebra.toSubmodule_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.toSubmodule_toSubalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace AlgHom

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
variable (φ : A →ₐ[R] B)

/-- Range of an `AlgHom` as a subalgebra. -/
@[simps! coe toSubsemiring]
/-
**AlgHom.range** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：{R : Type u} →   {A : Type v} →     {B : Type w} →       [inst : CommSemir
ing R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A] → [ins
t_3 : Semiring B] → [inst_4 : Algebra R B] → (A →ₐ[R] B) → Subalgebra R B
参数：A →ₐ[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Range of an `AlgHom` as a subalgebra.
-/
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
/-
**AlgHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ exists x, φ x = y
参数：φ : A ->ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.mem_rangeS`：mem_rangeS {f : R ->+* S} {y : S} : y in f.rangeS ↔ 
exists x, f x = y
-/
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_rangeS
/-
**AlgHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mem_range_self (φ : A ->ₐ[R] B) (x : A) : φ x in φ.range
参数：φ : A ->ₐ[R] B；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
-/
theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩
/-
**AlgHom.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.comp f).range = f.range.
map g
参数：f : A ->ₐ[R] B；g : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g :=
  SetLike.coe_injective (Set.range_comp g f)
/-
**AlgHom.range_comp_le_range** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：range_comp_le_range (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.comp f).range <
= g.range
参数：f : A ->ₐ[R] B；g : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/-- Restrict the codomain of an algebra homomorphism. -/
/-
**AlgHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S
) : A ->ₐ[R] S
参数：f : A ->ₐ[R] B；S : Subalgebra R B；hf : forall x, f x in S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A

--- 原说明 ---
Restrict the codomain of an algebra homomorphism.
-/
def codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codRestrict (f : A →+* B) S hf with commutes' := fun r => Subtype.ext <| f.commutes r }

@[simp]
/-
**AlgHom.val_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：val_comp_codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x,
 f x in S) : S.val.comp (f.codRestrict S hf) = f
参数：f : A ->ₐ[R] B；S : Subalgebra R B；hf : forall x, f x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem val_comp_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    S.val.comp (f.codRestrict S hf) = f :=
  AlgHom.ext fun _ => rfl

@[simp]
/-
**AlgHom.coe_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x 
in S) (x : A) : ↑(f.codRestrict S hf x) = f x
参数：f : A ->ₐ[R] B；S : Subalgebra R B；hf : forall x, f x in S；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl
/-
**AlgHom.injective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：injective_codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x
, f x in S) : Function.Injective (f.codRestrict S hf) ↔ Function.Injective f
参数：f : A ->ₐ[R] B；S : Subalgebra R B；hf : forall x, f x in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_codRestrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f :=
  ⟨fun H _x _y hxy => H <| Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/-- Restrict the codomain of an `AlgHom` `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**AlgHom.rangeRestrict** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgHom`。
形式化陈述：rangeRestrict (f : A ->ₐ[R] B) : A ->ₐ[R] f.range
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.mem_range_self`：mem_range_self (φ : A ->ₐ[R] B) (x : A) : φ x in 
φ.range

--- 原说明 ---
Restrict the codomain of an `AlgHom` `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`.
-/
abbrev rangeRestrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.codRestrict f.range f.mem_range_self
/-
**AlgHom.val_comp_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：val_comp_rangeRestrict : (Subalgebra.val _).comp φ.rangeRestrict = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.val_comp_codRestrict`：val_comp_codRestrict (f : A ->ₐ[R] B) (S : 
Subalgebra R B) (hf : forall x, f x in S) : S.val.comp (f.codRestrict S hf) = f
· 使用定理 `AlgHom.mem_range_self`：mem_range_self (φ : A ->ₐ[R] B) (x : A) : φ x in 
φ.range
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem val_comp_rangeRestrict :
    (Subalgebra.val _).comp φ.rangeRestrict = φ := by simp
/-
**AlgHom.rangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：rangeRestrict_surjective (f : A ->ₐ[R] B) : Function.Surjective (f.rangeRe
strict)
参数：f : A ->ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
-/
theorem rangeRestrict_surjective (f : A →ₐ[R] B) : Function.Surjective (f.rangeRestrict) :=
  fun ⟨_y, hy⟩ =>
    let ⟨x, hx⟩ := hy
    ⟨x, SetCoe.ext hx⟩

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is also a fintype. -/
/-
**AlgHom.fintypeRange** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：fintypeRange [Fintype A] [DecidableEq B] (φ : A ->ₐ[R] B) : Fintype φ.rang
e
参数：φ : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.fintype` if `B` is als
o a fintype.
-/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : A →ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ

end AlgHom

namespace AlgEquiv

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `AlgEquiv.ofInjective`. -/
/-
**AlgEquiv.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofLeftInverse {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f)
 : A ≃ₐ[R] f.range
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an algebra homomorphism with a left inverse to an algebra isomorphism t
o its range.

This is a computable alternative to `AlgEquiv.ofInjective`.
-/
def ofLeftInverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/-
**AlgEquiv.ofLeftInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofLeftInverse_apply {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInvers
e g f) (x : A) : ↑(ofLeftInverse h x) = f x
参数：h : Function.LeftInverse g f；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
/-
**AlgEquiv.ofLeftInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofLeftInverse_symm_apply {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftI
nverse g f) (x : f.range) : (ofLeftInverse h).symm x = g x
参数：h : Function.LeftInverse g f；x : f.range。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
/-
**AlgEquiv.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofInjective (f : A ->ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range
参数：f : A ->ₐ[R] B；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an injective algebra homomorphism to an algebra isomorphism
-/
noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)

@[simp]
/-
**AlgEquiv.ofInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：ofInjective_apply (f : A ->ₐ[R] B) (hf : Function.Injective f) (x : A) : ↑
(ofInjective f hf x) = f x
参数：f : A ->ₐ[R] B；hf : Function.Injective f；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
    ↑(ofInjective f hf x) = f x :=
  rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
/-
**AlgEquiv.ofInjectiveField** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F
] [Algebra R E] [Algebra R F] (f : E ->ₐ[R] F) : E ≃ₐ[R] f.range
参数：f : E ->ₐ[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an algebra homomorphism between fields to an algebra isomorphism
-/
noncomputable def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
    [Algebra R E] [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
  ofInjective f f.toRingHom.injective

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`,
`subalgebraMap` is the induced equivalence between `S` and `S.map e` -/
@[simps!]
/-
**AlgEquiv.subalgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map (e : A 
->ₐ[R] B)
参数：e : A ≃ₐ[R] B；S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`
,
`subalgebraMap` is the induced equivalence between `S` and `S.map e`
-/
def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map (e : A →ₐ[R] B) :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by ext; exact e.commutes r }

end AlgEquiv

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S T U : Subalgebra R A)

/-
**Subalgebra.subsingleton_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`
。
形式化陈述：subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R
 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩
/-
**Subalgebra.range_val** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：range_val : S.val.range = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem range_val : S.val.range = S :=
  ext <| Set.ext_iff.1 <| S.val.coe_range.trans Subtype.range_val

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `Submodule.inclusion`, or `Subring.inclusion` -/
/-
**Subalgebra.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：inclusion {S T : Subalgebra R A} (h : S <= T) : S ->ₐ[R] T where toFun
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `Submodule.inclusion`, or `Subring.inclusion`
-/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

variable {S T U} (h : S ≤ T)
/-
**Subalgebra.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：inclusion_injective : Function.Injective (inclusion h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem inclusion_injective : Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
/-
**Subalgebra.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：inclusion_self : inclusion (le_refl S) = AlgHom.id R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem inclusion_self : inclusion (le_refl S) = AlgHom.id R S :=
  AlgHom.ext fun _x => Subtype.ext rfl

@[simp]
/-
**Subalgebra.inclusion_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：inclusion_mk (x : A) (hx : x in S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩
参数：x : A；hx : x in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_mk (x : A) (hx : x ∈ S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl
/-
**Subalgebra.inclusion_right** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：inclusion_right (x : T) (m : (x : A) in S) : inclusion h ⟨x, m⟩ = x
参数：x : T；m : (x : A) in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem inclusion_right (x : T) (m : (x : A) ∈ S) : inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
/-
**Subalgebra.inclusion_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：inclusion_inclusion (hst : S <= T) (htu : T <= U) (x : S) : inclusion htu 
(inclusion hst x) = inclusion (le_trans hst htu) x
参数：hst : S <= T；htu : T <= U；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem inclusion_inclusion (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
/-
**Subalgebra.val_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：val_comp_inclusion (hst : S <= T) : T.val.comp (inclusion hst) = S.val
参数：hst : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_comp_inclusion (hst : S ≤ T) :
    T.val.comp (inclusion hst) = S.val :=
  rfl

@[simp]
/-
**Subalgebra.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_inclusion (s : S) : (inclusion h s : A) = s
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion (s : S) : (inclusion h s : A) = s :=
  rfl

namespace inclusion

/-
**Subalgebra.inclusion.isScalarTower_left** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.
inclusion`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] {S T : Subalgebra R A}   (h : S ≤ T) (X : Type u_1) [inst
_3 : SMul X R] [inst_4 : SMul X A] [inst_5 : IsScalarTower X R A],   IsScalarTow
er X ↥S ↥T
参数：h : S ≤ T；X : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SetLike.instIsScalarTowerSubtypeMem`：∀ {S : Type u'} {M : Type v} {N : T
ype u_1} {α : Type u_2} [inst : SetLike S α] [inst_1 : SMul M N] [inst_2 : SMul 
M α]   [inst_3 : Monoid N…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
scoped instance isScalarTower_left (X) [SMul X R] [SMul X A] [IsScalarTower X R A] :
    letI := (inclusion h).toModule; IsScalarTower X S T :=
  letI := (inclusion h).toModule
  ⟨fun x s t ↦ Subtype.ext <| by
    rw [← one_smul R s, ← smul_assoc, one_smul, ← one_smul R (s • t), ← smul_assoc,
      Algebra.smul_def, Algebra.smul_def]
    apply mul_assoc⟩
/-
**Subalgebra.inclusion.isScalarTower_right** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra
.inclusion`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] {S T : Subalgebra R A}   (h : S ≤ T) (X : Type u_1) [inst
_3 : MulAction A X], IsScalarTower (↥S) (↥T) X
参数：h : S ≤ T；X : Type u_1；↥S；↥T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
-/
scoped instance isScalarTower_right (X) [MulAction A X] :
    letI := (inclusion h).toModule; IsScalarTower S T X :=
  letI := (inclusion h).toModule; ⟨fun _ ↦ mul_smul _⟩
/-
**Subalgebra.inclusion.faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra.inclus
ion`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] {S T : Subalgebra R A}   (h : S ≤ T), FaithfulSMul ↥S ↥T
参数：h : S ≤ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
scoped instance faithfulSMul :
    letI := (inclusion h).toModule; FaithfulSMul S T :=
  letI := (inclusion h).toModule
  ⟨fun {x y} h ↦ Subtype.ext <| by
    convert! Subtype.ext_iff.mp (h 1) using 1 <;> exact (mul_one _).symm⟩

end inclusion

variable (S)

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.setCongr`. -/
@[simps apply]
/-
**Subalgebra.equivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T where __
参数：S T : Subalgebra R A；h : S = T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.setCongr`.
-/
def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T where
  __ := LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
/-
**Subalgebra.equivOfEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：equivOfEq_symm (S T : Subalgebra R A) (h : S = T) : (equivOfEq S T h).symm
 = equivOfEq T S h.symm
参数：S T : Subalgebra R A；h : S = T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfEq_symm (S T : Subalgebra R A) (h : S = T) :
    (equivOfEq S T h).symm = equivOfEq T S h.symm := rfl

@[simp]
/-
**Subalgebra.equivOfEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：equivOfEq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem equivOfEq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl := by ext; rfl

@[simp]
/-
**Subalgebra.equivOfEq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) : (eq
uivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU)
参数：S T U : Subalgebra R A；hST : S = T；hTU : T = U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU) := rfl

section equivMapOfInjective

variable (f : A →ₐ[R] B)

/-
**Subalgebra.range_comp_val** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：range_comp_val : (f.comp S.val).range = S.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.range_comp`：range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.com
p f).range = f.range.map g
· 使用定理 `Subalgebra.range_val`：range_val : S.val.range = S
-/
theorem range_comp_val : (f.comp S.val).range = S.map f := by
  rw [AlgHom.range_comp, range_val]

/-- An `AlgHom` between two rings restricts to an `AlgHom` from any subalgebra of the
domain onto the image of that subalgebra. -/
/-
**Subalgebra._root_.AlgHom.subalgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AlgHom` between two rings restricts to an `AlgHom` from any subalgebra of th
e
domain onto the image of that subalgebra.
-/
def _root_.AlgHom.subalgebraMap : S →ₐ[R] S.map f :=
  (f.comp S.val).codRestrict _ fun x ↦ ⟨_, x.2, rfl⟩

variable {S} in
@[simp]
/-
**Subalgebra._root_.AlgHom.subalgebraMap_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Su
balgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.subalgebraMap_coe_apply (x : S) : f.subalgebraMap S x = f x := rfl
/-
**Subalgebra._root_.AlgHom.subalgebraMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `S
ubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.subalgebraMap_surjective : Function.Surjective (f.subalgebraMap S) :=
  f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

variable (hf : Function.Injective f)

/-- A subalgebra is isomorphic to its image under an injective `AlgHom` -/
/-
**Subalgebra.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：equivMapOfInjective : S ≃ₐ[R] S.map f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.range_comp_val`：range_comp_val : (f.comp S.val).range = S.map
 f

--- 原说明 ---
A subalgebra is isomorphic to its image under an injective `AlgHom`
-/
noncomputable def equivMapOfInjective : S ≃ₐ[R] S.map f :=
  (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[simp]
/-
**Subalgebra.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra
`。
形式化陈述：coe_equivMapOfInjective_apply (x : S) : ↑(equivMapOfInjective S f hf x) = 
f x
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivMapOfInjective_apply (x : S) : ↑(equivMapOfInjective S f hf x) = f x := rfl

end equivMapOfInjective

/-! ## Actions by `Subalgebra`s

These are just copies of the definitions about `Subsemiring` starting from
`Subring.mulAction`.
-/


section Actions

variable {α β : Type*}

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance [SMul A α] (S : Subalgebra R A) : SMul S α :=
  inferInstanceAs (SMul S.toSubsemiring α)
/-
**Subalgebra.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A)
 • m
参数：g : S；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := rfl
/-
**Subalgebra.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：smulCommClass_left [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalg
ebra R A) : SMulCommClass S α β
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_left [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A) :
    SMulCommClass S α β :=
  S.toSubsemiring.smulCommClass_left
/-
**Subalgebra.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：smulCommClass_right [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subal
gebra R A) : SMulCommClass α S β
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_right [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A) :
    SMulCommClass α S β :=
  S.toSubsemiring.smulCommClass_right

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
/-
**Subalgebra.isScalarTower_left** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β] 
: IsScalarTower S α β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc
`.
-/
instance isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β] :
    IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) isScalarTower_mid [SMul α R] [SMul α A]
    [IsScalarTower α R A] [SMul A β] [SMul α β] [IsScalarTower α A β] :
    IsScalarTower α S β :=
  ⟨fun a b c ↦ smul_assoc a b.1 c⟩
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) isScalarTower_right [SMul α R] [SMul α A] [IsScalarTower α R A]
    [SMul β R] [SMul β A] [IsScalarTower β R A] [SMul α β] [IsScalarTower α β A] :
    IsScalarTower α β S :=
  ⟨fun a b c ↦ Subtype.ext (smul_assoc a b c.1)⟩
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul A α] [FaithfulSMul A α] (S : Subalgebra R A) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance [MulAction A α] (S : Subalgebra R A) : MulAction S α :=
  inferInstanceAs (MulAction S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance [AddMonoid α] [DistribMulAction A α] (S : Subalgebra R A) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance [Zero α] [SMulWithZero A α] (S : Subalgebra R A) : SMulWithZero S α :=
  inferInstanceAs (SMulWithZero S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance [Zero α] [MulActionWithZero A α] (S : Subalgebra R A) : MulActionWithZero S α :=
  inferInstanceAs (MulActionWithZero S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.moduleLeft** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：moduleLeft [AddCommMonoid α] [Module A α] (S : Subalgebra R A) : Module S 
α
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance moduleLeft [AddCommMonoid α] [Module A α] (S : Subalgebra R A) : Module S α :=
  inferInstanceAs (Module S.toSubsemiring α)

/-- The action by a subalgebra is the action by the underlying algebra. -/
/-
**Subalgebra.toAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toAlgebra {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Al
gebra R A] [Algebra A α] (S : Subalgebra R A) : Algebra S α
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subalgebra is the action by the underlying algebra.
-/
instance toAlgebra {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.toSubsemiring
/-
**Subalgebra.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：algebraMap_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
 [Algebra R A] [Algebra A α] (S : Subalgebra R A) : algebraMap S α = (algebraMap
 A α).comp S.val
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  rfl
/-
**Subalgebra.algebraMap_def** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：algebraMap_def {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α
] [Algebra R A] [Algebra A α] {S : Subalgebra R A} (s : S) : algebraMap S α s = 
algebraMap A α (s : A)
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_def {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
    [Algebra R A] [Algebra A α] {S : Subalgebra R A} (s : S) :
  algebraMap S α s = algebraMap A α (s : A) := rfl

@[simp]
/-
**Subalgebra.algebraMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：algebraMap_mk {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
 [Algebra R A] [Algebra A α] {S : Subalgebra R A} (a : A) (ha : a in S) : algebr
aMap S α (⟨a, ha⟩ : S) = algebraMap A α a
参数：a : A；ha : a in S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_mk {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
    [Algebra R A] [Algebra A α] {S : Subalgebra R A} (a : A) (ha : a ∈ S) :
  algebraMap S α (⟨a, ha⟩ : S) = algebraMap A α a := rfl

@[simp]
/-
**Subalgebra.algebraMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：algebraMap_apply {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra 
R A] (S : Subalgebra R A) (x : S) : algebraMap S A x = x
参数：S : Subalgebra R A；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_apply {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) (x : S) : algebraMap S A x = x :=
  rfl

@[simp]
/-
**Subalgebra.rangeS_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra
 R A] (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.algebraMap_eq`：algebraMap_eq {R A : Type*} [CommSemiring R] [
CommSemiring A] [Semiring α] [Algebra R A] [Algebra A α] (S : Subalgebra R A) : 
algebraMap S α…
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.toSubsemiring_subtype`：toSubsemiring_subtype : S.toSubsemirin
g.subtype = (S.val : S ->+* A)
· 使用定理 `Subsemiring.rangeS_subtype`：rangeS_subtype (s : Subsemiring R) : s.subty
pe.rangeS = s
-/
theorem rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring := by
  rw [algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← toSubsemiring_subtype,
    Subsemiring.rangeS_subtype]

@[simp]
/-
**Subalgebra.range_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S 
: Subalgebra R A) : (algebraMap S A).range = S.toSubring
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.algebraMap_eq`：algebraMap_eq {R A : Type*} [CommSemiring R] [
CommSemiring A] [Semiring α] [Algebra R A] [Algebra A α] (S : Subalgebra R A) : 
algebraMap S α…
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.toSubring_subtype`：toSubring_subtype {R A : Type*} [CommRing 
R] [Ring A] [Algebra R A] (S : Subalgebra R A) : S.toSubring.subtype = (S.val : 
S ->+* A)
· 使用定理 `Subring.range_subtype`：range_subtype (s : Subring R) : s.subtype.range =
 s
-/
theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← toSubring_subtype,
    Subring.range_subtype]

@[simp]
/-
**Subalgebra.setRange_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：setRange_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algeb
ra R A] (S : Subalgebra R A) : Set.range (algebraMap S A) = (S : Set A)
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Subalgebra.rangeS_algebraMap`：rangeS_algebraMap {R A : Type*} [CommSemir
ing R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) : (algebraMap S A).ra
ngeS = S.toSubsemi…
-/
lemma setRange_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : Set.range (algebraMap S A) = (S : Set A) :=
  SetLike.ext'_iff.mp S.rangeS_algebraMap
/-
**Subalgebra.instIsTorsionFree'** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：instIsTorsionFree' [IsDomain A] (S : Subalgebra R A) : IsTorsionFree S A
参数：S : Subalgebra R A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.IsTorsionFree.comap`：Module.IsTorsionFree.comap [IsTorsionFree S 
M] (f : R -> S) (isRegular : forall r, IsRegular r -> IsRegular (f r)) (smul : f
orall (r : R) (m…
· 使用定理 `instIsTorsionFree`：∀ {R : Type u_1} [inst : Semiring R], Module.IsTorsio
nFree R R
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance instIsTorsionFree' [IsDomain A] (S : Subalgebra R A) : IsTorsionFree S A :=
  .comap Subtype.val (fun r hr ↦ by simpa [isRegular_iff_ne_zero] using hr.ne_zero)
    (by simp [smul_def])

end Actions

section Center

/-
**Subalgebra._root_.Set.algebraMap_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Subalge
bra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.algebraMap_mem_center (r : R) : algebraMap R A r ∈ Set.center A := by
  simp only [Semigroup.mem_center_iff, commutes, forall_const]

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
@[simps! coe toSubsemiring]
/-
**Subalgebra.center** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：center : Subalgebra R A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.algebraMap_mem_center`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R),   (algebraMap R A) 
r ∈ Set.center …

--- 原说明 ---
The center of an algebra is the set of elements which commute with every element
. They form a
subalgebra.
-/
def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

@[simp]
/-
**Subalgebra.center_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] : (cent
er R A).toSubring = Subring.center A
参数：R A : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl

variable {R A}
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (center R A) :=
  inferInstanceAs (CommSemiring (Subsemiring.center A))
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [Ring A] [Algebra R A] : CommRing (center R A) :=
  inferInstanceAs (CommRing (Subring.center A))
/-
**Subalgebra.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_center_iff {a : A} : a in center R A ↔ forall b : A, b * a = a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ fo
rall g, g * z = z * g
-/
theorem mem_center_iff {a : A} : a ∈ center R A ↔ ∀ b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff

end Center

section Centralizer

@[simp]
/-
**Subalgebra._root_.Set.algebraMap_mem_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Su
balgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.algebraMap_mem_centralizer {s : Set A} (r : R) :
    algebraMap R A r ∈ s.centralizer :=
  fun _a _h => (Algebra.commutes _ _).symm

variable (R)

/-- The centralizer of a set as a subalgebra. -/
/-
**Subalgebra.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：centralizer (s : Set A) : Subalgebra R A
参数：s : Set A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.algebraMap_mem_centralizer`：∀ {R : Type u} {A : Type v} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {s : Set A} (r : R),   
(algebraMap R A) r ∈…

--- 原说明 ---
The centralizer of a set as a subalgebra.
-/
def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }

@[simp, norm_cast]
/-
**Subalgebra.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl
/-
**Subalgebra.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_centralizer_iff {s : Set A} {z : A} : z in centralizer R s ↔ forall g 
in s, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ centralizer R s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
/-
**Subalgebra.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：center_le_centralizer (s) : center R A <= centralizer R s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer (s) : center R A ≤ centralizer R s :=
  s.center_subset_centralizer
/-
**Subalgebra.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centr
alizer R s
参数：s t : Set A；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le (s t : Set A) (h : s ⊆ t) : centralizer R t ≤ centralizer R s :=
  Set.centralizer_subset h

@[simp]
/-
**Subalgebra.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_univ : centralizer R Set.univ = center R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)
/-
**Subalgebra.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：le_centralizer_centralizer {s : Subalgebra R A} : s <= centralizer R (cent
ralizer R (s : Set A))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma le_centralizer_centralizer {s : Subalgebra R A} :
    s ≤ centralizer R (centralizer R (s : Set A)) :=
  Set.subset_centralizer_centralizer

@[simp]
/-
**Subalgebra.centralizer_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Suba
lgebra`。
形式化陈述：centralizer_centralizer_centralizer {s : Set A} : centralizer R s.centrali
zer.centralizer = centralizer R s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.centralizer_centralizer_centralizer`：centralizer_centralizer_central
izer (S : Set M) : S.centralizer.centralizer.centralizer = S.centralizer
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralizer_centralizer_centralizer {s : Set A} :
    centralizer R s.centralizer.centralizer = centralizer R s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end Centralizer

end Subalgebra

section Nat

variable {R : Type*} [Semiring R]

/-- A subsemiring is an `ℕ`-subalgebra. -/
@[simps toSubsemiring]
/-
**subalgebraOfSubsemiring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra Nat R
参数：S : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring is an `ℕ`-subalgebra.
-/
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebraMap_mem' := fun i => natCast_mem S i }

@[simp]
/-
**mem_subalgebraOfSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} : x in subalgebraO
fSubsemiring S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} :
    x ∈ subalgebraOfSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [Ring R]

/-- A subring is a `ℤ`-subalgebra. -/
@[simps toSubsemiring]
/-
**subalgebraOfSubring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subalgebraOfSubring (S : Subring R) : Subalgebra Int R
参数：S : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring is a `ℤ`-subalgebra.
-/
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simp)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : ℤ) : R) ∈ S by
          rw [Int.cast_sub, Int.cast_one]
          exact S.sub_mem ih S.one_mem }

variable {S : Type*} [Semiring S]

@[simp]
/-
**mem_subalgebraOfSubring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_subalgebraOfSubring {x : R} {S : Subring R} : x in subalgebraOfSubring
 S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subalgebraOfSubring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S :=
  Iff.rfl

end Int

section Equalizer

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The equalizer of two R-algebra homomorphisms -/
@[simps coe toSubsemiring]
/-
**AlgHom.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：equalizer (ϕ ψ : A ->ₐ[R] B) : Subalgebra R A where carrier
参数：ϕ ψ : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of two R-algebra homomorphisms
-/
def equalizer (ϕ ψ : A →ₐ[R] B) : Subalgebra R A where
  carrier := { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq, map_add, map_add, hx, hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq, map_mul, map_mul, hx, hy]
  algebraMap_mem' x := by
    simp only [Set.mem_ofPred_eq, AlgHomClass.commutes]

@[simp]
/-
**AlgHom.mem_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mem_equalizer (φ ψ : A ->ₐ[R] B) (x : A) : x in equalizer φ ψ ↔ φ x = ψ x
参数：φ ψ : A ->ₐ[R] B；x : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_equalizer (φ ψ : A →ₐ[R] B) (x : A) : x ∈ equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl
/-
**AlgHom.equalizer_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：equalizer_toSubmodule {φ ψ : A ->ₐ[R] B} : Subalgebra.toSubmodule (equaliz
er φ ψ) = LinearMap.eqLocus (LinearMapClass.linearMap φ) (LinearMapClass.linearM
ap ψ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizer_toSubmodule {φ ψ : A →ₐ[R] B} :
    Subalgebra.toSubmodule (equalizer φ ψ) = LinearMap.eqLocus
      (LinearMapClass.linearMap φ) (LinearMapClass.linearMap ψ) := rfl
/-
**AlgHom.le_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：le_equalizer {φ ψ : A ->ₐ[R] B} {S : Subalgebra R A} : S <= equalizer φ ψ 
↔ Set.EqOn φ ψ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_equalizer {φ ψ : A →ₐ[R] B} {S : Subalgebra R A} :
    S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-
**Subalgebra.comap_map_eq_self_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a`。
形式化陈述：comap_map_eq_self_of_injective {f : A ->ₐ[R] B} (hf : Function.Injective f
) (S : Subalgebra R A) : (S.map f).comap f = S
参数：hf : Function.Injective f；S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem comap_map_eq_self_of_injective
    {f : A →ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subalgebra

end MapComap

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Turn a non-unital subalgebra containing `1` into a subalgebra. -/
/-
**NonUnitalSubalgebra.toSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : 
A) in S) : Subalgebra R A
参数：S : NonUnitalSubalgebra R A；h1 : (1 : A) in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a non-unital subalgebra containing `1` into a subalgebra.
-/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) ∈ S) :
    Subalgebra R A :=
  { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }
/-
**Subalgebra.toNonUnitalSubalgebra_toSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) : S.toN
onUnitalSubalgebra.toSubalgebra S.one_mem = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl
/-
**NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubal
gebra R A) (h1 : (1 : A) in S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUn
italSubalgebra = S
参数：S : NonUnitalSubalgebra R A；h1 : (1 : A) in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) ∈ S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by
  cases S; rfl
