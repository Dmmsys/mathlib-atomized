/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.Algebra.Module.Opposite

/-!
# Conjugations

This file defines the grade reversal and grade involution functions on multivectors, `reverse` and
`involute`.
Together, these operations compose to form the "Clifford conjugate", hence the name of this file.

https://en.wikipedia.org/wiki/Clifford_algebra#Antiautomorphisms

## Main definitions

* `CliffordAlgebra.involute`: the grade involution, negating each basis vector
* `CliffordAlgebra.reverse`: the grade reversion, reversing the order of a product of vectors

## Main statements

* `CliffordAlgebra.involute_involutive`
* `CliffordAlgebra.reverse_involutive`
* `CliffordAlgebra.reverse_involute_commute`
* `CliffordAlgebra.involute_mem_evenOdd_iff`
* `CliffordAlgebra.reverse_mem_evenOdd_iff`

-/

@[expose] public section


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

section Involute

/-- Grade involution, inverting the sign of each basis vector. -/
/-
**CliffordAlgebra.involute** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Grade involution, inverting the sign of each basis vector.
-/
def involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift Q ⟨-ι Q, fun m => by simp⟩

@[simp]
/-
**CliffordAlgebra.involute_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  lift_ι_apply _ _ m

@[simp]
/-
**CliffordAlgebra.involute_comp_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlge
bra`。
形式化陈述：involute_comp_involute : involute.comp involute = AlgHom.id R (CliffordAlg
ebra Q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem involute_comp_involute : involute.comp involute = AlgHom.id R (CliffordAlgebra Q) := by
  ext; simp
/-
**CliffordAlgebra.involute_involutive** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
`。
形式化陈述：involute_involutive : Function.Involutive (involute : _ -> CliffordAlgebra
 Q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebra.involute_comp_involute`：involute_comp_involute : involut
e.comp involute = AlgHom.id R (CliffordAlgebra Q)
-/
theorem involute_involutive : Function.Involutive (involute : _ → CliffordAlgebra Q) :=
  AlgHom.congr_fun involute_comp_involute

@[simp]
/-
**CliffordAlgebra.involute_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：involute_involute : forall a : CliffordAlgebra Q, involute (involute a) = 
a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.involute_involutive`：involute_involutive : Function.Invo
lutive (involute : _ -> CliffordAlgebra Q)
-/
theorem involute_involute : ∀ a : CliffordAlgebra Q, involute (involute a) = a :=
  involute_involutive

/-- `CliffordAlgebra.involute` as an `AlgEquiv`. -/
@[simps!]
/-
**CliffordAlgebra.involuteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：involuteEquiv : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CliffordAlgebra.involute` as an `AlgEquiv`.
-/
def involuteEquiv : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom involute involute (AlgHom.ext <| involute_involute)
    (AlgHom.ext <| involute_involute)

end Involute

section Reverse

open MulOpposite

/-- `CliffordAlgebra.reverse` as an `AlgHom` to the opposite algebra -/
/-
**CliffordAlgebra.reverseOp** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：reverseOp : CliffordAlgebra Q ->ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CliffordAlgebra.reverse` as an `AlgHom` to the opposite algebra
-/
def reverseOp : CliffordAlgebra Q →ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  CliffordAlgebra.lift Q
    ⟨(MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ ι Q, fun m => unop_injective <| by simp⟩

@[simp]
/-
**CliffordAlgebra.reverseOp_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverseOp_ι (m : M) : reverseOp (ι Q m) = op (ι Q m) := lift_ι_apply _ _ _

/-- `CliffordAlgebra.reverseEquiv` as an `AlgEquiv` to the opposite algebra -/
@[simps! apply]
/-
**CliffordAlgebra.reverseOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：reverseOpEquiv : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CliffordAlgebra.reverseEquiv` as an `AlgEquiv` to the opposite algebra
-/
def reverseOpEquiv : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom reverseOp (AlgHom.opComm reverseOp)
    (AlgHom.unop.injective <| hom_ext <| LinearMap.ext fun _ => by simp)
    (hom_ext <| LinearMap.ext fun _ => by simp)

@[simp]
/-
**CliffordAlgebra.reverseOpEquiv_opComm** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：reverseOpEquiv_opComm : AlgEquiv.opComm (reverseOpEquiv (Q
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverseOpEquiv_opComm :
    AlgEquiv.opComm (reverseOpEquiv (Q := Q)) = reverseOpEquiv.symm := rfl

/-- Grade reversion, inverting the multiplication order of basis vectors.
Also called *transpose* in some literature. -/
/-
**CliffordAlgebra.reverse** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Grade reversion, inverting the multiplication order of basis vectors.
Also called *transpose* in some literature.
-/
def reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (opLinearEquiv R).symm.toLinearMap.comp reverseOp.toLinearMap
/-
**CliffordAlgebra.unop_reverseOp** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} (x : CliffordAlgebra 
Q),   MulOpposite.unop (CliffordAlgebra.reverseOp x) = CliffordAlgebra.reverse x
参数：x : CliffordAlgebra Q；CliffordAlgebra.reverseOp x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem unop_reverseOp (x : CliffordAlgebra Q) : (reverseOp x).unop = reverse x := rfl
/-
**CliffordAlgebra.op_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} (x : CliffordAlgebra 
Q),   MulOpposite.op (CliffordAlgebra.reverse x) = CliffordAlgebra.reverseOp x
参数：x : CliffordAlgebra Q；CliffordAlgebra.reverse x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem op_reverse (x : CliffordAlgebra Q) : op (reverse x) = reverseOp x := rfl

@[simp]
/-
**CliffordAlgebra.reverse_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_ι (m : M) : reverse (ι Q m) = ι Q m := by simp [reverse]

@[simp]
/-
**CliffordAlgebra.reverse.commutes** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.re
verse`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} (r : R),   CliffordAl
gebra.reverse ((algebraMap R (CliffordAlgebra Q)) r) = (algebraMap R (CliffordAl
gebra Q)) r
参数：r : R；(algebraMap R (CliffordAlgebra Q)) r；algebraMap R (CliffordAlgebra Q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem reverse.commutes (r : R) :
    reverse (algebraMap R (CliffordAlgebra Q) r) = algebraMap R _ r :=
  op_injective <| reverseOp.commutes r

@[simp]
/-
**CliffordAlgebra.reverse.map_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.rev
erse`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M}, CliffordAlgebra.reve
rse 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
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
protected theorem reverse.map_one : reverse (1 : CliffordAlgebra Q) = 1 :=
  op_injective (map_one reverseOp)

@[simp]
/-
**CliffordAlgebra.reverse.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.rev
erse`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} (a b : CliffordAlgebr
a Q),   CliffordAlgebra.reverse (a * b) = CliffordAlgebra.reverse b * CliffordAl
gebra.reverse a
参数：a b : CliffordAlgebra Q；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
protected theorem reverse.map_mul (a b : CliffordAlgebra Q) :
    reverse (a * b) = reverse b * reverse a :=
  op_injective (map_mul reverseOp a b)

@[simp]
/-
**CliffordAlgebra.reverse_involutive** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
形式化陈述：reverse_involutive : Function.Involutive (reverse (Q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `AlgEquiv.symm_comp`：symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e
 : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁
-/
theorem reverse_involutive : Function.Involutive (reverse (Q := Q)) :=
  AlgHom.congr_fun reverseOpEquiv.symm_comp

@[simp]
/-
**CliffordAlgebra.reverse_comp_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a`。
形式化陈述：reverse_comp_reverse : reverse.comp reverse = (LinearMap.id : _ ->ₗ[R] Cli
ffordAlgebra Q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebra.reverse_involutive`：reverse_involutive : Function.Involu
tive (reverse (Q
-/
theorem reverse_comp_reverse :
    reverse.comp reverse = (LinearMap.id : _ →ₗ[R] CliffordAlgebra Q) :=
  LinearMap.ext reverse_involutive

@[simp]
/-
**CliffordAlgebra.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：reverse_reverse : forall a : CliffordAlgebra Q, reverse (reverse a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.reverse_involutive`：reverse_involutive : Function.Involu
tive (reverse (Q
-/
theorem reverse_reverse : ∀ a : CliffordAlgebra Q, reverse (reverse a) = a :=
  reverse_involutive

/-- `CliffordAlgebra.reverse` as a `LinearEquiv`. -/
@[simps!]
/-
**CliffordAlgebra.reverseEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：reverseEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.reverse_involutive`：reverse_involutive : Function.Involu
tive (reverse (Q

--- 原说明 ---
`CliffordAlgebra.reverse` as a `LinearEquiv`.
-/
def reverseEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q :=
  LinearEquiv.ofInvolutive reverse reverse_involutive
/-
**CliffordAlgebra.reverse_comp_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：reverse_comp_involute : reverse.comp involute.toLinearMap = (involute.toLi
nearMap.comp reverse : _ ->ₗ[R] CliffordAlgebra Q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebra.induction`：induction {C : CliffordAlgebra Q -> Prop} (al
gebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι
 Q x)) (mul : f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem reverse_comp_involute :
    reverse.comp involute.toLinearMap =
      (involute.toLinearMap.comp reverse : _ →ₗ[R] CliffordAlgebra Q) := by
  ext x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  induction x using CliffordAlgebra.induction with
  | algebraMap => simp
  | ι => simp
  | mul a b ha hb => simp only [ha, hb, reverse.map_mul, map_mul]
  | add a b ha hb => simp only [ha, hb, reverse.map_add, map_add]

/-- `CliffordAlgebra.reverse` and `CliffordAlgebra.involute` commute. Note that the composition
is sometimes referred to as the "clifford conjugate". -/
/-
**CliffordAlgebra.reverse_involute_commute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAl
gebra`。
形式化陈述：reverse_involute_commute : Function.Commute (reverse (Q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `CliffordAlgebra.reverse_comp_involute`：reverse_comp_involute : reverse.c
omp involute.toLinearMap = (involute.toLinearMap.comp reverse : _ ->ₗ[R] Cliffor
dAlgebra Q)

--- 原说明 ---
`CliffordAlgebra.reverse` and `CliffordAlgebra.involute` commute. Note that the 
composition
is sometimes referred to as the "clifford conjugate".
-/
theorem reverse_involute_commute : Function.Commute (reverse (Q := Q)) involute :=
  LinearMap.congr_fun reverse_comp_involute
/-
**CliffordAlgebra.reverse_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：reverse_involute : forall a : CliffordAlgebra Q, reverse (involute a) = in
volute (reverse a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.reverse_involute_commute`：reverse_involute_commute : Fun
ction.Commute (reverse (Q
-/
theorem reverse_involute :
    ∀ a : CliffordAlgebra Q, reverse (involute a) = involute (reverse a) :=
  reverse_involute_commute

end Reverse

/-!
### Statements about conjugations of products of lists
-/


section List

/-- Taking the reverse of the product a list of $n$ vectors lifted via `ι` is equivalent to
taking the product of the reverse of that list. -/
/-
**CliffordAlgebra.reverse_prod_map_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the reverse of the product a list of $n$ vectors lifted via `ι` is equiva
lent to
taking the product of the reverse of that list.
-/
theorem reverse_prod_map_ι :
    ∀ l : List M, reverse (l.map <| ι Q).prod = (l.map <| ι Q).reverse.prod
  | [] => by simp
  | x::xs => by simp [reverse_prod_map_ι xs]

/-- Taking the involute of the product a list of $n$ vectors lifted via `ι` is equivalent to
premultiplying by ${-1}^n$. -/
/-
**CliffordAlgebra.involute_prod_map_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the involute of the product a list of $n$ vectors lifted via `ι` is equiv
alent to
premultiplying by ${-1}^n$.
-/
theorem involute_prod_map_ι :
    ∀ l : List M, involute (l.map <| ι Q).prod = (-1 : R) ^ l.length • (l.map <| ι Q).prod
  | [] => by simp
  | x::xs => by simp [pow_succ, involute_prod_map_ι xs]

end List

/-!
### Statements about `Submodule.map` and `Submodule.comap`
-/


section Submodule

variable (Q)

section Involute

/-
**CliffordAlgebra.submodule_map_involute_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Cli
ffordAlgebra`。
形式化陈述：submodule_map_involute_eq_comap (p : Submodule R (CliffordAlgebra Q)) : p.
map (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap = p.coma
p (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap
参数：p : Submodule R (CliffordAlgebra Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
-/
theorem submodule_map_involute_eq_comap (p : Submodule R (CliffordAlgebra Q)) :
    p.map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      p.comap (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap :=
  Submodule.map_equiv_eq_comap_symm involuteEquiv.toLinearEquiv _

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_map_involute :
    (LinearMap.range (ι Q)).map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      LinearMap.range (ι Q) :=
  (ι_range_map_lift _ _).trans (LinearMap.range_neg _)

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_comap_involute :
    (LinearMap.range (ι Q)).comap
      (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      LinearMap.range (ι Q) := by
  rw [← submodule_map_involute_eq_comap, ι_range_map_involute]

@[simp]
/-
**CliffordAlgebra.evenOdd_map_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a`。
形式化陈述：evenOdd_map_involute (n : ZMod 2) : (evenOdd Q n).map (involute : Clifford
Algebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap = evenOdd Q n
参数：n : ZMod 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.map_pow`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A)   {A' : Type u_1
} [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.ι_range_map_involute`：ι_range_map_involute : (LinearMap.
range (ι Q)).map (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinea
rMap = LinearMap.range (ι …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evenOdd_map_involute (n : ZMod 2) :
    (evenOdd Q n).map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      evenOdd Q n := by
  simp_rw [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_involute]

@[simp]
/-
**CliffordAlgebra.evenOdd_comap_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlge
bra`。
形式化陈述：evenOdd_comap_involute (n : ZMod 2) : (evenOdd Q n).comap (involute : Clif
fordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap = evenOdd Q n
参数：n : ZMod 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.submodule_map_involute_eq_comap`：submodule_map_involute_
eq_comap (p : Submodule R (CliffordAlgebra Q)) : p.map (involute : CliffordAlgeb
ra Q ->ₐ[R] CliffordAlgebra Q).toLine…
· 使用定理 `CliffordAlgebra.evenOdd_map_involute`：evenOdd_map_involute (n : ZMod 2) 
: (evenOdd Q n).map (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLi
nearMap = evenOdd Q n
-/
theorem evenOdd_comap_involute (n : ZMod 2) :
    (evenOdd Q n).comap (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      evenOdd Q n := by
  rw [← submodule_map_involute_eq_comap, evenOdd_map_involute]

end Involute

section Reverse

/-
**CliffordAlgebra.submodule_map_reverse_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Clif
fordAlgebra`。
形式化陈述：submodule_map_reverse_eq_comap (p : Submodule R (CliffordAlgebra Q)) : p.m
ap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = p.comap (reverse : C
liffordAlgebra Q ->ₗ[R] CliffordAlgebra Q)
参数：p : Submodule R (CliffordAlgebra Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
-/
theorem submodule_map_reverse_eq_comap (p : Submodule R (CliffordAlgebra Q)) :
    p.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      p.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) :=
  Submodule.map_equiv_eq_comap_symm (reverseEquiv : _ ≃ₗ[R] _) _

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_map_reverse :
    (LinearMap.range (ι Q)).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q)
      = LinearMap.range (ι Q) := by
  rw [reverse, reverseOp, Submodule.map_comp, ι_range_map_lift, LinearMap.range_comp,
    ← Submodule.map_comp]
  exact Submodule.map_id _

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_comap_reverse :
    (LinearMap.range (ι Q)).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q)
      = LinearMap.range (ι Q) := by
  rw [← submodule_map_reverse_eq_comap, ι_range_map_reverse]

/-- Like `Submodule.map_mul`, but with the multiplication reversed. -/
/-
**CliffordAlgebra.submodule_map_mul_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra`。
形式化陈述：submodule_map_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) : (p * q
).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = q.map (reverse : 
CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) * p.map (reverse : CliffordAlgebra Q
 ->ₗ[R] CliffordAlgebra Q)
参数：p q : Submodule R (CliffordAlgebra Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_mul`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M N : Submodule R A)   {A' : Type u
_1} [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_unop_mul`：map_unop_mul (M N : Submodule R Aᵐᵒᵖ) : map (↑(o
pLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M * N) = map (↑(opLinearEq
uiv R : A ≃ₗ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Like `Submodule.map_mul`, but with the multiplication reversed.
-/
theorem submodule_map_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) :
    (p * q).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      q.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) *
        p.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_mul, Submodule.map_unop_mul]
/-
**CliffordAlgebra.submodule_comap_mul_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：submodule_comap_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) : (p *
 q).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = q.comap (reve
rse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) * p.comap (reverse : CliffordA
lgebra Q ->ₗ[R] CliffordAlgebra Q)
参数：p q : Submodule R (CliffordAlgebra Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CliffordAlgebra.submodule_map_mul_reverse`：submodule_map_mul_reverse (p 
q : Submodule R (CliffordAlgebra Q)) : (p * q).map (reverse : CliffordAlgebra Q 
->ₗ[R] CliffordAlgebra Q) = q.m…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submodule_comap_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) :
    (p * q).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      q.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) *
        p.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_mul_reverse]

/-- Like `Submodule.map_pow` -/
/-
**CliffordAlgebra.submodule_map_pow_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra`。
形式化陈述：submodule_map_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : Nat) 
: (p ^ n).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = p.map (re
verse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) ^ n
参数：p : Submodule R (CliffordAlgebra Q)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_pow`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A)   {A' : Type u_1
} [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_unop_pow`：map_unop_pow (n : Nat) (M : Submodule R Aᵐᵒᵖ) : 
map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M ^ n) = map (↑(op
LinearEquiv …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Like `Submodule.map_pow`
-/
theorem submodule_map_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : ℕ) :
    (p ^ n).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      p.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) ^ n := by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_pow, Submodule.map_unop_pow]
/-
**CliffordAlgebra.submodule_comap_pow_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：submodule_comap_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : Nat
) : (p ^ n).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = p.com
ap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) ^ n
参数：p : Submodule R (CliffordAlgebra Q)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.submodule_map_pow_reverse`：submodule_map_pow_reverse (p 
: Submodule R (CliffordAlgebra Q)) (n : Nat) : (p ^ n).map (reverse : CliffordAl
gebra Q ->ₗ[R] CliffordAlgebra …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submodule_comap_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : ℕ) :
    (p ^ n).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      p.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) ^ n := by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_pow_reverse]

@[simp]
/-
**CliffordAlgebra.evenOdd_map_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
`。
形式化陈述：evenOdd_map_reverse (n : ZMod 2) : (evenOdd Q n).map (reverse : CliffordAl
gebra Q ->ₗ[R] CliffordAlgebra Q) = evenOdd Q n
参数：n : ZMod 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CliffordAlgebra.submodule_map_pow_reverse`：submodule_map_pow_reverse (p 
: Submodule R (CliffordAlgebra Q)) (n : Nat) : (p ^ n).map (reverse : CliffordAl
gebra Q ->ₗ[R] CliffordAlgebra …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.ι_range_map_reverse`：ι_range_map_reverse : (LinearMap.ra
nge (ι Q)).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = LinearMa
p.range (ι Q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evenOdd_map_reverse (n : ZMod 2) :
    (evenOdd Q n).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) = evenOdd Q n := by
  simp_rw [evenOdd, Submodule.map_iSup, submodule_map_pow_reverse, ι_range_map_reverse]

@[simp]
/-
**CliffordAlgebra.evenOdd_comap_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：evenOdd_comap_reverse (n : ZMod 2) : (evenOdd Q n).comap (reverse : Cliffo
rdAlgebra Q ->ₗ[R] CliffordAlgebra Q) = evenOdd Q n
参数：n : ZMod 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.submodule_map_reverse_eq_comap`：submodule_map_reverse_eq
_comap (p : Submodule R (CliffordAlgebra Q)) : p.map (reverse : CliffordAlgebra 
Q ->ₗ[R] CliffordAlgebra Q) = p.coma…
· 使用定理 `CliffordAlgebra.evenOdd_map_reverse`：evenOdd_map_reverse (n : ZMod 2) : 
(evenOdd Q n).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = evenO
dd Q n
-/
theorem evenOdd_comap_reverse (n : ZMod 2) :
    (evenOdd Q n).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) = evenOdd Q n := by
  rw [← submodule_map_reverse_eq_comap, evenOdd_map_reverse]

end Reverse

@[simp]
/-
**CliffordAlgebra.involute_mem_evenOdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAl
gebra`。
形式化陈述：involute_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} : involute x
 in evenOdd Q n ↔ x in evenOdd Q n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `CliffordAlgebra.evenOdd_comap_involute`：evenOdd_comap_involute (n : ZMod
 2) : (evenOdd Q n).comap (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q
).toLinearMap = evenOdd Q n
-/
theorem involute_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} :
    involute x ∈ evenOdd Q n ↔ x ∈ evenOdd Q n :=
  SetLike.ext_iff.mp (evenOdd_comap_involute Q n) x

@[simp]
/-
**CliffordAlgebra.reverse_mem_evenOdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlg
ebra`。
形式化陈述：reverse_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} : reverse x i
n evenOdd Q n ↔ x in evenOdd Q n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `CliffordAlgebra.evenOdd_comap_reverse`：evenOdd_comap_reverse (n : ZMod 2
) : (evenOdd Q n).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) =
 evenOdd Q n
-/
theorem reverse_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} :
    reverse x ∈ evenOdd Q n ↔ x ∈ evenOdd Q n :=
  SetLike.ext_iff.mp (evenOdd_comap_reverse Q n) x

end Submodule

/-!
### Related properties of the even and odd submodules

TODO: show that these are `iff`s when `Invertible (2 : R)`.
-/


/-
**CliffordAlgebra.involute_eq_of_mem_even** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlg
ebra`。
形式化陈述：involute_eq_of_mem_even {x : CliffordAlgebra Q} (h : x in evenOdd Q 0) : i
nvolute x = x
参数：h : x in evenOdd Q 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.even_induction`：even_induction {motive : forall x, x in 
evenOdd Q 0 -> Prop} (algebraMap : forall r : R, motive (algebraMap _ _ r) (SetL
ike.algebraMap_mem_g…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b

--- 原说明 ---
### Related properties of the even and odd submodules

TODO: show that these are `iff`s when `Invertible (2 : R)`.
-/
theorem involute_eq_of_mem_even {x : CliffordAlgebra Q} (h : x ∈ evenOdd Q 0) : involute x = x := by
  induction x, h using even_induction with
  | algebraMap r => exact AlgHom.commutes _ _
  | add x y _hx _hy ihx ihy =>
    rw [map_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul, map_mul, involute_ι, involute_ι, ihx, neg_mul_neg]
/-
**CliffordAlgebra.involute_eq_of_mem_odd** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlge
bra`。
形式化陈述：involute_eq_of_mem_odd {x : CliffordAlgebra Q} (h : x in evenOdd Q 1) : in
volute x = -x
参数：h : x in evenOdd Q 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.odd_induction`：odd_induction {P : forall x, x in evenOdd
 Q 1 -> Prop} (ι : forall v, P (ι Q v) (ι_mem_evenOdd_one _ _)) (add : forall x 
y hx hy, P x hx -> …
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem involute_eq_of_mem_odd {x : CliffordAlgebra Q} (h : x ∈ evenOdd Q 1) : involute x = -x := by
  induction x, h using odd_induction with
  | ι m => exact involute_ι _
  | add x y _hx _hy ihx ihy =>
    rw [map_add, ihx, ihy, neg_add]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul, map_mul, involute_ι, involute_ι, ihx, neg_mul_neg, mul_neg]

end CliffordAlgebra

