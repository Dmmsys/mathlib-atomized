/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/

@[expose] public section

-- Porting note: used to import `tactic.pi_instances`

namespace Pi

universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

variable (i : I)

/-
**Pi.distrib** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：distrib [forall i, Distrib <| f i] : Distrib (forall i : I, f i) where lef
t_distrib
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distrib [∀ i, Distrib <| f i] : Distrib (∀ i : I, f i) where
  left_distrib := by intros; ext; exact mul_add _ _ _
  right_distrib := by intros; ext; exact add_mul _ _ _
/-
**Pi.hasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：hasDistribNeg [forall i, Mul (f i)] [forall i, HasDistribNeg (f i)] : HasD
istribNeg (forall i, f i) where neg_mul _ _
参数：f i；f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasDistribNeg [∀ i, Mul (f i)] [∀ i, HasDistribNeg (f i)] : HasDistribNeg (∀ i, f i) where
  neg_mul _ _ := funext fun _ ↦ neg_mul _ _
  mul_neg _ _ := funext fun _ ↦ mul_neg _ _
/-
**Pi.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：addMonoidWithOne [forall i, AddMonoidWithOne (f i)] : AddMonoidWithOne (fo
rall i, f i) where natCast n _
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne [∀ i, AddMonoidWithOne (f i)] : AddMonoidWithOne (∀ i, f i) where
  natCast n _ := n
  natCast_zero := funext fun _ ↦ AddMonoidWithOne.natCast_zero
  natCast_succ n := funext fun _ ↦ AddMonoidWithOne.natCast_succ n
/-
**Pi.addGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：addGroupWithOne [forall i, AddGroupWithOne (f i)] : AddGroupWithOne (foral
l i, f i) where __
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroupWithOne [∀ i, AddGroupWithOne (f i)] : AddGroupWithOne (∀ i, f i) where
  __ := addGroup
  __ := addMonoidWithOne
  intCast n _ := n
  intCast_ofNat n := funext fun _ ↦ AddGroupWithOne.intCast_ofNat n
  intCast_negSucc n := funext fun _ ↦ AddGroupWithOne.intCast_negSucc n
/-
**Pi.nonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonUnitalNonAssocSemiring [forall i, NonUnitalNonAssocSemiring <| f i] : N
onUnitalNonAssocSemiring (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalNonAssocSemiring [∀ i, NonUnitalNonAssocSemiring <| f i] :
    NonUnitalNonAssocSemiring (∀ i : I, f i) :=
  { Pi.distrib, Pi.addCommMonoid, Pi.mulZeroClass with }
/-
**Pi.nonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonUnitalSemiring [forall i, NonUnitalSemiring <| f i] : NonUnitalSemiring
 (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalSemiring [∀ i, NonUnitalSemiring <| f i] : NonUnitalSemiring (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocSemiring, Pi.semigroupWithZero with }
/-
**Pi.nonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonAssocSemiring [forall i, NonAssocSemiring <| f i] : NonAssocSemiring (f
orall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocSemiring, Pi.mulZeroOneClass, Pi.addMonoidWithOne with }
/-
**Pi.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：semiring [forall i, Semiring <| f i] : Semiring (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring [∀ i, Semiring <| f i] : Semiring (∀ i : I, f i) :=
  { Pi.nonUnitalSemiring, Pi.nonAssocSemiring, Pi.monoidWithZero with }
/-
**Pi.nonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonUnitalCommSemiring [forall i, NonUnitalCommSemiring <| f i] : NonUnital
CommSemiring (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalCommSemiring [∀ i, NonUnitalCommSemiring <| f i] :
    NonUnitalCommSemiring (∀ i : I, f i) :=
  { Pi.nonUnitalSemiring, Pi.commSemigroup with }
/-
**Pi.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：commSemiring [forall i, CommSemiring <| f i] : CommSemiring (forall i : I,
 f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemiring [∀ i, CommSemiring <| f i] : CommSemiring (∀ i : I, f i) :=
  { Pi.semiring, Pi.commMonoid with }
/-
**Pi.nonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonUnitalNonAssocRing [forall i, NonUnitalNonAssocRing <| f i] : NonUnital
NonAssocRing (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalNonAssocRing [∀ i, NonUnitalNonAssocRing <| f i] :
    NonUnitalNonAssocRing (∀ i : I, f i) :=
  { Pi.addCommGroup, Pi.nonUnitalNonAssocSemiring with }
/-
**Pi.nonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonUnitalRing [forall i, NonUnitalRing <| f i] : NonUnitalRing (forall i :
 I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalRing [∀ i, NonUnitalRing <| f i] : NonUnitalRing (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocRing, Pi.nonUnitalSemiring with }
/-
**Pi.nonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonAssocRing [forall i, NonAssocRing <| f i] : NonAssocRing (forall i : I,
 f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocRing [∀ i, NonAssocRing <| f i] : NonAssocRing (∀ i : I, f i) :=
  { Pi.nonUnitalNonAssocRing, Pi.nonAssocSemiring, Pi.addGroupWithOne with }
/-
**Pi.ring** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：ring [forall i, Ring <| f i] : Ring (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ring [∀ i, Ring <| f i] : Ring (∀ i : I, f i) :=
  { Pi.semiring, Pi.addCommGroup, Pi.addGroupWithOne with }
/-
**Pi.nonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nonUnitalCommRing [forall i, NonUnitalCommRing <| f i] : NonUnitalCommRing
 (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalCommRing [∀ i, NonUnitalCommRing <| f i] : NonUnitalCommRing (∀ i : I, f i) :=
  { Pi.nonUnitalRing, Pi.commSemigroup with }
/-
**Pi.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：commRing [forall i, CommRing <| f i] : CommRing (forall i : I, f i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing [∀ i, CommRing <| f i] : CommRing (∀ i : I, f i) :=
  { Pi.ring, Pi.commSemiring with }

end Pi

section NonUnitalRingHom

universe u v

variable {I : Type u}

/-- A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unital ring
homomorphism `NonUnitalRingHom.pi f : γ →+* Π a, β a` given by
`NonUnitalRingHom.pi f x b = f b x`. -/
@[simps]
/-
**NonUnitalRingHom.pi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRingHom.pi {f : I -> Type*} {γ : Type*} [forall i, NonUnitalNonAs
socSemiring (f i)] [NonUnitalNonAssocSemiring γ] (g : forall i, γ ->ₙ+* f i) : γ
 ->ₙ+* forall i, f i
参数：f i；g : forall i, γ ->ₙ+* f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unita
l ring
homomorphism `NonUnitalRingHom.pi f : γ →+* Π a, β a` given by
`NonUnitalRingHom.pi f x b = f b x`.
-/
def NonUnitalRingHom.pi {f : I → Type*} {γ : Type*} [∀ i, NonUnitalNonAssocSemiring (f i)]
    [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i) : γ →ₙ+* ∀ i, f i :=
  { MulHom.pi fun i => (g i).toMulHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom := NonUnitalRingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_apply :=
  NonUnitalRingHom.pi_apply
/-
**NonUnitalRingHom.pi_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NonUnitalRingHom.pi_injective {f : I -> Type*} {γ : Type*} [Nonempty I] [f
orall i, NonUnitalNonAssocSemiring (f i)] [NonUnitalNonAssocSemiring γ] (g : for
all i, γ ->ₙ+* f i) (hg : forall i, Function.Injective (g i)) : Function.Injecti
ve (NonUnitalRingHom.pi g)
参数：f i；g : forall i, γ ->ₙ+* f i；hg : forall i, Function.Injective (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.pi_injective`：MulHom.pi_injective {γ : Type w} [Nonempty I] [Mul 
γ] (g : forall i, γ ->ₙ* f i) (hg : forall i, Function.Injective (g i)) : Functi
on.Inject…
-/
theorem NonUnitalRingHom.pi_injective {f : I → Type*} {γ : Type*} [Nonempty I]
    [∀ i, NonUnitalNonAssocSemiring (f i)] [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (NonUnitalRingHom.pi g) :=
  MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_injective :=
  NonUnitalRingHom.pi_injective

/-- Evaluation of functions into an indexed collection of non-unital rings at a point is a
non-unital ring homomorphism. This is `Function.eval` as a `NonUnitalRingHom`. -/
@[simps!]
/-
**Pi.evalNonUnitalRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.evalNonUnitalRingHom (f : I -> Type v) [forall i, NonUnitalNonAssocSemi
ring (f i)] (i : I) : (forall i, f i) ->ₙ+* f i
参数：f : I -> Type v；f i；i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of functions into an indexed collection of non-unital rings at a poin
t is a
non-unital ring homomorphism. This is `Function.eval` as a `NonUnitalRingHom`.
-/
def Pi.evalNonUnitalRingHom (f : I → Type v) [∀ i, NonUnitalNonAssocSemiring (f i)] (i : I) :
    (∀ i, f i) →ₙ+* f i :=
  { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }

/-- `Function.const` as a `NonUnitalRingHom`. -/
@[simps]
/-
**Pi.constNonUnitalRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.constNonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring β] : β -
>ₙ+* α -> β
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` as a `NonUnitalRingHom`.
-/
def Pi.constNonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring β] : β →ₙ+* α → β :=
  { NonUnitalRingHom.pi fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }

/-- Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, induced by a
non-unital ring homomorphism `f` between `α` and `β`. -/
@[simps]
/-
**NonUnitalRingHom.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : NonUnitalNonAssocSemiring 
α] →       [inst_1 : NonUnitalNonAssocSemiring β] → (α →ₙ+* β) → (I : Type u_3) 
→ (I → α) →ₙ+* I → β
参数：α →ₙ+* β；I : Type u_3；I → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, in
duced by a
non-unital ring homomorphism `f` between `α` and `β`.
-/
protected def NonUnitalRingHom.compLeft {α β : Type*} [NonUnitalNonAssocSemiring α]
    [NonUnitalNonAssocSemiring β] (f : α →ₙ+* β) (I : Type*) : (I → α) →ₙ+* I → β :=
  { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end NonUnitalRingHom

section RingHom

universe u v

variable {I : Type u}

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`RingHom.pi f : γ →+* Π a, β a` given by `RingHom.pi f x b = f b x`. -/
@[simps]
/-
**RingHom.pi** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{I : Type u} →   {f : I → Type u_1} →     {γ : Type u_2} →       [inst : (
i : I) → NonAssocSemiring (f i)] →         [inst_1 : NonAssocSemiring γ] → ((i :
 I) → γ →+* f i) → γ →+* (i : I) → f i
参数：i : I；f i；(i : I) → γ →+* f i；i : I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`RingHom.pi f : γ →+* Π a, β a` given by `RingHom.pi f x b = f b x`.
-/
protected def RingHom.pi {f : I → Type*} {γ : Type*} [∀ i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : ∀ i, γ →+* f i) : γ →+* ∀ i, f i :=
  { MonoidHom.pi fun i => (g i).toMonoidHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom := RingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_apply := RingHom.pi_apply
/-
**RingHom.pi_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.pi_injective {f : I -> Type*} {γ : Type*} [Nonempty I] [forall i, 
NonAssocSemiring (f i)] [NonAssocSemiring γ] (g : forall i, γ ->+* f i) (hg : fo
rall i, Function.Injective (g i)) : Function.Injective (RingHom.pi g)
参数：f i；g : forall i, γ ->+* f i；hg : forall i, Function.Injective (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.pi_injective`：MonoidHom.pi_injective {γ : Type w} [Nonempty I]
 [MulOneClass γ] (g : forall i, γ ->* f i) (hg : forall i, Function.Injective (g
 i)) : Funct…
-/
theorem RingHom.pi_injective {f : I → Type*} {γ : Type*} [Nonempty I] [∀ i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : ∀ i, γ →+* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (RingHom.pi g) :=
  MonoidHom.pi_injective (fun i => (g i).toMonoidHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_injective := RingHom.pi_injective

/-- Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `Function.eval` as a `RingHom`. -/
@[simps!]
/-
**Pi.evalRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.evalRingHom (f : I -> Type v) [forall i, NonAssocSemiring (f i)] (i : I
) : (forall i, f i) ->+* f i
参数：f : I -> Type v；f i；i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `Function.eval` as a `RingHom`.
-/
def Pi.evalRingHom (f : I → Type v) [∀ i, NonAssocSemiring (f i)] (i : I) : (∀ i, f i) →+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : I → Type*) [∀ i, Semiring (f i)] (i) :
    RingHomSurjective (Pi.evalRingHom f i) where
  is_surjective x := ⟨by classical exact (if h : · = i then h ▸ x else 0), by simp⟩

/-- `Function.const` as a `RingHom`. -/
@[simps]
/-
**Pi.constRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.constRingHom (α β : Type*) [NonAssocSemiring β] : β ->+* α -> β
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` as a `RingHom`.
-/
def Pi.constRingHom (α β : Type*) [NonAssocSemiring β] : β →+* α → β :=
  { RingHom.pi fun _ => RingHom.id β with toFun := Function.const _ }

/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps]
/-
**RingHom.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : NonAssocSemiring α] → [ins
t_1 : NonAssocSemiring β] → (α →+* β) → (I : Type u_3) → (I → α) →+* I → β
参数：α →+* β；I : Type u_3；I → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a 
ring
homomorphism `f` between `α` and `β`.
-/
protected def RingHom.compLeft {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (I : Type*) : (I → α) →+* I → β :=
  { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end RingHom

