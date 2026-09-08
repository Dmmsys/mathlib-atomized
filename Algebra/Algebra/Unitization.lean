/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `Unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `Unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `Unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `Unitization R A` given by `fun a ↦ (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `Unitization R A` to `B`.

## Main definitions

* `Unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `Unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `Unitization.coeNonUnitalAlgHom`: coercion as a non-unital algebra homomorphism.
* `NonUnitalAlgHom.toAlgHom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `Unitization R A →ₐ[R] B`.
* `Unitization.lift`: the universal property of the unitization, the extension
  `NonUnitalAlgHom.toAlgHom` actually implements an equivalence
  `(A →ₙₐ[R] B) ≃ (Unitization R A ≃ₐ[R] B)`

## Main results

* `AlgHom.ext'`: an extensionality lemma for algebra homomorphisms whose domain is
  `Unitization R A`; it suffices that they agree on `A`.

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/

@[expose] public section


/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a structure wrapper for
`R × A`. -/
@[ext]
/-
**Unitization** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_2 → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal unitization of a non-unital `R`-algebra `A`. This is just a structur
e wrapper for
`R × A`.
-/
structure Unitization (R A : Type*) extends R × A

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `mk x` being printed as `{ toProd := x }` by `delabStructureInstance`. -/
@[app_delab Unitization.mk]
meta def Unitization.delabMk : Delab := delabApp

end Notation

namespace Unitization

section Basic

variable {R A : Type*}

/-
**Unitization.mk_toProd** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：mk_toProd (x : Unitization R A) : mk x.toProd = x
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_toProd (x : Unitization R A) : mk x.toProd = x := rfl
/-
**Unitization.toProd_mk** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toProd_mk (x : R × A) : toProd (mk x) = x
参数：x : R × A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toProd_mk (x : R × A) : toProd (mk x) = x := rfl

/-- The canonical equivalence between `Unitization R A` and `R × A`. -/
@[simps apply symm_apply]
/-
**Unitization.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：equiv : Unitization R A ≃ R × A where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Unitization.mk_toProd`：mk_toProd (x : Unitization R A) : mk x.toProd = x
· 使用引理 `Unitization.toProd_mk`：toProd_mk (x : R × A) : toProd (mk x) = x

--- 原说明 ---
The canonical equivalence between `Unitization R A` and `R × A`.
-/
def equiv : Unitization R A ≃ R × A where
  toFun := toProd
  invFun := mk
  left_inv := mk_toProd
  right_inv := toProd_mk
/-
**Unitization.toProd_injective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toProd_injective : (toProd : Unitization R A -> R × A).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma toProd_injective : (toProd : Unitization R A → R × A).Injective :=
  equiv.injective
/-
**Unitization.toProd_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toProd_surjective : (toProd : Unitization R A -> R × A).Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
lemma toProd_surjective : (toProd : Unitization R A → R × A).Surjective :=
  equiv.surjective
/-
**Unitization.toProd_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toProd_bijective : (toProd : Unitization R A -> R × A).Bijective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma toProd_bijective : (toProd : Unitization R A → R × A).Bijective :=
  equiv.bijective
/-
**Unitization.mk_injective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：mk_injective : (mk : R × A -> Unitization R A).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mk_injective : (mk : R × A → Unitization R A).Injective :=
  equiv.symm.injective
/-
**Unitization.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：mk_surjective : (mk : R × A -> Unitization R A).Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mk_surjective : (mk : R × A → Unitization R A).Surjective :=
  equiv.symm.surjective
/-
**Unitization.mk_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：mk_bijective : (mk : R × A -> Unitization R A).Bijective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mk_bijective : (mk : R × A → Unitization R A).Bijective :=
  equiv.symm.bijective

@[simp]
/-
**Unitization.toProd_inj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toProd_inj_iff {x y : Unitization R A} : toProd x = toProd y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Unitization.toProd_injective`：toProd_injective : (toProd : Unitization R
 A -> R × A).Injective
-/
lemma toProd_inj_iff {x y : Unitization R A} : toProd x = toProd y ↔ x = y :=
  toProd_injective.eq_iff

/-- The canonical inclusion `R → Unitization R A`. -/
/-
**Unitization.inl** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inl [Zero A] (r : R) : Unitization R A
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `R → Unitization R A`.
-/
def inl [Zero A] (r : R) : Unitization R A :=
  mk (r, 0)

/-- The canonical inclusion `A → Unitization R A`. -/
@[coe]
/-
**Unitization.inr** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inr [Zero R] (a : A) : Unitization R A
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `A → Unitization R A`.
-/
def inr [Zero R] (a : A) : Unitization R A :=
  mk (0, a)
/-
**Unitization.** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] : Coe A (Unitization R A) where
  coe := inr

section

variable (A)

@[simp]
/-
**Unitization.fst_inl** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r :=
  rfl

@[simp]
/-
**Unitization.snd_inl** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0 :=
  rfl

end

section

variable (R)

@[simp]
/-
**Unitization.fst_inr** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl

@[simp]
/-
**Unitization.snd_inr** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl

end

/-
**Unitization.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_injective [Zero A] : Function.Injective (inl : R -> Unitization R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Unitization.fst_inl`：fst_inl [Zero A] (r : R) : (inl r : Unitization R A
).fst = r
-/
theorem inl_injective [Zero A] : Function.Injective (inl : R → Unitization R A) :=
  Function.LeftInverse.injective (g := Prod.fst ∘ toProd) <| fst_inl _
/-
**Unitization.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_injective [Zero R] : Function.Injective ((↑) : A -> Unitization R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Unitization.snd_inr`：snd_inr [Zero R] (a : A) : (a : Unitization R A).sn
d = a
-/
theorem inr_injective [Zero R] : Function.Injective ((↑) : A → Unitization R A) :=
  Function.LeftInverse.injective (g := Prod.snd ∘ toProd) <| snd_inr _
/-
**Unitization.inr_inj** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : Zero R] {x y : A}, ↑x = ↑y ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Unitization.inr_injective`：inr_injective [Zero R] : Function.Injective (
(↑) : A -> Unitization R A)
-/
@[simp, norm_cast] theorem inr_inj [Zero R] {x y : A} :
    (inr x : Unitization R A) = inr y ↔ x = y := inr_injective.eq_iff
/-
**Unitization.inl_inj** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : Zero A] {x y : R}, Unitization.inl
 x = Unitization.inl y ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Unitization.inl_injective`：inl_injective [Zero A] : Function.Injective (
inl : R -> Unitization R A)
-/
@[simp] theorem inl_inj [Zero A] {x y : R} :
    (inl x : Unitization R A) = inl y ↔ x = y :=
  inl_injective.eq_iff
/-
**Unitization.instNontrivialLeft** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNontrivialLeft {𝕜 A} [Nontrivial 𝕜] [Nonempty A] : Nontrivial (Unitiza
tion 𝕜 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
-/
instance instNontrivialLeft {𝕜 A} [Nontrivial 𝕜] [Nonempty A] :
    Nontrivial (Unitization 𝕜 A) :=
  equiv.nontrivial
/-
**Unitization.instNontrivialRight** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNontrivialRight {𝕜 A} [Nonempty 𝕜] [Nontrivial A] : Nontrivial (Unitiz
ation 𝕜 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
-/
instance instNontrivialRight {𝕜 A} [Nonempty 𝕜] [Nontrivial A] :
    Nontrivial (Unitization 𝕜 A) :=
  equiv.nontrivial

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

/-
**Unitization.instCanLift** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instCanLift [Zero R] : CanLift (Unitization R A) A inr (fun x => x.fst = 0
) where prf x hx
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Unitization.fst_inr`：fst_inr [Zero R] (a : A) : (a : Unitization R A).fs
t = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instCanLift [Zero R] : CanLift (Unitization R A) A inr (fun x ↦ x.fst = 0) where
  prf x hx := ⟨x.snd, Unitization.ext (hx ▸ fst_inr R x.snd) rfl⟩
/-
**Unitization.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instInhabited [Inhabited R] [Inhabited A] : Inhabited (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  equiv.inhabited
/-
**Unitization.instZero** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instZero [Zero R] [Zero A] : Zero (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Zero R] [Zero A] : Zero (Unitization R A) :=
  equiv.zero
/-
**Unitization.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAdd [Add R] [Add A] : Add (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [Add R] [Add A] : Add (Unitization R A) :=
  equiv.add
/-
**Unitization.instSub** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instSub [Sub R] [Sub A] : Sub (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub [Sub R] [Sub A] : Sub (Unitization R A) :=
  equiv.sub
/-
**Unitization.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNeg [Neg R] [Neg A] : Neg (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg [Neg R] [Neg A] : Neg (Unitization R A) :=
  equiv.Neg
/-
**Unitization.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instSMul [SMul S R] [SMul S A] : SMul S (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [SMul S R] [SMul S A] : SMul S (Unitization R A) :=
  equiv.smul S
/-
**Unitization.instAddSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddSemigroup [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitiza
tion R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddSemigroup [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitization R A) :=
  fast_instance% equiv.addSemigroup
/-
**Unitization.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddZeroClass [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitiza
tion R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddZeroClass [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitization R A) :=
  fast_instance% equiv.addZeroClass
/-
**Unitization.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddMonoid [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A) :=
  fast_instance% equiv.addMonoid
/-
**Unitization.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddGroup [AddGroup R] [AddGroup A] : AddGroup (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroup [AddGroup R] [AddGroup A] : AddGroup (Unitization R A) :=
  fast_instance% equiv.addGroup
/-
**Unitization.instAddCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddCommSemigroup [AddCommSemigroup R] [AddCommSemigroup A] : AddCommSe
migroup (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommSemigroup [AddCommSemigroup R] [AddCommSemigroup A] :
    AddCommSemigroup (Unitization R A) :=
  fast_instance% equiv.addCommSemigroup
/-
**Unitization.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddCommMonoid [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Uni
tization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Unitization R A) :=
  fast_instance% equiv.addCommMonoid
/-
**Unitization.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAddCommGroup [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitiza
tion R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitization R A) :=
  fast_instance% equiv.addCommGroup

@[simp]
/-
**Unitization.toProd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：toProd_zero [Zero R] [Zero A] : (0 : Unitization R A).toProd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_zero [Zero R] [Zero A] : (0 : Unitization R A).toProd = 0 :=
  rfl

@[simp]
/-
**Unitization.toProd_add** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：toProd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).toProd = 
x₁.toProd + x₂.toProd
参数：x₁ x₂ : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) :
    (x₁ + x₂).toProd = x₁.toProd + x₂.toProd :=
  rfl

@[simp]
/-
**Unitization.toProd_neg** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：toProd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).toProd = -x.toProd
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).toProd = -x.toProd :=
  rfl

@[simp]
/-
**Unitization.toProd_smul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：toProd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).
toProd = s • x.toProd
参数：s : S；x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) :
    (s • x).toProd = s • x.toProd :=
  rfl
/-
**Unitization.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instIsScalarTower [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S] [
IsScalarTower T S R] [IsScalarTower T S A] : IsScalarTower T S (Unitization R A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isScalarTower`：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β :
 Type u_5} [inst : SMul M N] [inst_1 : SMul M β] [inst_2 : SMul N β]   (e : α ≃ 
β) [IsSca…
-/
instance instIsScalarTower [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  equiv.isScalarTower T S
/-
**Unitization.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instSMulCommClass [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommCla
ss T S R] [SMulCommClass T S A] : SMulCommClass T S (Unitization R A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.smulCommClass`：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β :
 Type u_5} [inst : SMul M β] [inst_1 : SMul N β] (e : α ≃ β)   [SMulCommClass M 
N β], SMu…
-/
instance instSMulCommClass [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R]
    [SMulCommClass T S A] : SMulCommClass T S (Unitization R A) :=
  equiv.smulCommClass T S
/-
**Unitization.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instIsCentralScalar [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsC
entralScalar S R] [IsCentralScalar S A] : IsCentralScalar S (Unitization R A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isCentralScalar`：∀ (M : Type u_1) {α : Type u_4} {β : Type u_5} [i
nst : SMul M β] [inst_1 : SMul Mᵐᵒᵖ β] (e : α ≃ β)   [IsCentralScalar M β], IsCe
ntralScalar…
-/
instance instIsCentralScalar [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
    [IsCentralScalar S A] : IsCentralScalar S (Unitization R A) :=
  equiv.isCentralScalar S
/-
**Unitization.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instMulAction [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Un
itization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  fast_instance% equiv.mulAction S
/-
**Unitization.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instDistribMulAction [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAct
ion S R] [DistribMulAction S A] : DistribMulAction S (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R]
    [DistribMulAction S A] : DistribMulAction S (Unitization R A) :=
  fast_instance% equiv.distribMulAction S
/-
**Unitization.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instModule [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [
Module S A] : Module S (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Module S (Unitization R A) :=
  fast_instance% equiv.module S

variable (R A) in
/-- The identity map between `Unitization R A` and `R × A` as an `AddEquiv`. -/
@[simps! apply symm_apply]
/-
**Unitization.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：addEquiv [Add R] [Add A] : Unitization R A ≃+ R × A where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map between `Unitization R A` and `R × A` as an `AddEquiv`.
-/
def addEquiv [Add R] [Add A] : Unitization R A ≃+ R × A where
  toEquiv := equiv
  map_add' _ _ := rfl

-- not marked `simp` because the LHS would not be in simp normal form.
/-
**Unitization.toEquiv_addEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toEquiv_addEquiv [Add R] [Add A] : (addEquiv R A).toEquiv = equiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_addEquiv [Add R] [Add A] : (addEquiv R A).toEquiv = equiv :=
  rfl

variable (R S A) in
/-- The identity map between `Unitization R A` and `R × A` as a `LinearEquiv`. -/
@[simps! apply symm_apply]
/-
**Unitization.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] 
[Module S A] : Unitization R A ≃ₗ[S] R × A where toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map between `Unitization R A` and `R × A` as a `LinearEquiv`.
-/
def linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Unitization R A ≃ₗ[S] R × A where
  toAddEquiv := addEquiv R A
  map_smul' _ _ := rfl

@[simp]
/-
**Unitization.toAddEquiv_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：toAddEquiv_linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [M
odule S R] [Module S A] : (linearEquiv S R A).toAddEquiv = addEquiv R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAddEquiv_linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A]
    [Module S R] [Module S A] : (linearEquiv S R A).toAddEquiv = addEquiv R A :=
  rfl

@[simp]
/-
**Unitization.fst_zero** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 :=
  rfl

@[simp]
/-
**Unitization.snd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 :=
  rfl

@[simp]
/-
**Unitization.fst_add** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst
 + x₂.fst
参数：x₁ x₂ : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl

@[simp]
/-
**Unitization.snd_add** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd
 + x₂.snd
参数：x₁ x₂ : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl

@[simp]
/-
**Unitization.fst_neg** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst :=
  rfl

@[simp]
/-
**Unitization.snd_neg** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd :=
  rfl

@[simp]
/-
**Unitization.fst_smul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst
 = s • x.fst
参数：s : S；x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst :=
  rfl

@[simp]
/-
**Unitization.snd_smul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd
 = s • x.snd
参数：s : S；x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd :=
  rfl

section

variable (A)

@[simp]
/-
**Unitization.inl_zero** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0 :=
  rfl

@[simp]
/-
**Unitization.inl_add** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) : (inl (r₁ + r₂) : Unitizatio
n R A) = inl r₁ + inl r₂
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂ :=
  Unitization.ext rfl (add_zero 0).symm

@[simp]
/-
**Unitization.inl_neg** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_neg [Neg R] [AddGroup A] (r : R) : (inl (-r) : Unitization R A) = -inl
 r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem inl_neg [Neg R] [AddGroup A] (r : R) : (inl (-r) : Unitization R A) = -inl r :=
  Unitization.ext rfl neg_zero.symm

@[simp]
/-
**Unitization.inl_sub** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_sub [AddGroup R] [AddGroup A] (r₁ r₂ : R) : (inl (r₁ - r₂) : Unitizati
on R A) = inl r₁ - inl r₂
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem inl_sub [AddGroup R] [AddGroup A] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : Unitization R A) = inl r₁ - inl r₂ :=
  Unitization.ext rfl (sub_zero 0).symm

@[simp]
/-
**Unitization.inl_smul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_smul [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R) : (inl (s
 • r) : Unitization R A) = s • inl r
参数：s : S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem inl_smul [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R) :
    (inl (s • r) : Unitization R A) = s • inl r :=
  Unitization.ext rfl (smul_zero s).symm

end

section

variable (R)

@[simp, norm_cast]
/-
**Unitization.inr_zero** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl

@[simp, norm_cast]
/-
**Unitization.inr_add** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R
 A) = m₁ + m₂
参数：m₁ m₂ : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  Unitization.ext (add_zero 0).symm rfl

@[simp, norm_cast]
/-
**Unitization.inr_neg** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m
参数：m : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  Unitization.ext neg_zero.symm rfl

@[simp, norm_cast]
/-
**Unitization.inr_sub** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_sub [AddGroup R] [AddGroup A] (m₁ m₂ : A) : (↑(m₁ - m₂) : Unitization 
R A) = m₁ - m₂
参数：m₁ m₂ : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem inr_sub [AddGroup R] [AddGroup A] (m₁ m₂ : A) : (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂ :=
  Unitization.ext (sub_zero 0).symm rfl

@[simp, norm_cast]
/-
**Unitization.inr_smul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A) : (↑(r • 
m) : Unitization R A) = r • (m : Unitization R A)
参数：r : S；m : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • (m : Unitization R A) :=
  Unitization.ext (smul_zero _).symm rfl

end

/-
**Unitization.inl_fst_add_inr_snd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization 
R A) : inl x.fst + (x.snd : Unitization R A) = x
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    inl x.fst + (x.snd : Unitization R A) = x :=
  Unitization.ext (add_zero x.fst) (zero_add x.snd)

/-- To show a property hold on all `Unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**Unitization.ind** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A -> Prop} 
(inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitization R A))) (x) : 
P x
参数：inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitization R A))；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.inl_fst_add_inr_snd_eq`：inl_fst_add_inr_snd_eq [AddZeroClass
 R] [AddZeroClass A] (x : Unitization R A) : inl x.fst + (x.snd : Unitization R 
A) = x

--- 原说明 ---
To show a property hold on all `Unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x`.
-/
theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (inl_add_inr : ∀ (r : R) (a : A), P (inl r + (a : Unitization R A))) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

@[ext]
/-
**Unitization.linearMap_ext** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [Ad
dCommMonoid N] [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A ->ₗ
[S] N⦄ (hl : forall r, f (inl r) = g (inl r)) (hr : forall a : A, f a = g a) : f
 = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ a : A, f a = g a) : f = g :=
  (linearEquiv S R A).arrowCongr (.refl ..) |>.injective <|
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

variable [Semiring S] [Semiring R] [AddCommMonoid A] [SMul R A] [Module S R] [Module S A]

variable (S R A) in
/-- The canonical `S`-linear inclusion `A → Unitization R A`. -/
@[simps apply]
/-
**Unitization.inrHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inrHom : A ->ₗ[S] Unitization R A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `S`-linear inclusion `A → Unitization R A`.
-/
def inrHom : A →ₗ[S] Unitization R A where
  toFun := (↑)
  map_add' := inr_add R
  map_smul' := inr_smul R

omit [SMul R A] in
/-
**Unitization.inrHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：inrHom_injective : Function.Injective (inrHom S R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.inr_injective`：inr_injective [Zero R] : Function.Injective (
(↑) : A -> Unitization R A)
-/
lemma inrHom_injective : Function.Injective (inrHom S R A) := Unitization.inr_injective

variable (S R A) in
/-- The canonical `S`-linear projection `Unitization R A → A`. -/
@[simps apply]
/-
**Unitization.sndHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：sndHom : Unitization R A ->ₗ[S] A where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `S`-linear projection `Unitization R A → A`.
-/
def sndHom : Unitization R A →ₗ[S] A where
  toFun a := a.snd
  map_add' := snd_add
  map_smul' := snd_smul

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type*}

/-
**Unitization.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instOne [One R] [Zero A] : One (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne [One R] [Zero A] : One (Unitization R A) :=
  ⟨.mk (1, 0)⟩
/-
**Unitization.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instMul [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A) :=
  ⟨fun x y => .mk (x.fst * y.fst, x.fst • y.snd + y.fst • x.snd + x.snd * y.snd)⟩

@[simp]
/-
**Unitization.fst_one** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 :=
  rfl

@[simp]
/-
**Unitization.snd_one** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 :=
  rfl

@[simp]
/-
**Unitization.fst_mul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) : (x₁
 * x₂).fst = x₁.fst * x₂.fst
参数：x₁ x₂ : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl

@[simp]
/-
**Unitization.snd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) : (x₁
 * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd
参数：x₁ x₂ : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
  rfl

section

variable (A)

@[simp]
/-
**Unitization.inl_one** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1 :=
  rfl

@[simp]
/-
**Unitization.inl_mul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_mul [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ :
 R) : (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_mul [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂ :=
  Unitization.ext rfl <| by simp
/-
**Unitization.inl_mul_inl** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_mul_inl [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ 
r₂ : R) : (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂)
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unitization.inl_mul`：inl_mul [Mul R] [NonUnitalNonAssocSemiring A] [SMul
ZeroClass R A] (r₁ r₂ : R) : (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂
-/
theorem inl_mul_inl [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm

end

section

variable (R)

@[simp, norm_cast]
/-
**Unitization.inr_mul** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a
₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
参数：a₁ a₂ : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
  Unitization.ext (mul_zero _).symm <| by simp

end

@[norm_cast]
/-
**Unitization.inl_mul_inr** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_mul_inr [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass 
R A] (r : R) (a : A) : ((inl r : Unitization R A) * a) = ↑(r • a)
参数：r : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_mul_inr [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : ((inl r : Unitization R A) * a) = ↑(r • a) :=
  Unitization.ext (mul_zero r) <| by simp

@[norm_cast]
/-
**Unitization.inr_mul_inl** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass 
R A] (r : R) (a : A) : a * (inl r : Unitization R A) = ↑(r • a)
参数：r : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : a * (inl r : Unitization R A) = ↑(r • a) :=
  Unitization.ext (zero_mul r) <| by simp
/-
**Unitization.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instMulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction
 R A] : MulOneClass (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] :
    MulOneClass (Unitization R A) :=
  fast_instance%
  { Unitization.instOne, Unitization.instMul with
    one_mul x := Unitization.ext (one_mul x.fst) <| by simp
    mul_one x := Unitization.ext (mul_one x.fst) <| by simp }
/-
**Unitization.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNonAssocSemiring [Semiring R] [NonUnitalNonAssocSemiring A] [Module R 
A] : NonAssocSemiring (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonAssocSemiring (Unitization R A) :=
  fast_instance%
  { Unitization.instMulOneClass,
    Unitization.instAddCommMonoid with
    zero_mul _ := Unitization.ext (zero_mul _) <| by simp
    mul_zero _ := Unitization.ext (mul_zero _) <| by simp
    left_distrib _ _ _ := Unitization.ext (mul_add ..) <| by
      simp [smul_add, add_smul, mul_add]
      abel
    right_distrib _ _ _ := Unitization.ext (add_mul ..) <| by
      simp [smul_add, add_smul, add_mul]
      abel }
/-
**Unitization.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instMonoid [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A] [Is
ScalarTower R A A] [SMulCommClass R A A] : Monoid (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Monoid (Unitization R A) :=
  fast_instance%
  { Unitization.instMulOneClass with
    mul_assoc x y z := Unitization.ext (mul_assoc ..) <| by
      simp only [snd_mul, fst_mul, smul_add, smul_smul, add_mul, smul_mul_assoc, mul_assoc, mul_add,
        mul_smul_comm, mul_comm z.fst x.fst, mul_comm z.fst y.fst]
      abel }
/-
**Unitization.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instCommMonoid [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction 
R A] [IsScalarTower R A A] [SMulCommClass R A A] : CommMonoid (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommMonoid (Unitization R A) :=
  fast_instance%
  { Unitization.instMonoid with
    mul_comm _ _ := Unitization.ext (mul_comm ..) <| by simp [add_comm, mul_comm] }
/-
**Unitization.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalar
Tower R A A] [SMulCommClass R A A] : Semiring (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Semiring (Unitization R A) :=
  fast_instance%
  { Unitization.instMonoid, Unitization.instNonAssocSemiring with }
/-
**Unitization.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A] [
IsScalarTower R A A] [SMulCommClass R A A] : CommSemiring (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommSemiring (Unitization R A) :=
  fast_instance%
  { Unitization.instCommMonoid, Unitization.instNonAssocSemiring with }
/-
**Unitization.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A] : Non
AssocRing (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonAssocRing (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instNonAssocSemiring with }
/-
**Unitization.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instRing [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
 [SMulCommClass R A A] : Ring (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Ring (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instSemiring with }
/-
**Unitization.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instCommRing [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTowe
r R A A] [SMulCommClass R A A] : CommRing (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommRing (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instCommSemiring with }

variable (R A)

/-- The canonical inclusion of rings `R →+* Unitization R A`. -/
@[simps apply]
/-
**Unitization.inlRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inlRingHom [Semiring R] [NonUnitalSemiring A] [Module R A] : R ->+* Unitiz
ation R A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion of rings `R →+* Unitization R A`.
-/
def inlRingHom [Semiring R] [NonUnitalSemiring A] [Module R A] : R →+* Unitization R A where
  toFun := inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type*}

/-
**Unitization.instStar** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instStar [Star R] [Star A] : Star (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStar [Star R] [Star A] : Star (Unitization R A) :=
  ⟨fun ra => .mk (star ra.fst, star ra.snd)⟩

@[simp]
/-
**Unitization.fst_star** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.f
st
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.fst :=
  rfl

@[simp]
/-
**Unitization.snd_star** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.s
nd
参数：x : Unitization R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.snd :=
  rfl

@[simp]
/-
**Unitization.inl_star** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) : inl (star r) =
 star (inl r : Unitization R A)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    inl (star r) = star (inl r : Unitization R A) :=
  Unitization.ext rfl (by simp only [snd_star, star_zero, snd_inl])

@[simp, norm_cast]
/-
**Unitization.inr_star** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) : ↑(star a) = st
ar (a : Unitization R A)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) :=
  Unitization.ext (by simp only [fst_star, star_zero, fst_inr]) rfl
/-
**Unitization.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instStarAddMonoid [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMo
noid A] : StarAddMonoid (Unitization R A) where star_involutive x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A] :
    StarAddMonoid (Unitization R A) where
  star_involutive x := Unitization.ext (star_star x.fst) (star_star x.snd)
  star_add x y := Unitization.ext (star_add x.fst y.fst) (star_add x.snd y.snd)
/-
**Unitization.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instStarModule [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMon
oid A] [Module R A] [StarModule R A] : StarModule R (Unitization R A) where star
_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
-/
instance instStarModule [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
    [Module R A] [StarModule R A] : StarModule R (Unitization R A) where
  star_smul _ _ := Unitization.ext (by simp) (by simp)
/-
**Unitization.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instStarRing [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [
StarRing A] [Module R A] [StarModule R A] : StarRing (Unitization R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
    [Module R A] [StarModule R A] :
    StarRing (Unitization R A) :=
  fast_instance%
  { Unitization.instStarAddMonoid with
    star_mul x y := Unitization.ext
      (by simp [-star_mul']) (by simp [-star_mul', add_comm (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type*) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

/-
**Unitization.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instAlgebra : Algebra S (Unitization R A) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra S (Unitization R A) where
  algebraMap := (Unitization.inlRingHom R A).comp (algebraMap S R)
  commutes' := fun s x => by
    induction x with
    | inl_add_inr =>
      change inl (algebraMap S R s) * _ = _ * inl (algebraMap S R s)
      rw [mul_add, add_mul, inl_mul_inl, inl_mul_inl, inl_mul_inr, inr_mul_inl, mul_comm]
  smul_def' := fun s x => by
    induction x with
    | inl_add_inr =>
      change _ = inl (algebraMap S R s) * _
      rw [mul_add, smul_add, Algebra.algebraMap_eq_smul_one, inl_mul_inl, inl_mul_inr,
        smul_one_mul, inl_smul, inr_smul, smul_one_smul]
/-
**Unitization.algebraMap_eq_inl_comp** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebra
Map S R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R :=
  rfl
/-
**Unitization.algebraMap_eq_inlRingHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Unitizati
on`。
形式化陈述：algebraMap_eq_inlRingHom_comp : algebraMap S (Unitization R A) = (inlRingH
om R A).comp (algebraMap S R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_inlRingHom_comp :
    algebraMap S (Unitization R A) = (inlRingHom R A).comp (algebraMap S R) :=
  rfl
/-
**Unitization.algebraMap_eq_inl** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：algebraMap_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl :=
  rfl
/-
**Unitization.algebraMap_eq_inlRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：algebraMap_eq_inlRingHom : algebraMap R (Unitization R A) = inlRingHom R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_inlRingHom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl

/-- The canonical `R`-algebra projection `Unitization R A → R`. -/
@[simps]
/-
**Unitization.fstHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：fstHom : Unitization R A ->ₐ[R] R where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `R`-algebra projection `Unitization R A → R`.
-/
def fstHom : Unitization R A →ₐ[R] R where
  toFun a := a.fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (A := A)
  map_add' := fst_add
  commutes' := fst_inl A

end Algebra

section coe

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps toFun]
/-
**Unitization.inrNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inrNonUnitalAlgHom (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [M
odule R A] : A ->ₙₐ[R] Unitization R A where toFun
参数：R A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R
 A`
realized as a non-unital algebra homomorphism.
-/
def inrNonUnitalAlgHom (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] :
    A →ₙₐ[R] Unitization R A where
  toFun := (↑)
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R A`
realized as a non-unital star algebra homomorphism. -/
@[simps! apply]
/-
**Unitization.inrNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inrNonUnitalStarAlgHom (R A : Type*) [CommSemiring R] [StarAddMonoid R] [N
onUnitalSemiring A] [Star A] [Module R A] : A ->⋆ₙₐ[R] Unitization R A where toN
onUnitalAlgHom
参数：R A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R
 A`
realized as a non-unital star algebra homomorphism.
-/
def inrNonUnitalStarAlgHom (R A : Type*) [CommSemiring R] [StarAddMonoid R]
    [NonUnitalSemiring A] [Star A] [Module R A] :
    A →⋆ₙₐ[R] Unitization R A where
  toNonUnitalAlgHom := inrNonUnitalAlgHom R A
  map_star' := inr_star

/-- The star algebra equivalence obtained by restricting `Unitization.inrNonUnitalStarAlgHom`
to its range. -/
@[simps!]
/-
**Unitization.inrRangeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：inrRangeEquiv (R A : Type*) [CommSemiring R] [StarAddMonoid R] [NonUnitalS
emiring A] [Star A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : A
 ≃⋆ₐ[R] NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A)
参数：R A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star algebra equivalence obtained by restricting `Unitization.inrNonUnitalSt
arAlgHom`
to its range.
-/
def inrRangeEquiv (R A : Type*) [CommSemiring R] [StarAddMonoid R] [NonUnitalSemiring A]
    [Star A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A) :=
  StarAlgEquiv.ofLeftInverse' (g := fun a ↦ a.snd) (snd_inr R ·)

end coe

section AlgHom

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

/-
**Unitization.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：algHom_ext {F : Type*} [FunLike F (Unitization R A) B] [AlgHomClass F S (U
nitization R A) B] {φ ψ : F} (h : forall a : A, φ a = ψ a) (h' : forall r, φ (al
gebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) : φ = ψ
参数：Unitization R A；Unitization R A；h : forall a : A, φ a = ψ a；h' : forall r, φ 
(algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Unitization.ind`：ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitiz
ation R A -> Prop} (inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitiz
ation…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algHom_ext {F : Type*}
    [FunLike F (Unitization R A) B] [AlgHomClass F S (Unitization R A) B] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a)
    (h' : ∀ r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) :
    φ = ψ := by
  refine DFunLike.ext φ ψ (fun x ↦ ?_)
  induction x
  simp only [map_add, ← algebraMap_eq_inl, h, h']
/-
**Unitization.algHom_ext''** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：algHom_ext'' {F : Type*} [FunLike F (Unitization R A) C] [AlgHomClass F R 
(Unitization R A) C] {φ ψ : F} (h : forall a : A, φ a = ψ a) : φ = ψ
参数：Unitization R A；Unitization R A；h : forall a : A, φ a = ψ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.algHom_ext`：algHom_ext {F : Type*} [FunLike F (Unitization R
 A) B] [AlgHomClass F S (Unitization R A) B] {φ ψ : F} (h : forall a : A, φ a = 
ψ a) (h' : f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algHom_ext'' {F : Type*}
    [FunLike F (Unitization R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a) : φ = ψ :=
  algHom_ext h (fun r => by simp only [AlgHomClass.commutes])

/-- See note [partially-applied ext lemmas] -/
@[ext 1100]
/-
**Unitization.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：algHom_ext' {φ ψ : Unitization R A ->ₐ[R] C} (h : φ.toNonUnitalAlgHom.comp
 (inrNonUnitalAlgHom R A) = ψ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)) :
 φ = ψ
参数：h : φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A) = ψ.toNonUnitalAlgHom.c
omp (inrNonUnitalAlgHom R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Unitization.algHom_ext''`：algHom_ext'' {F : Type*} [FunLike F (Unitizati
on R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F} (h : forall a : A, φ 
a = ψ a) : φ =…
· 使用定理 `NonUnitalAlgHom.congr_fun`：congr_fun {f g : A ->ₛₙₐ[φ] B} (h : f = g) (x
 : A) : f x = g x

--- 原说明 ---
See note [partially-applied ext lemmas]
-/
theorem algHom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)) :
    φ = ψ :=
  algHom_ext'' (NonUnitalAlgHom.congr_fun h)

/-- A non-unital algebra homomorphism from `A` into a unital `R`-algebra `C` lifts to a unital
algebra homomorphism from the unitization into `C`. This is extended to an `Equiv` in
`Unitization.lift` and that should be used instead. This declaration only exists for performance
reasons. -/
@[simps]
/-
**Unitization._root_.NonUnitalAlgHom.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Unitiza
tion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital algebra homomorphism from `A` into a unital `R`-algebra `C` lifts t
o a unital
algebra homomorphism from the unitization into `C`. This is extended to an `Equi
v` in
`Unitization.lift` and that should be used instead. This declaration only exists
 for performance
reasons.
-/
def _root_.NonUnitalAlgHom.toAlgHom (φ : A →ₙₐ[R] C) : Unitization R A →ₐ[R] C where
  toFun := fun x => algebraMap R C x.fst + φ x.snd
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
  map_mul' := fun x y => by
    induction x with
    | inl_add_inr x_r x_a =>
      induction y with
      | inl_add_inr =>
        simp only [fst_mul, fst_add, fst_inl, fst_inr, snd_mul, snd_add, snd_inl, snd_inr, add_zero,
          map_mul, zero_add, map_add, map_smul φ]
        rw [add_mul, mul_add, mul_add]
        rw [← Algebra.commutes _ (φ x_a)]
        simp only [Algebra.algebraMap_eq_smul_one, smul_one_mul, add_assoc]
  map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero]
  map_add' := fun x y => by
    induction x with
    | inl_add_inr =>
      induction y with
      | inl_add_inr =>
        simp only [fst_add, fst_inl, fst_inr, add_zero, map_add, snd_add, snd_inl, snd_inr,
          zero_add, φ.map_add]
        rw [add_add_add_comm]
  commutes' := fun r => by
    simp only [algebraMap_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero]


set_option backward.isDefEq.respectTransparency false in
/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`Unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply]
/-
**Unitization.lift** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：lift : (A ->ₙₐ[R] C) ≃ (Unitization R A ->ₐ[R] C) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uni
quely to
`Unitization R A →ₐ[R] C`. This is the universal property of the unitization.
-/
def lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C) where
  toFun := NonUnitalAlgHom.toAlgHom
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
  right_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
/-
**Unitization.lift_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：lift_symm_apply_apply (φ : Unitization R A ->ₐ[R] C) (a : A) : Unitization
.lift.symm φ a = φ a
参数：φ : Unitization R A ->ₐ[R] C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_symm_apply_apply (φ : Unitization R A →ₐ[R] C) (a : A) :
    Unitization.lift.symm φ a = φ a :=
  rfl

@[simp]
/-
**Unitization._root_.NonUnitalAlgHom.toAlgHom_zero** 是 Mathlib 中的一个引理，位于命名空间 `Un
itization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalAlgHom.toAlgHom_zero :
    ⇑(0 : A →ₙₐ[R] R).toAlgHom = (fun x ↦ x.fst) := by
  ext
  simp

end AlgHom

section StarAlgHom

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [Semiring C] [Algebra R C] [StarRing C]

/-- See note [partially-applied ext lemmas] -/
@[ext]
/-
**Unitization.starAlgHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：starAlgHom_ext {φ ψ : Unitization R A ->⋆ₐ[R] C} (h : (φ : Unitization R A
 ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) = (ψ : Unitization R 
A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) : φ = ψ
参数：h : (φ : Unitization R A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom
 R A) = (ψ : Unitization R A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHo
m R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用引理 `Unitization.algHom_ext''`：algHom_ext'' {F : Type*} [FunLike F (Unitizati
on R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F} (h : forall a : A, φ 
a = ψ a) : φ =…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
See note [partially-applied ext lemmas]
-/
theorem starAlgHom_ext {φ ψ : Unitization R A →⋆ₐ[R] C}
    (h : (φ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) =
      (ψ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) :
    φ = ψ :=
  Unitization.algHom_ext'' <| DFunLike.congr_fun h

variable [StarModule R C]

/-- Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C` lift uniquely
to `Unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply]
/-
**Unitization.starLift** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：starLift : (A ->⋆ₙₐ[R] C) ≃ (Unitization R A ->⋆ₐ[R] C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C
` lift uniquely
to `Unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization
.
-/
def starLift : (A →⋆ₙₐ[R] C) ≃ (Unitization R A →⋆ₐ[R] C) :=
{ toFun := fun φ ↦
  { toAlgHom := Unitization.lift φ.toNonUnitalAlgHom
    map_star' := fun x => by
      simp [map_star] }
  invFun φ := φ.toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A),
  left_inv _ := by ext; simp,
  right_inv _ := by ext; simp }
/-
**Unitization.starLift_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {C : Type u_3} [inst : CommSemiring R] [in
st_1 : StarRing R]   [inst_2 : NonUnitalSemiring A] [inst_3 : StarRing A] [inst_
4 : _root_.Module R A] [inst_5 : SMulCommClass R A A]   [inst_6 : IsScalarTower 
R A A] [inst_7 : Semiring C] [inst_8 : Algebra R C] [inst_9 : StarRing C]   [ins
t_10 : StarModule R C] (φ : Unitization R A →⋆ₐ[R] C) (a : A), (Unitization.star
Lift.symm φ) a = φ ↑a
参数：φ : Unitization R A →⋆ₐ[R] C；a : A；Unitization.starLift.symm φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem starLift_symm_apply_apply (φ : Unitization R A →⋆ₐ[R] C) (a : A) :
    Unitization.starLift.symm φ a = φ a :=
  rfl

end StarAlgHom

section StarMap

variable {R A B C : Type*} [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [StarModule R B] [StarModule R C]

/-- The functorial map on morphisms between the category of non-unital C⋆-algebras with non-unital
star homomorphisms and unital C⋆-algebras with unital star homomorphisms.

This sends `φ : A →⋆ₙₐ[R] B` to a map `Unitization R A →⋆ₐ[R] Unitization R B` given by the formula
`(r, a) ↦ (r, φ a)` (or perhaps more precisely,
`algebraMap R _ r + ↑a ↦ algebraMap R _ r + ↑(φ a)`). -/
@[simps! apply]
/-
**Unitization.starMap** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：starMap (φ : A ->⋆ₙₐ[R] B) : Unitization R A ->⋆ₐ[R] Unitization R B
参数：φ : A ->⋆ₙₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial map on morphisms between the category of non-unital C⋆-algebras w
ith non-unital
star homomorphisms and unital C⋆-algebras with unital star homomorphisms.

This sends `φ : A →⋆ₙₐ[R] B` to a map `Unitization R A →⋆ₐ[R] Unitization R B` g
iven by the formula
`(r, a) ↦ (r, φ a)` (or perhaps more precisely,
`algebraMap R _ r + ↑a ↦ algebraMap R _ r + ↑(φ a)`).
-/
def starMap (φ : A →⋆ₙₐ[R] B) : Unitization R A →⋆ₐ[R] Unitization R B :=
  Unitization.starLift <| (Unitization.inrNonUnitalStarAlgHom R B).comp φ

@[simp high]
/-
**Unitization.starMap_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：starMap_inr (φ : A ->⋆ₙₐ[R] B) (a : A) : starMap φ (inr a) = inr (φ a)
参数：φ : A ->⋆ₙₐ[R] B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.starMap_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3
} [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : NonUnitalSemiring A]
 [inst_3 : Star…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma starMap_inr (φ : A →⋆ₙₐ[R] B) (a : A) :
    starMap φ (inr a) = inr (φ a) := by
  simp

@[simp high]
/-
**Unitization.starMap_inl** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：starMap_inl (φ : A ->⋆ₙₐ[R] B) (r : R) : starMap φ (inl r) = algebraMap R 
(Unitization R B) r
参数：φ : A ->⋆ₙₐ[R] B；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.starMap_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3
} [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : NonUnitalSemiring A]
 [inst_3 : Star…
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
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma starMap_inl (φ : A →⋆ₙₐ[R] B) (r : R) :
    starMap φ (inl r) = algebraMap R (Unitization R B) r := by
  simp

/-- If `φ : A →⋆ₙₐ[R] B` is injective, the lift `starMap φ : Unitization R A →⋆ₐ[R] Unitization R B`
is also injective. -/
/-
**Unitization.starMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：starMap_injective {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Injective φ) : Functio
n.Injective (starMap φ)
参数：hφ : Function.Injective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.starMap_apply`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3
} [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : NonUnitalSemiring A]
 [inst_3 : Star…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
If `φ : A →⋆ₙₐ[R] B` is injective, the lift `starMap φ : Unitization R A →⋆ₐ[R] 
Unitization R B`
is also injective.
-/
lemma starMap_injective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (starMap φ) := by
  intro x y h
  ext
  · simpa using! congr($(h).fst)
  · exact hφ <| by simpa [algebraMap_eq_inl] using! congr($(h).snd)

/-- If `φ : A →⋆ₙₐ[R] B` is surjective, the lift
`starMap φ : Unitization R A →⋆ₐ[R] Unitization R B` is also surjective. -/
/-
**Unitization.starMap_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：starMap_surjective {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Surjective φ) : Funct
ion.Surjective (starMap φ)
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.ind`：ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitiz
ation R A -> Prop} (inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitiz
ation…

--- 原说明 ---
If `φ : A →⋆ₙₐ[R] B` is surjective, the lift
`starMap φ : Unitization R A →⋆ₐ[R] Unitization R B` is also surjective.
-/
lemma starMap_surjective {φ : A →⋆ₙₐ[R] B} (hφ : Function.Surjective φ) :
    Function.Surjective (starMap φ) := by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨mk (r, a), by rfl⟩

/-- `starMap` is functorial: `starMap (ψ.comp φ) = (starMap ψ).comp (starMap φ)`. -/
/-
**Unitization.starMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：starMap_comp {φ : A ->⋆ₙₐ[R] B} {ψ : B ->⋆ₙₐ[R] C} : starMap (ψ.comp φ) = 
(starMap ψ).comp (starMap φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.starAlgHom_ext`：starAlgHom_ext {φ ψ : Unitization R A ->⋆ₐ[R
] C} (h : (φ : Unitization R A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlg
Hom R A) = (ψ : …
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.inrNonUnitalStarAlgHom_apply`：∀ (R : Type u_1) (A : Type u_2
) [inst : CommSemiring R] [inst_1 : StarAddMonoid R] [inst_2 : NonUnitalSemiring
 A]   [inst_3 : Star A] [inst_…
· 使用引理 `Unitization.starMap_inr`：starMap_inr (φ : A ->⋆ₙₐ[R] B) (a : A) : starMa
p φ (inr a) = inr (φ a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`starMap` is functorial: `starMap (ψ.comp φ) = (starMap ψ).comp (starMap φ)`.
-/
lemma starMap_comp {φ : A →⋆ₙₐ[R] B} {ψ : B →⋆ₙₐ[R] C} :
    starMap (ψ.comp φ) = (starMap ψ).comp (starMap φ) := by
  ext; all_goals simp

/-- `starMap` is functorial:
`starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B)`. -/
@[simp]
/-
**Unitization.starMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：starMap_id : starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Uniti
zation R B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.starAlgHom_ext`：starAlgHom_ext {φ ψ : Unitization R A ->⋆ₐ[R
] C} (h : (φ : Unitization R A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlg
Hom R A) = (ψ : …
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `Unitization.ext`：∀ {R : Type u_1} {A : Type u_2} {x y : Unitization R A}
, x.toProd.1 = y.toProd.1 → x.toProd.2 = y.toProd.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.inrNonUnitalStarAlgHom_apply`：∀ (R : Type u_1) (A : Type u_2
) [inst : CommSemiring R] [inst_1 : StarAddMonoid R] [inst_2 : NonUnitalSemiring
 A]   [inst_3 : Star A] [inst_…
· 使用引理 `Unitization.starMap_inr`：starMap_inr (φ : A ->⋆ₙₐ[R] B) (a : A) : starMa
p φ (inr a) = inr (φ a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`starMap` is functorial:
`starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B)`.
-/
lemma starMap_id : starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B) := by
  ext; all_goals simp

end StarMap

section StarNormal

variable {R A : Type*} [Semiring R]
variable [StarAddMonoid R] [Star A] {a : A}


@[simp]
/-
**Unitization.isSelfAdjoint_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：isSelfAdjoint_inr : IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Unitization.inr_injective`：inr_injective [Zero R] : Function.Injective (
(↑) : A -> Unitization R A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSelfAdjoint_inr : IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a := by
  simp only [isSelfAdjoint_iff, ← inr_star, inr_injective.eq_iff]

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr

variable (R) in
/-
**Unitization._root_.IsSelfAdjoint.inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsSelfAdjoint.inr (ha : IsSelfAdjoint a) : IsSelfAdjoint (a : Unitization R A) :=
  isSelfAdjoint_inr.mpr ha

variable [AddCommMonoid A] [Mul A] [SMulWithZero R A]

@[simp]
/-
**Unitization.isStarNormal_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：isStarNormal_inr : IsStarNormal (a : Unitization R A) ↔ IsStarNormal a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Unitization.inr_injective`：inr_injective [Zero R] : Function.Injective (
(↑) : A -> Unitization R A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isStarNormal_inr : IsStarNormal (a : Unitization R A) ↔ IsStarNormal a := by
  simp only [isStarNormal_iff, commute_iff_eq, ← inr_star, ← inr_mul, inr_injective.eq_iff]

alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

variable (R a) in
/-
**Unitization.instIsStarNormal** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instIsStarNormal (a : A) [IsStarNormal a] : IsStarNormal (a : Unitization 
R A)
参数：a : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Unitization.isStarNormal_inr`：isStarNormal_inr : IsStarNormal (a : Uniti
zation R A) ↔ IsStarNormal a
-/
instance instIsStarNormal (a : A) [IsStarNormal a] :
    IsStarNormal (a : Unitization R A) :=
  isStarNormal_inr.mpr ‹_›

end StarNormal

@[simp]
/-
**Unitization.isIdempotentElem_inr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R] [AddZero
Class A] [Mul A] [SMulWithZero R A] {a : A} : IsIdempotentElem (a : Unitization 
R A) ↔ IsIdempotentElem a
参数：R : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Unitization.inr_injective`：inr_injective [Zero R] : Function.Injective (
(↑) : A -> Unitization R A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R]
    [AddZeroClass A] [Mul A] [SMulWithZero R A] {a : A} :
    IsIdempotentElem (a : Unitization R A) ↔ IsIdempotentElem a := by
  simp only [IsIdempotentElem, ← inr_mul, inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

@[grind =]
/-
**Unitization.isStarProjection_inr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：isStarProjection_inr_iff {R A : Type*} [Semiring R] [StarRing R] [NonUnita
lSemiring A] [StarRing A] [Module R A] {p : A} : IsStarProjection (p : Unitizati
on R A) ↔ IsStarProjection p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isStarProjection_inr_iff {R A : Type*} [Semiring R] [StarRing R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] {p : A} :
    IsStarProjection (p : Unitization R A) ↔ IsStarProjection p := by
  simp [isStarProjection_iff]

protected alias ⟨_root_.IsStarProjection.of_inr, _root_.IsStarProjection.inr⟩ :=
  isStarProjection_inr_iff

end Unitization

