/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0` that commutes with every other
element. They are a special case of `TrivSqZeroExt R M` with `M = R`.

## Notation

In the `DualNumber` locale:

* `R[ε]` is a shorthand for `DualNumber R`
* `ε` is a shorthand for `DualNumber.eps`

## Main definitions

* `DualNumber`
* `DualNumber.eps`
* `DualNumber.lift`

## Implementation notes

Rather than duplicating the API of `TrivSqZeroExt`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/

@[expose] public section


variable {R A B : Type*}

/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.
`R[ε]` is notation for `DualNumber R`. -/
/-
**DualNumber** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DualNumber (R : Type*) : Type _
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.
`R[ε]` is notation for `DualNumber R`.
-/
abbrev DualNumber (R : Type*) : Type _ :=
  TrivSqZeroExt R R

/-- The unit element $ε$ that squares to zero, with notation `ε`. -/
/-
**DualNumber.eps** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DualNumber.eps [Zero R] [One R] : DualNumber R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit element $ε$ that squares to zero, with notation `ε`.
-/
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1

@[inherit_doc]
scoped[DualNumber] notation "ε" => DualNumber.eps

@[inherit_doc]
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

open DualNumber

namespace DualNumber

open TrivSqZeroExt Algebra

@[simp]
/-
**DualNumber.fst_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：fst_eps [Zero R] [One R] : fst ε = (0 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) :=
  rfl

@[simp]
/-
**DualNumber.snd_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：snd_eps [Zero R] [One R] : snd ε = (1 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  rfl

/-- A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`. -/
@[simp]
/-
**DualNumber.snd_mul** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * 
fst y
参数：x y : R[ε]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`.
-/
theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y :=
  rfl

@[simp]
/-
**DualNumber.eps_mul_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.inr_mul_inr`：inr_mul_inr [Semiring R] [AddCommMonoid M] [M
odule R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) : (inr m₁ * inr m₂ : tsze R M) = 0
-/
theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 :=
  inr_mul_inr _ _ _

@[simp]
/-
**DualNumber.eps_pow_two** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`。
形式化陈述：eps_pow_two [Semiring R] : (ε : R[ε]) ^ 2 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `DualNumber.eps_mul_eps`：eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eps_pow_two [Semiring R] : (ε : R[ε]) ^ 2 = 0 := by
  simp [pow_two]

@[simp]
/-
**DualNumber.inv_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：inv_eps [DivisionRing R] : (ε : R[ε])⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.inv_inr`：inv_inr (m : M) : (inr m)⁻¹ = (0 : tsze R M)
-/
theorem inv_eps [DivisionRing R] : (ε : R[ε])⁻¹ = 0 :=
  TrivSqZeroExt.inv_inr 1

@[simp]
/-
**DualNumber.inr_eq_smul_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε])
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) :=
  ext (mul_zero r).symm (mul_one r).symm

/-- `ε` commutes with every element of the algebra. -/
/-
**DualNumber.commute_eps_left** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x
参数：x : DualNumber R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
`ε` commutes with every element of the algebra.
-/
theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp

/-- `ε` commutes with every element of the algebra. -/
/-
**DualNumber.commute_eps_right** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε
参数：x : DualNumber R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `DualNumber.commute_eps_left`：commute_eps_left [Semiring R] (x : DualNumb
er R) : Commute ε x

--- 原说明 ---
`ε` commutes with every element of the algebra.
-/
theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (commute_eps_left x).symm

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- For two `R`-algebra morphisms out of `A[ε]` to agree, it suffices for them to agree on the
elements of `A` and the `A`-multiples of `ε`. -/
@[ext 1100]
nonrec theorem algHom_ext' ⦃f g : A[ε] →ₐ[R] B⦄
    (hinl : f.comp (inlAlgHom _ _ _) = g.comp (inlAlgHom _ _ _))
    (hinr : f.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R =
        g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R) :
      f = g :=
  algHom_ext' hinl (by
    ext a
    change f (inr a) = g (inr a)
    simpa only [inr_eq_smul_eps] using! DFunLike.congr_fun hinr a)

set_option backward.defeqAttrib.useBackward true in
/-- For two `R`-algebra morphisms out of `R[ε]` to agree, it suffices for them to agree on `ε`. -/
@[ext 1200]
/-
**DualNumber.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：algHom_ext ⦃f g : R[ε] ->ₐ[R] A⦄ (hε : f ε = g ε) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DualNumber.algHom_ext'`：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [
inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : A
lgebra R A] …
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For two `R`-algebra morphisms out of `R[ε]` to agree, it suffices for them to ag
ree on `ε`.
-/
theorem algHom_ext ⦃f g : R[ε] →ₐ[R] A⦄ (hε : f ε = g ε) : f = g := by
  ext
  dsimp
  simp only [one_smul, hε]

/-- A ring morphism `R[ε] →+* R'` is determined by its restriction
on `R` and its value on `ε`. -/
@[ext high]
/-
**DualNumber.ringHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `DualNumber`。
形式化陈述：ringHom_ext {R' : Type*} [CommSemiring R'] {f g : R[ε] ->+* R'} (h₀ : f.co
mp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε])) (hε : f ε = g ε) : f = g
参数：h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε])；hε : f ε = g ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `DualNumber.algHom_ext`：algHom_ext ⦃f g : R[ε] ->ₐ[R] A⦄ (hε : f ε = g ε)
 : f = g

--- 原说明 ---
A ring morphism `R[ε] →+* R'` is determined by its restriction
on `R` and its value on `ε`.
-/
lemma ringHom_ext {R' : Type*} [CommSemiring R'] {f g : R[ε] →+* R'}
    (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  let : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] →ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] →ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg AlgHom.toRingHom (show f' = g' from algHom_ext hε)

/-- A universal property of the dual numbers, providing a unique `A[ε] →ₐ[R] B` for every map
`f : A →ₐ[R] B` and a choice of element `e : B` which squares to `0` and commutes with the range of
`f`.

This isomorphism is named to match the similar `Complex.lift`.
Note that when `f : R →ₐ[R] B := Algebra.ofId R B`, the commutativity assumption is automatic, and
we are free to choose any element `e : B`. -/
/-
**DualNumber.lift** 是 Mathlib 中的一个定义，位于命名空间 `DualNumber`。
形式化陈述：lift : {fe : (A ->ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ forall a, Commute fe.2 
(fe.1 a)} ≃ (A[ε] ->ₐ[R] B)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
A universal property of the dual numbers, providing a unique `A[ε] →ₐ[R] B` for 
every map
`f : A →ₐ[R] B` and a choice of element `e : B` which squares to `0` and commute
s with the range of
`f`.

This isomorphism is named to match the similar `Complex.lift`.
Note that when `f : R →ₐ[R] B := Algebra.ofId R B`, the commutativity assumption
 is automatic, and
we are free to choose any element `e : B`.
-/
def lift :
    {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)} ≃ (A[ε] →ₐ[R] B) := by
  refine Equiv.trans ?_ TrivSqZeroExt.liftEquiv
  exact {
    toFun := fun fe => ⟨
      (fe.val.1, MulOpposite.op fe.val.2 • fe.val.1.toLinearMap),
      fun x y => show (fe.val.1 x * fe.val.2) * (fe.val.1 y * fe.val.2) = 0 by
        rw [(fe.prop.2 _).mul_mul_mul_comm, fe.prop.1, mul_zero],
      fun r x => show fe.val.1 (r * x) * fe.val.2 = fe.val.1 r * (fe.val.1 x * fe.val.2) by
        rw [map_mul, mul_assoc],
      fun r x => show fe.val.1 (x * r) * fe.val.2 = (fe.val.1 x * fe.val.2) * fe.val.1 r by
        rw [map_mul, (fe.prop.2 _).right_comm]⟩
    invFun := fun fg => ⟨
      (fg.val.1, fg.val.2 1),
      fg.prop.1 _ _,
      fun a => show fg.val.2 1 * fg.val.1 a = fg.val.1 a * fg.val.2 1 by
        rw [← fg.prop.2.1, ← fg.prop.2.2, smul_eq_mul, op_smul_eq_mul, mul_one, one_mul]⟩
    left_inv := fun fe => Subtype.ext <| Prod.ext rfl <|
      show fe.val.1 1 * fe.val.2 = fe.val.2 by
        rw [map_one, one_mul]
    right_inv := fun fg => Subtype.ext <| Prod.ext rfl <| LinearMap.ext fun x =>
      show fg.val.1 x * fg.val.2 1 = fg.val.2 x by
        rw [← fg.prop.2.1, smul_eq_mul, mul_one] }
/-
**DualNumber.lift_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：lift_apply_apply (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A[ε]) : lift fe
 a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2
参数：fe : {_fe : (A ->ₐ[R] B) × B // _}；a : A[ε]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem lift_apply_apply (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A[ε]) :
    lift fe a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2 := rfl
/-
**DualNumber.coe_lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] (F : DualNumber A →ₐ[R] B),   ↑(DualNumber.lift.symm F) = (F.comp (Triv
SqZeroExt.inlAlgHom R A A), F DualNumber.eps)
参数：F : DualNumber A →ₐ[R] B；DualNumber.lift.symm F；F.comp (TrivSqZeroExt.inlAlgH
om R A A), F DualNumber.eps。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem coe_lift_symm_apply (F : A[ε] →ₐ[R] B) :
    (lift.symm F).val = (F.comp (inlAlgHom _ _ _), F ε) := rfl

/-- When applied to `inl`, `DualNumber.lift` applies the map `f : A →ₐ[R] B`. -/
/-
**DualNumber.lift_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] (fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }
)   (a : A), (DualNumber.lift fe) (TrivSqZeroExt.inl a) = (↑fe).1 a
参数：fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }；a : A；
DualNumber.lift fe；TrivSqZeroExt.inl a；↑fe。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DualNumber.lift_apply_apply`：lift_apply_apply (fe : {_fe : (A ->ₐ[R] B) 
× B // _}) (a : A[ε]) : lift fe a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
· 使用定理 `TrivSqZeroExt.snd_inl`：snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
When applied to `inl`, `DualNumber.lift` applies the map `f : A →ₐ[R] B`.
-/
@[simp] theorem lift_apply_inl (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A) :
    lift fe (inl a : A[ε]) = fe.val.1 a := by
  rw [lift_apply_apply, fst_inl, snd_inl, map_zero, zero_mul, add_zero]
/-
**DualNumber.lift_comp_inlHom** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B]   (fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a)
 }),   (DualNumber.lift fe).comp (TrivSqZeroExt.inlAlgHom R A A) = (↑fe).1
参数：fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }；DualNu
mber.lift fe；TrivSqZeroExt.inlAlgHom R A A；↑fe。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DualNumber.lift_apply_inl`：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4
} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 
: Algebra R A] …
-/
@[simp] theorem lift_comp_inlHom (fe : {_fe : (A →ₐ[R] B) × B // _}) :
    (lift fe).comp (inlAlgHom R A A) = fe.val.1 :=
  AlgHom.ext <| lift_apply_inl fe

/-- Scaling on the left is sent by `DualNumber.lift` to multiplication on the left -/
/-
**DualNumber.lift_smul** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] (fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }
)   (a : A) (ad : DualNumber A), (DualNumber.lift fe) (a • ad) = (↑fe).1 a * (Du
alNumber.lift fe) ad
参数：fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }；a : A；
ad : DualNumber A；DualNumber.lift fe；a • ad；↑fe；DualNumber.lift fe。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_mul_eq_smul`：inl_mul_eq_smul [Monoid R] [AddMonoid M] 
[DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R) (x : tsze R M) : inl r 
* x = r •> x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `DualNumber.lift_apply_inl`：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4
} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 
: Algebra R A] …

--- 原说明 ---
Scaling on the left is sent by `DualNumber.lift` to multiplication on the left
-/
@[simp] theorem lift_smul (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (a • ad) = fe.val.1 a * lift fe ad := by
  rw [← inl_mul_eq_smul, map_mul, lift_apply_inl]

/-- Scaling on the right is sent by `DualNumber.lift` to multiplication on the right -/
/-
**DualNumber.lift_op_smul** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] (fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }
)   (a : A) (ad : DualNumber A), (DualNumber.lift fe) (MulOpposite.op a • ad) = 
(DualNumber.lift fe) ad * (↑fe).1 a
参数：fe : { _fe // _fe.2 * _fe.2 = 0 ∧ ∀ (a : A), Commute _fe.2 (_fe.1 a) }；a : A；
ad : DualNumber A；DualNumber.lift fe；MulOpposite.op a • ad；DualNumber.lift fe；↑f
e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.mul_inl_eq_op_smul`：mul_inl_eq_op_smul [Monoid R] [AddMono
id M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (x : tsze R M) (r : R) : 
x * inl r = x <• r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `DualNumber.lift_apply_inl`：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4
} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 
: Algebra R A] …

--- 原说明 ---
Scaling on the right is sent by `DualNumber.lift` to multiplication on the right
-/
@[simp] theorem lift_op_smul (fe : {_fe : (A →ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (MulOpposite.op a • ad) = lift fe ad * fe.val.1 a := by
  rw [← mul_inl_eq_op_smul, map_mul, lift_apply_inl]

/-- When applied to `ε`, `DualNumber.lift` produces the element of `B` that squares to 0. -/
/-
**DualNumber.lift_apply_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] (fe : { fe // fe.2 * fe.2 = 0 ∧ ∀ (a : A), Commute fe.2 (fe.1 a) }),   
(DualNumber.lift fe) DualNumber.eps = (↑fe).2
参数：fe : { fe // fe.2 * fe.2 = 0 ∧ ∀ (a : A), Commute fe.2 (fe.1 a) }；DualNumber.
lift fe；↑fe。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When applied to `ε`, `DualNumber.lift` produces the element of `B` that squares 
to 0.
-/
@[simp] theorem lift_apply_eps
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    lift fe (ε : A[ε]) = fe.val.2 := by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, map_one, one_mul, zero_add]

/-- Lifting `DualNumber.eps` itself gives the identity. -/
@[simp]
/-
**DualNumber.lift_inlAlgHom_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：lift_inlAlgHom_eps : lift ⟨(inlAlgHom _ _ _, ε), eps_mul_eps, fun _ => com
mute_eps_left _⟩ = AlgHom.id R A[ε]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
Lifting `DualNumber.eps` itself gives the identity.
-/
theorem lift_inlAlgHom_eps :
    lift ⟨(inlAlgHom _ _ _, ε), eps_mul_eps, fun _ => commute_eps_left _⟩ = AlgHom.id R A[ε] :=
  lift.apply_symm_apply <| AlgHom.id R A[ε]

@[simp]
/-
**DualNumber.range_inlAlgHom_sup_adjoin_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumbe
r`。
形式化陈述：range_inlAlgHom_sup_adjoin_eps : (inlAlgHom R A A).range ⊔ Algebra.adjoin 
R {ε} = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_fst_add_inr_snd_eq`：inl_fst_add_inr_snd_eq [AddZeroCla
ss R] [AddZeroClass M] (x : tsze R M) : inl x.fst + inr x.snd = x
· 使用定理 `DualNumber.inr_eq_smul_eps`：inr_eq_smul_eps [MulZeroOneClass R] (r : R) 
: inr r = (r • ε : R[ε])
· 使用定理 `TrivSqZeroExt.inl_mul_eq_smul`：inl_mul_eq_smul [Monoid R] [AddMonoid M] 
[DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R) (x : tsze R M) : inl r 
* x = r •> x
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
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem range_inlAlgHom_sup_adjoin_eps :
    (inlAlgHom R A A).range ⊔ Algebra.adjoin R {ε} = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq, inr_eq_smul_eps, ← inl_mul_eq_smul]
  refine add_mem ?_ (mul_mem ?_ ?_)
  · exact le_sup_left (α := Subalgebra R _) <| Set.mem_range_self x.fst
  · exact le_sup_left (α := Subalgebra R _) <| Set.mem_range_self x.snd
  · refine le_sup_right (α := Subalgebra R _) <| subset_adjoin <| Set.mem_singleton ε

@[simp]
/-
**DualNumber.range_lift** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：range_lift (fe : {fe : (A ->ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ forall a, Com
mute fe.2 (fe.1 a)}) : (lift fe).range = fe.1.1.range ⊔ R[fe.1.2]
参数：fe : {fe : (A ->ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ forall a, Commute fe.2 (fe.1
 a)}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.map_sup`：map_sup (f : A ->ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ 
T).map f = S.map f ⊔ T.map f
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `DualNumber.lift_apply_eps`：∀ {R : Type u_1} {B : Type u_3} {A : Type u_4
} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 
: Algebra R A] …
· 使用定理 `DualNumber.lift_comp_inlHom`：∀ {R : Type u_1} {B : Type u_3} {A : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_
3 : Algebra R A] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_lift
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (lift fe).range = fe.1.1.range ⊔ R[fe.1.2] := by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]

/-- Show DualNumber with values x and y as an `"x + y*ε"` string -/
/-
**DualNumber.instRepr** 是 Mathlib 中的一个实例，位于命名空间 `DualNumber`。
形式化陈述：instRepr [Repr R] : Repr (DualNumber R) where reprPrec f p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show DualNumber with values x and y as an `"x + y*ε"` string
-/
instance instRepr [Repr R] : Repr (DualNumber R) where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.fst 65 ++ " + " ++ reprPrec f.snd 70 ++ "*ε"

end DualNumber

