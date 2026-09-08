/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Isomorphisms with the even subalgebra of a Clifford algebra

This file provides some notable isomorphisms regarding the even subalgebra, `CliffordAlgebra.even`.

## Main definitions

* `CliffordAlgebra.equivEven`: Every Clifford algebra is isomorphic as an algebra to the even
  subalgebra of a Clifford algebra with one more dimension.
  * `CliffordAlgebra.EquivEven.Q'`: The quadratic form used by this "one-up" algebra.
  * `CliffordAlgebra.toEven`: The simp-normal form of the forward direction of this isomorphism.
  * `CliffordAlgebra.ofEven`: The simp-normal form of the reverse direction of this isomorphism.

* `CliffordAlgebra.evenEquivEvenNeg`: Every even subalgebra is isomorphic to the even subalgebra
  of the Clifford algebra with negated quadratic form.
  * `CliffordAlgebra.evenToNeg`: The simp-normal form of each direction of this isomorphism.

## Main results

* `CliffordAlgebra.coe_toEven_reverse_involute`: the behavior of `CliffordAlgebra.toEven` on the
  "Clifford conjugate", that is `CliffordAlgebra.reverse` composed with
  `CliffordAlgebra.involute`.
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-! ### Constructions needed for `CliffordAlgebra.equivEven` -/


namespace EquivEven

/-- The quadratic form on the augmented vector space `M × R` sending `v + r•e0` to `Q v - r^2`. -/
/-
**CliffordAlgebra.EquivEven.Q'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CliffordAlgebra.Equi
vEven`。
形式化陈述：Q' : QuadraticForm R (M × R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quadratic form on the augmented vector space `M × R` sending `v + r•e0` to `
Q v - r^2`.
-/
abbrev Q' : QuadraticForm R (M × R) :=
  Q.prod <| -QuadraticMap.sq (R := R)
/-
**CliffordAlgebra.EquivEven.Q'_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.
EquivEven`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   (Q : QuadraticForm R M) (m : M × R), (Cliffor
dAlgebra.EquivEven.Q' Q) m = Q m.1 - m.2 * m.2
参数：Q : QuadraticForm R M；m : M × R；CliffordAlgebra.EquivEven.Q' Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem Q'_apply (m : M × R) : Q' Q m = Q m.1 - m.2 * m.2 :=
  (sub_eq_add_neg _ _).symm

/-- The unit vector in the new dimension -/
/-
**CliffordAlgebra.EquivEven.e0** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra.EquivE
ven`。
形式化陈述：e0 : CliffordAlgebra (Q' Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit vector in the new dimension
-/
def e0 : CliffordAlgebra (Q' Q) :=
  ι (Q' Q) (0, 1)

/-- The embedding from the existing vector space -/
/-
**CliffordAlgebra.EquivEven.v** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra.EquivEv
en`。
形式化陈述：v : M ->ₗ[R] CliffordAlgebra (Q' Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from the existing vector space
-/
def v : M →ₗ[R] CliffordAlgebra (Q' Q) :=
  ι (Q' Q) ∘ₗ LinearMap.inl _ _ _
/-
**CliffordAlgebra.EquivEven.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.EquivEve
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (Q' Q) (m, r) = v Q m + r • e0 Q := by
  rw [e0, v, LinearMap.comp_apply, LinearMap.inl_apply, ← map_smul, Prod.smul_mk,
    smul_zero, smul_eq_mul, mul_one, ← map_add, Prod.mk_add_mk, zero_add, add_zero]
/-
**CliffordAlgebra.EquivEven.e0_mul_e0** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
.EquivEven`。
形式化陈述：e0_mul_e0 : e0 Q * e0 Q = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.prod_apply`：∀ {R : Type u_2} {M₁ : Type u_3} {M₂ : Type u_4
} {P : Type u_7} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 :
 AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `QuadraticMap.instIsNegApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 [inst_3 : AddCom…
· 使用定理 `QuadraticMap.sq_apply`：∀ {R : Type u_3} {A : Type u_7} [inst : CommSemir
ing R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] [in
st_3 : SMul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem e0_mul_e0 : e0 Q * e0 Q = -1 :=
  (ι_sq_scalar _ _).trans <| by simp
/-
**CliffordAlgebra.EquivEven.v_sq_scalar** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra.EquivEven`。
形式化陈述：v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.prod_apply`：∀ {R : Type u_2} {M₁ : Type u_3} {M₂ : Type u_4
} {P : Type u_7} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 :
 AddCommMonoi…
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `QuadraticMap.instIsNegApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 [inst_3 : AddCom…
· 使用定理 `QuadraticMap.sq_apply`：∀ {R : Type u_3} {A : Type u_7} [inst : CommSemir
ing R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] [in
st_3 : SMul…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m) :=
  (ι_sq_scalar _ _).trans <| by simp

set_option backward.defeqAttrib.useBackward true in
/-
**CliffordAlgebra.EquivEven.neg_e0_mul_v** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlge
bra.EquivEven`。
形式化陈述：neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_eq_of_add_eq_zero_right`：∀ {G : Type u_1} [inst : SubtractionMonoid 
G] {a b : G}, a + b = 0 → -a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.ι_mul_ι_add_swap`：ι_mul_ι_add_swap (a b : M) : ι Q a * ι
 Q b + ι Q b * ι Q a = algebraMap R _ (QuadraticMap.polar Q a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `QuadraticMap.instIsNegApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 [inst_3 : AddCom…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q := by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  simp [QuadraticMap.polar]
/-
**CliffordAlgebra.EquivEven.neg_v_mul_e0** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlge
bra.EquivEven`。
形式化陈述：neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.EquivEven.neg_e0_mul_v`：neg_e0_mul_v (m : M) : -(e0 Q * 
v Q m) = v Q m * e0 Q
-/
theorem neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m := by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm

@[simp]
/-
**CliffordAlgebra.EquivEven.e0_mul_v_mul_e0** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra.EquivEven`。
形式化陈述：e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.EquivEven.neg_v_mul_e0`：neg_v_mul_e0 (m : M) : -(v Q m *
 e0 Q) = e0 Q * v Q m
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CliffordAlgebra.EquivEven.e0_mul_e0`：e0_mul_e0 : e0 Q * e0 Q = -1
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m := by
  rw [← neg_v_mul_e0, ← neg_mul, mul_assoc, e0_mul_e0, mul_neg_one, neg_neg]

@[simp]
/-
**CliffordAlgebra.EquivEven.reverse_v** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
.EquivEven`。
形式化陈述：reverse_v (m : M) : reverse (Q
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
-/
theorem reverse_v (m : M) : reverse (Q := Q' Q) (v Q m) = v Q m :=
  reverse_ι _

@[simp]
/-
**CliffordAlgebra.EquivEven.involute_v** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a.EquivEven`。
形式化陈述：involute_v (m : M) : involute (v Q m) = -v Q m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
-/
theorem involute_v (m : M) : involute (v Q m) = -v Q m :=
  involute_ι _

@[simp]
/-
**CliffordAlgebra.EquivEven.reverse_e0** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a.EquivEven`。
形式化陈述：reverse_e0 : reverse (Q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
-/
theorem reverse_e0 : reverse (Q := Q' Q) (e0 Q) = e0 Q :=
  reverse_ι _

@[simp]
/-
**CliffordAlgebra.EquivEven.involute_e0** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra.EquivEven`。
形式化陈述：involute_e0 : involute (e0 Q) = -e0 Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
-/
theorem involute_e0 : involute (e0 Q) = -e0 Q :=
  involute_ι _

end EquivEven

open EquivEven

set_option backward.isDefEq.respectTransparency.types false in
/-- The embedding from the smaller algebra into the new larger one. -/
/-
**CliffordAlgebra.toEven** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：toEven : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra.even (Q' Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from the smaller algebra into the new larger one.
-/
def toEven : CliffordAlgebra Q →ₐ[R] CliffordAlgebra.even (Q' Q) := by
  refine CliffordAlgebra.lift Q ⟨?_, fun m => ?_⟩
  · refine LinearMap.codRestrict _ ?_ fun m => Submodule.mem_iSup_of_mem ⟨2, rfl⟩ ?_
    · exact (LinearMap.mulLeft R <| e0 Q).comp (v Q)
    rw [Subtype.coe_mk, pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  · ext1
    simp only [Subalgebra.coe_mul, ← even_toSubmodule]
    rw [LinearMap.codRestrict_apply]
    simp [← mul_assoc, v_sq_scalar]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CliffordAlgebra.toEven_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEven_ι (m : M) : (toEven Q (ι Q m) : CliffordAlgebra (Q' Q)) = e0 Q * v Q m := by
  simp only [toEven, CliffordAlgebra.lift_ι_apply, ← even_toSubmodule]
  rw [LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]

/-- The embedding from the even subalgebra with an extra dimension into the original algebra. -/
/-
**CliffordAlgebra.ofEven** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：ofEven : CliffordAlgebra.even (Q' Q) ->ₐ[R] CliffordAlgebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from the even subalgebra with an extra dimension into the original
 algebra.
-/
def ofEven : CliffordAlgebra.even (Q' Q) →ₐ[R] CliffordAlgebra Q := by
  /-
    Recall that we need:
     * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
     * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
     * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
     * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
    -/
  let f : M × R →ₗ[R] M × R →ₗ[R] CliffordAlgebra Q :=
    ((Algebra.lmul R (CliffordAlgebra Q)).toLinearMap.comp <|
          (ι Q).comp (LinearMap.fst _ _ _) +
            (Algebra.linearMap R _).comp (LinearMap.snd _ _ _)).compl₂
      ((ι Q).comp (LinearMap.fst _ _ _) - (Algebra.linearMap R _).comp (LinearMap.snd _ _ _))
  haveI f_apply : ∀ x y, f x y = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
    fun x y => by rfl
  haveI hc : ∀ (r : R) (x : CliffordAlgebra Q), Commute (algebraMap _ _ r) x := Algebra.commutes
  haveI hm :
    ∀ m : M × R,
      ι Q m.1 * ι Q m.1 - algebraMap R _ m.2 * algebraMap R _ m.2 = algebraMap R _ (Q' Q m) := by
    intro m
    rw [ι_sq_scalar, ← map_mul, ← map_sub, sub_eq_add_neg, Q'_apply, sub_eq_add_neg]
  refine even.lift (Q' Q) ⟨f, ?_, ?_⟩ <;> simp_rw [f_apply]
  · intro m
    rw [← (hc _ _).symm.mul_self_sub_mul_self_eq, hm]
  · intro m₁ m₂ m₃
    rw [← mul_smul_comm, ← mul_assoc, mul_assoc (_ + _), ← (hc _ _).symm.mul_self_sub_mul_self_eq',
      Algebra.smul_def, ← mul_assoc, hm]
/-
**CliffordAlgebra.ofEven_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEven_ι (x y : M × R) :
    ofEven Q ((even.ι (Q' Q)).bilin x y) =
      (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
  even.lift_ι (Q' Q) _ x y
/-
**CliffordAlgebra.toEven_comp_ofEven** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
形式化陈述：toEven_comp_ofEven : (toEven Q).comp (ofEven Q) = AlgHom.id R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.even.algHom_ext`：∀ {R : Type u_1} {M : Type u_2} [inst :
 CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : Quadr
aticForm R M) {A : Ty…
· 使用定理 `CliffordAlgebra.EvenHom.ext`：∀ {R : Type u_1} {M : Type u_2} {inst : Com
mRing R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   {Q : Quadratic
Form R M} {A : Ty…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.ofEven_ι`：ofEven_ι (x y : M × R) : ofEven Q ((even.ι (Q'
 Q)).bilin x y) = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2
)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Subalgebra.coe_mul`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (x y : ↥S), 
↑(x * y)…
· 使用定理 `Subalgebra.coe_add`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (x y : ↥S), 
↑(x + y)…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
· 使用定理 `Subalgebra.coe_sub`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] {S : Subalgebra R A}   (x y : ↥S), ↑(x - y)
 = ↑x - …
· 使用定理 `CliffordAlgebra.toEven_ι`：toEven_ι (m : M) : (toEven Q (ι Q m) : Cliffor
dAlgebra (Q' Q)) = e0 Q * v Q m
· 使用定理 `Subalgebra.coe_algebraMap`：coe_algebraMap [CommSemiring R'] [SMul R' R] 
[Algebra R' A] [IsScalarTower R' R A] (r : R') : ↑(algebraMap R' S r) = algebraM
ap R' A r
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
（共 49 条，此处仅展示前 30 条）
-/
theorem toEven_comp_ofEven : (toEven Q).comp (ofEven Q) = AlgHom.id R _ :=
  even.algHom_ext (Q' Q) <|
    EvenHom.ext <|
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
          Subtype.ext <|
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m₁ + algebraMap R _ r₁) * (e0 Q * v Q m₂ - algebraMap R _ r₂) := by
                rw [ofEven_ι, map_mul, map_add, map_sub, AlgHom.commutes,
                  AlgHom.commutes, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_sub,
                  toEven_ι, toEven_ι, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
              _ =
                  e0 Q * v Q m₁ * (e0 Q * v Q m₂) + r₁ • e0 Q * v Q m₂ - r₂ • e0 Q * v Q m₁ -
                    algebraMap R _ (r₁ * r₂) := by
                rw [mul_sub, add_mul, add_mul, ← Algebra.commutes, ← Algebra.smul_def, ← map_mul, ←
                  Algebra.smul_def, sub_add_eq_sub_sub, smul_mul_assoc, smul_mul_assoc]
              _ =
                  v Q m₁ * v Q m₂ + r₁ • e0 Q * v Q m₂ + v Q m₁ * r₂ • e0 Q +
                    r₁ • e0 Q * r₂ • e0 Q := by
                have h1 : e0 Q * v Q m₁ * (e0 Q * v Q m₂) = v Q m₁ * v Q m₂ := by
                  rw [← mul_assoc, e0_mul_v_mul_e0]
                have h2 : -(r₂ • e0 Q * v Q m₁) = v Q m₁ * r₂ • e0 Q := by
                  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg, neg_e0_mul_v]
                have h3 : -algebraMap R _ (r₁ * r₂) = r₁ • e0 Q * r₂ • e0 Q := by
                  rw [Algebra.algebraMap_eq_smul_one, smul_mul_smul_comm, e0_mul_e0, smul_neg]
                rw [sub_eq_add_neg, sub_eq_add_neg, h1, h2, h3]
              _ = ι (Q' Q) (m₁, r₁) * ι (Q' Q) (m₂, r₂) := by
                rw [ι_eq_v_add_smul_e0, ι_eq_v_add_smul_e0, mul_add, add_mul, add_mul, add_assoc]
/-
**CliffordAlgebra.ofEven_comp_toEven** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
形式化陈述：ofEven_comp_toEven : (ofEven Q).comp (toEven Q) = AlgHom.id R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `CliffordAlgebra.toEven_ι`：toEven_ι (m : M) : (toEven Q (ι Q m) : Cliffor
dAlgebra (Q' Q)) = e0 Q * v Q m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `CliffordAlgebra.ofEven_ι`：ofEven_ι (x y : M × R) : ofEven Q ((even.ι (Q'
 Q)).bilin x y) = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2
)
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem ofEven_comp_toEven : (ofEven Q).comp (toEven Q) = AlgHom.id R _ :=
  CliffordAlgebra.hom_ext <|
    LinearMap.ext fun m =>
      calc
        ofEven Q (toEven Q (ι Q m)) = ofEven Q ⟨_, (toEven Q (ι Q m)).prop⟩ := by
          rw [Subtype.coe_eta]
        _ = (ι Q 0 + algebraMap R _ 1) * (ι Q m - algebraMap R _ 0) := by
          simp_rw [toEven_ι]
          exact ofEven_ι Q _ _
        _ = ι Q m := by rw [map_one, map_zero, map_zero, sub_zero, zero_add, one_mul]

/-- Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating to `-1` on that new
basis vector. -/
/-
**CliffordAlgebra.equivEven** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：equivEven : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.toEven_comp_ofEven`：toEven_comp_ofEven : (toEven Q).comp
 (ofEven Q) = AlgHom.id R _
· 使用定理 `CliffordAlgebra.ofEven_comp_toEven`：ofEven_comp_toEven : (ofEven Q).comp
 (toEven Q) = AlgHom.id R _

--- 原说明 ---
Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra 
with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating
 to `-1` on that new
basis vector.
-/
def equivEven : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q) :=
  AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (toEven_comp_ofEven Q) (ofEven_comp_toEven Q)

/-- The representation of the clifford conjugate (i.e. the reverse of the involute) in the even
subalgebra is just the reverse of the representation. -/
/-
**CliffordAlgebra.coe_toEven_reverse_involute** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：coe_toEven_reverse_involute (x : CliffordAlgebra Q) : ↑(toEven Q (reverse 
(involute x))) = reverse (Q
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `CliffordAlgebra.toEven_ι`：toEven_ι (m : M) : (toEven Q (ι Q m) : Cliffor
dAlgebra (Q' Q)) = e0 Q * v Q m
· 使用定理 `CliffordAlgebra.EquivEven.neg_e0_mul_v`：neg_e0_mul_v (m : M) : -(e0 Q * 
v Q m) = v Q m * e0 Q
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `CliffordAlgebra.EquivEven.reverse_v`：reverse_v (m : M) : reverse (Q
· 使用定理 `CliffordAlgebra.EquivEven.reverse_e0`：reverse_e0 : reverse (Q
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…

--- 原说明 ---
The representation of the clifford conjugate (i.e. the reverse of the involute) 
in the even
subalgebra is just the reverse of the representation.
-/
theorem coe_toEven_reverse_involute (x : CliffordAlgebra Q) :
    ↑(toEven Q (reverse (involute x))) =
      reverse (Q := Q' Q) (toEven Q x : CliffordAlgebra (Q' Q)) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Subalgebra.coe_algebraMap, reverse.commutes]
  | ι m =>
    simp only [involute_ι, Subalgebra.coe_neg, toEven_ι, reverse.map_mul, reverse_v, reverse_e0,
      reverse_ι, neg_e0_mul_v, map_neg]
  | mul x y hx hy => simp only [map_mul, Subalgebra.coe_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]

/-! ### Constructions needed for `CliffordAlgebra.evenEquivEvenNeg` -/

/-- One direction of `CliffordAlgebra.evenEquivEvenNeg` -/
/-
**CliffordAlgebra.evenToNeg** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) : CliffordAlgebra.even Q 
->ₐ[R] CliffordAlgebra.even Q'
参数：Q' : QuadraticForm R M；h : Q' = -Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One direction of `CliffordAlgebra.evenEquivEvenNeg`
-/
def evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) :
    CliffordAlgebra.even Q →ₐ[R] CliffordAlgebra.even Q' :=
  even.lift Q <|
    { bilin := -(even.ι Q' :).bilin
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, EvenHom.contract, h, neg_apply, map_neg, neg_neg]
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, EvenHom.contract_mid, h, neg_apply, smul_neg,
          neg_smul] }

@[simp]
/-
**CliffordAlgebra.evenToNeg_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evenToNeg_ι (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M) :
    evenToNeg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').bilin m₁ m₂ :=
  even.lift_ι _ _ m₁ m₂
/-
**CliffordAlgebra.evenToNeg_comp_evenToNeg** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAl
gebra`。
形式化陈述：evenToNeg_comp_evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = 
-Q') : (evenToNeg Q' Q h').comp (evenToNeg Q Q' h) = AlgHom.id R _
参数：Q' : QuadraticForm R M；h : Q' = -Q；h' : Q = -Q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.even.algHom_ext`：∀ {R : Type u_1} {M : Type u_2} [inst :
 CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : Quadr
aticForm R M) {A : Ty…
· 使用定理 `CliffordAlgebra.EvenHom.ext`：∀ {R : Type u_1} {M : Type u_2} {inst : Com
mRing R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   {Q : Quadratic
Form R M} {A : Ty…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CliffordAlgebra.EvenHom.compr₂_bilin`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : 
QuadraticForm R M} {A : Ty…
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
· 使用定理 `CliffordAlgebra.evenToNeg_ι`：evenToNeg_ι (Q' : QuadraticForm R M) (h : Q
' = -Q) (m₁ m₂ : M) : evenToNeg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').b
ilin m₁ m₂
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
theorem evenToNeg_comp_evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q') :
    (evenToNeg Q' Q h').comp (evenToNeg Q Q' h) = AlgHom.id R _ := by
  ext m₁ m₂ : 4
  simp [evenToNeg_ι]

/-- The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps!]
/-
**CliffordAlgebra.evenEquivEvenNeg** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：evenEquivEvenNeg : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomor
phic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic.
-/
def evenEquivEvenNeg : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q) :=
  AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_neg _).symm)
    (evenToNeg_comp_evenToNeg _ _ _ _) (evenToNeg_comp_evenToNeg _ _ _ _)

end CliffordAlgebra

